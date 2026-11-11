-- Prove2me | solution 1 for PauliUnclonable531.Pauli.top_eigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T10:18:36.051261+00:00
-- url     : https://prove2.me/submissions/d0467bfe-ec80-4c29-852c-37da589f7a55

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations
import Theorems.Thm_PauliUnclonable531_Pauli_quadratic_sum
import Theorems.Thm_PauliUnclonable531_Pauli_filter_properties

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli.Kit


open PauliUnclonable531.Pauli

/-- The tensor product `⊗ᵢ fᵢ` of single-qubit matrices, on the computational basis. -/
def tens {n : ℕ} (f : Fin n → Op (Fin 2)) : Op (Bits n) := fun x y => ∏ i, f i (x i) (y i)

lemma tens_mul {n : ℕ} (f g : Fin n → Op (Fin 2)) :
    tens f * tens g = tens (fun i => f i * g i) := by
  ext x y
  simp only [tens, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

lemma tens_one {n : ℕ} : tens (fun _ : Fin n => (1 : Op (Fin 2))) = 1 := by
  ext x y
  simp only [tens, Matrix.one_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma tens_smul {n : ℕ} (c : Fin n → ℂ) (f : Fin n → Op (Fin 2)) :
    tens (fun i => c i • f i) = (∏ i, c i) • tens f := by
  ext x y
  simp [tens, Finset.prod_mul_distrib]

lemma tens_conjTranspose {n : ℕ} (f : Fin n → Op (Fin 2)) :
    (tens f).conjTranspose = tens (fun i => (f i).conjTranspose) := by
  ext x y
  simp [tens, star_prod]

lemma tens_transpose {n : ℕ} (f : Fin n → Op (Fin 2)) :
    (tens f).transpose = tens (fun i => (f i).transpose) := by
  ext x y
  simp [tens]

lemma tens_trace {n : ℕ} (f : Fin n → Op (Fin 2)) :
    (tens f).trace = ∏ i, (f i).trace := by
  simp only [Matrix.trace, Matrix.diag, tens]
  rw [Fintype.prod_sum]

lemma pauli_eq_tens {n : ℕ} (k : Label n) :
    pauli k = tens (fun j => QMaxCutSDP.Rounding.pauli (localLabel (k.1 j) (k.2 j))) := rfl

lemma sign_add (a b : Fin 2) : sign (a + b) = sign a * sign b := by
  fin_cases a <;> fin_cases b <;> simp [sign]

lemma sign_sum {ι : Type} (s : Finset ι) (f : ι → Fin 2) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sign_add, ih]


lemma qubit_herm (a : Fin 4) :
    (QMaxCutSDP.Rounding.pauli a).conjTranspose = QMaxCutSDP.Rounding.pauli a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [QMaxCutSDP.Rounding.pauli]

lemma pauli_isHermitian {n : ℕ} (k : Label n) : (pauli k).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [pauli_eq_tens, tens_conjTranspose]
  simp only [qubit_herm]

end PauliUnclonable531.Pauli.Kit

namespace PauliUnclonable531.Pauli.Top

open PauliUnclonable531.Pauli

lemma kron_conjTranspose {X Y : Type} (x : Op X) (y : Op Y) :
    (Matrix.kronecker x y).conjTranspose = Matrix.kronecker x.conjTranspose y.conjTranspose :=
  Matrix.conjTranspose_kronecker x y

lemma avg_hermitian {n : ℕ} {X : Type} [Fintype X] (f : Key n → Op X)
    (hf : ∀ k, (f k).IsHermitian) : ((Fintype.card (Key n) : ℂ)⁻¹ • ∑ k, f k).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp only [fun k => (hf k).eq]
  congr 1
  simp

variable {n : ℕ} {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]

lemma transpose_pauli_herm (k : Label n) : ((pauli k).transpose).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, (Kit.pauli_isHermitian k).eq]

lemma EB_herm (a : Decoders n B C) : (EB a).IsHermitian := by
  apply avg_hermitian
  intro k
  unfold Matrix.IsHermitian
  rw [kron_conjTranspose, kron_conjTranspose, (transpose_pauli_herm k.val).eq,
    (a.bob_hermitian k).eq, Matrix.conjTranspose_one]

lemma EC_herm (a : Decoders n B C) : (EC a).IsHermitian := by
  apply avg_hermitian
  intro k
  unfold Matrix.IsHermitian
  rw [kron_conjTranspose, kron_conjTranspose, (transpose_pauli_herm k.val).eq,
    (a.charlie_hermitian k).eq, Matrix.conjTranspose_one]

lemma EBC_herm (a : Decoders n B C) : (EBC a).IsHermitian := by
  apply avg_hermitian
  intro k
  unfold Matrix.IsHermitian
  rw [kron_conjTranspose, kron_conjTranspose, (a.bob_hermitian k).eq,
    (a.charlie_hermitian k).eq, Matrix.conjTranspose_one]

lemma D_herm (a : Decoders n B C) : (disagreement a).IsHermitian :=
  Matrix.isHermitian_one.sub (EBC_herm a)

lemma G_herm (a : Decoders n B C) : (gameOperator a).IsHermitian := by
  unfold gameOperator
  have h := ((EB_herm a).add (EC_herm a)).sub (D_herm a)
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, h.eq]
  congr 1
  simp

lemma dot_sandwich {X : Type} [Fintype X] (M F : Op X) (hM : M.IsHermitian) (v : X → ℂ) :
    star (M *ᵥ v) ⬝ᵥ (F *ᵥ (M *ᵥ v)) = star v ⬝ᵥ ((M * F * M) *ᵥ v) := by
  rw [Matrix.star_mulVec, hM.eq, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

lemma dot_conjTranspose {X : Type} [Fintype X] (M : Op X) (v : X → ℂ) :
    star v ⬝ᵥ (M.conjTranspose *ᵥ v) = star (star v ⬝ᵥ (M *ᵥ v)) := by
  rw [Matrix.mulVec_conjTranspose, Matrix.dotProduct_star, star_star, ← Matrix.dotProduct_mulVec]

lemma quad_norm_le {X : Type} [Fintype X] [DecidableEq X] (M : Op X) (v : EuclideanSpace ℂ X)
    (hv : ‖v‖ = 1) : ‖star (⇑v) ⬝ᵥ (M *ᵥ ⇑v)‖ ≤ ‖M‖ := by
  have hinner : star (⇑v) ⬝ᵥ (M *ᵥ ⇑v) = inner ℂ v (Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) M v) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  rw [hinner]
  calc ‖inner ℂ v (Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) M v)‖
      ≤ ‖v‖ * ‖Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) M v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖M‖ * ‖v‖) := by
        gcongr
        simpa [Matrix.l2_opNorm_toEuclideanCLM] using
          (Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) M).le_opNorm v
    _ = ‖M‖ := by rw [hv]; ring

end PauliUnclonable531.Pauli.Top

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.Top in
theorem solution {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Decoders n B C)
    (ht : 0 < largestEigenvalue (gameOperator a)) :
    (largestEigenvalue (gameOperator a))^2 ≤
      spectralNorm (EB a * filterOperator a (largestEigenvalue (gameOperator a)) * EC a) := by
  classical
  have hG := G_herm a
  set t := largestEigenvalue (gameOperator a) with ht_def
  -- a unit eigenvector for the top eigenvalue
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Bits n × (B × C)))
    hG.eigenvalues
  have htval : t = hG.eigenvalues i0 := by
    rw [ht_def, largestEigenvalue, dif_pos hG, hi0]
  set e := hG.eigenvectorBasis i0
  set ψ : Bits n × (B × C) → ℂ := ⇑e
  have heig : gameOperator a *ᵥ ψ = (t : ℂ) • ψ := by
    rw [htval]; exact hG.mulVec_eigenvectorBasis i0
  have hunit : ‖e‖ = 1 := hG.eigenvectorBasis.orthonormal.norm_eq_one i0
  have hdot : star ψ ⬝ᵥ ψ = 1 := by
    have h1 : inner ℂ e e = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, hunit]; norm_num
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h1
    exact h1
  -- filter facts
  obtain ⟨hApd, hFpd, -, hAF, hFA⟩ := filter_properties n hn a t ht
  have hq := quadratic_sum n hn a t ht
  set A := (2 * (t : ℂ)) • (1 : Op (Bits n × (B × C))) + disagreement a with hA
  -- the eigen-relation `(EB + EC) ψ = A ψ`
  have hrel : (EB a + EC a) *ᵥ ψ = A *ᵥ ψ := by
    have h2 : (EB a + EC a) = (2 : ℂ) • gameOperator a + disagreement a := by
      unfold gameOperator
      rw [smul_smul]; norm_num
    rw [h2, hA, Matrix.add_mulVec, Matrix.smul_mulVec, heig, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul]
  -- exact value of the quadratic form of `(EB+EC) F (EB+EC)`
  have hX := (EB_herm a).add (EC_herm a)
  have hexact : star ψ ⬝ᵥ (((EB a + EC a) * filterOperator a t * (EB a + EC a)) *ᵥ ψ) =
      (2 * (t : ℂ)) * (star ψ ⬝ᵥ (A *ᵥ ψ)) := by
    rw [← dot_sandwich _ _ hX, hrel, Matrix.mulVec_mulVec, hFA, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    congr 1
    rw [Matrix.star_mulVec, hApd.isHermitian.eq, Matrix.dotProduct_mulVec]
  have hAval : star ψ ⬝ᵥ (A *ᵥ ψ) = 2 * (t : ℂ) + star ψ ⬝ᵥ (disagreement a *ᵥ ψ) := by
    rw [hA, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
      dotProduct_smul, hdot, smul_eq_mul, mul_one]
  -- Corollary 4.12 evaluated on ψ
  unfold Below at hq
  have hpos := hq.re_dotProduct_nonneg ψ
  have hFH : (filterOperator a t).IsHermitian := hFpd.isHermitian
  have hadj : EC a * filterOperator a t * EB a = (EB a * filterOperator a t * EC a).conjTranspose := by
    simp only [Matrix.conjTranspose_mul, (EB_herm a).eq, (EC_herm a).eq, hFH.eq, Matrix.mul_assoc]
  rw [hadj] at hpos
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_add, dotProduct_smul, smul_eq_mul] at hpos
  rw [hexact, hAval, dot_conjTranspose] at hpos
  set z := star ψ ⬝ᵥ ((EB a * filterOperator a t * EC a) *ᵥ ψ) with hz
  set w := star ψ ⬝ᵥ (disagreement a *ᵥ ψ)
  rw [RCLike.re_to_complex] at hpos
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.mul_im,
    Complex.add_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add] at hpos
  have hre : t ^ 2 ≤ z.re := by nlinarith
  calc t ^ 2 ≤ z.re := hre
    _ ≤ ‖z‖ := Complex.re_le_norm _
    _ ≤ ‖EB a * filterOperator a t * EC a‖ := quad_norm_le _ e hunit
