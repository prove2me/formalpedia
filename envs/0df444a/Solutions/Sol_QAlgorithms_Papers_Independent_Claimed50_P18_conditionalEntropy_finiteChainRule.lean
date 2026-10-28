-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P18.conditionalEntropy_finiteChainRule
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:02:00.242071+00:00
-- url     : https://prove2.me/submissions/58102597-5c18-440d-8d9f-fb71cc627271

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_extendedRelativeEntropy_monotone_of_finite_ssa
import Theorems.Thm_SimpleSSA_Monotone_eq_4

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

set_option linter.unusedSectionVars false

section S193C_gen
open Matrix Polynomial

variable {X K : Type*} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]

def S193C_conj (W : Matrix X K ℂ) (h1 : Wᴴ * W = 1) (h2 : W * Wᴴ = 1) :
    Matrix K K ℂ →ₐ[ℝ] Matrix X X ℂ where
  toFun M := W * M * Wᴴ
  map_one' := by rw [Matrix.mul_one, h2]
  map_mul' M N := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wᴴ W, h1, Matrix.one_mul]
  map_zero' := by simp
  map_add' M N := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, h2]

lemma S193C_herm (W : Matrix X K ℂ) (d : K → ℝ) :
    (W * diagonal (fun k => (d k : ℂ)) * Wᴴ).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_assoc]
  congr 3
  funext k
  simp

lemma S193C_cfc (W : Matrix X K ℂ) (h1 : Wᴴ * W = 1) (h2 : W * Wᴴ = 1) (d : K → ℝ)
    (f : ℝ → ℝ) :
    cfc f (W * diagonal (fun k => (d k : ℂ)) * Wᴴ) =
      W * diagonal (fun k => (f (d k) : ℂ)) * Wᴴ := by
  have hσ := S193C_herm W d
  set σ := W * diagonal (fun k => (d k : ℂ)) * Wᴴ with hσdef
  set s : Finset ℝ := Finset.univ.image d ∪ Finset.univ.image hσ.eigenvalues with hs
  set p : ℝ[X] := Lagrange.interpolate s id f with hpdef
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) _ (Set.injOn_id _) hx
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x ?_).symm),
    cfc_polynomial p σ hσ.isSelfAdjoint]
  · have : σ = S193C_conj W h1 h2 (diagonalAlgHom ℝ (fun k => (d k : ℂ))) := rfl
    rw [this, Polynomial.aeval_algHom_apply, Polynomial.aeval_algHom_apply]
    change W * (diagonalAlgHom ℝ ((aeval fun k => (d k : ℂ)) p)) * Wᴴ = _
    congr 2
    change diagonal _ = _
    congr 1
    funext k
    rw [Polynomial.aeval_pi_apply₂]
    rw [show ((d k : ℂ)) = algebraMap ℝ ℂ (d k) from rfl,
      Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hp _ (by simp [hs])]
    rfl
  · rw [hσ.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    simp [hs]

lemma S193C_tr (ρ : Matrix X X ℂ) (W : Matrix X K ℂ) (e : K → ℂ) :
    (ρ * (W * diagonal e * Wᴴ)).trace = ∑ k, (Wᴴ * ρ * W) k k * e k := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, mul_diagonal]

lemma S193C_ker (ρ : Matrix X X ℂ) (hρ : ρ.PosSemidef) (W : Matrix X K ℂ) (h1 : Wᴴ * W = 1)
    (h2 : W * Wᴴ = 1) (d : K → ℝ) (H0 : ∀ k, d k = 0 → (Wᴴ * ρ * W) k k = 0) :
    LinearMap.ker (W * diagonal (fun k => (d k : ℂ)) * Wᴴ).mulVecLin ≤
      LinearMap.ker ρ.mulVecLin := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  set c := Wᴴ *ᵥ v with hc
  have hdc : ∀ k, (d k : ℂ) * c k = 0 := by
    intro k
    have := congrArg (fun u => Wᴴ *ᵥ u) hv
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, ← Matrix.mulVec_mulVec,
      ← hc] at this
    have := congrFun this k
    simpa [Matrix.mulVec_diagonal] using this
  have hv' : v = W *ᵥ c := by
    rw [hc, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  have hcol : ∀ k, d k = 0 → ρ *ᵥ (fun x => W x k) = 0 := by
    intro k hk
    rw [← hρ.dotProduct_mulVec_zero_iff]
    rw [← H0 k hk]
    simp only [Matrix.mul_apply, conjTranspose_apply, dotProduct, Matrix.mulVec, Pi.star_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [hv', Matrix.mulVec_mulVec]
  funext x
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : d k = 0
  · have := congrFun (hcol k hk) x
    simp only [Matrix.mulVec, dotProduct] at this
    rw [Matrix.mul_apply, this]; simp
  · have : c k = 0 := by
      have := hdc k
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (by exact_mod_cast h) hk
      · exact h
    rw [this, mul_zero]


lemma S193C_klein {I : Type*} [Fintype I] (p : I → ℝ) (d : K → ℝ) (M : I → K → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hd : ∀ k, 0 ≤ d k) (hM : ∀ i k, 0 ≤ M i k)
    (hrow : ∀ i, ∑ k, M i k = 1) (hcol : ∀ k, ∑ i, M i k = 1)
    (H : ∀ k, d k = 0 → ∑ i, M i k * p i = 0) :
    ∑ k, (∑ i, M i k * p i) * Real.log (d k) ≤
      ∑ i, p i * Real.log (p i) + ∑ k, d k - ∑ i, p i := by
  have hpt : ∀ i k, M i k * (p i - d k) ≤
      M i k * (p i * Real.log (p i)) - M i k * p i * Real.log (d k) := by
    intro i k
    rcases (hp i).lt_or_eq with hpi | hpi
    · rcases (hd k).lt_or_eq with hdk | hdk
      · have hl := Real.log_le_sub_one_of_pos (div_pos hdk hpi)
        rw [Real.log_div hdk.ne' hpi.ne'] at hl
        have : p i - d k ≤ p i * Real.log (p i) - p i * Real.log (d k) := by
          have h3 : p i * (Real.log (d k) - Real.log (p i)) ≤ p i * (d k / p i - 1) :=
            mul_le_mul_of_nonneg_left hl hpi.le
          rw [mul_sub, mul_sub, mul_div_cancel₀ _ hpi.ne', mul_one] at h3
          linarith
        have := mul_le_mul_of_nonneg_left this (hM i k)
        linarith
      · have h0 := H k hdk.symm
        have hz : M i k * p i = 0 := by
          have hnn : ∀ i' ∈ Finset.univ, 0 ≤ M i' k * p i' := fun i' _ =>
            mul_nonneg (hM i' k) (hp i')
          exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 i (Finset.mem_univ _)
        have hMz : M i k = 0 := by
          rcases mul_eq_zero.1 hz with h | h
          · exact h
          · exact absurd h hpi.ne'
        simp [hMz]
    · rw [← hpi]
      simp only [zero_sub, zero_mul, Real.log_zero, mul_zero, sub_zero, mul_neg]
      exact neg_nonpos.2 (mul_nonneg (hM i k) (hd k))
  have hR : ∑ i, p i * Real.log (p i) = ∑ i, ∑ k, M i k * (p i * Real.log (p i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hrow i, one_mul]
  have hL : ∑ k, (∑ i, M i k * p i) * Real.log (d k) =
      ∑ i, ∑ k, M i k * p i * Real.log (d k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
  have h0 : ∑ i, ∑ k, M i k * (p i - d k) = ∑ i, p i - ∑ k, d k := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i k => M i k * d k)]
    simp only [← Finset.sum_mul, hrow, hcol, one_mul]
  rw [hR, hL]
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hpt i k
  simp only [Finset.sum_sub_distrib] at this
  linarith

lemma S193C_trf (W : Matrix X K ℂ) (h1 : Wᴴ * W = 1) (h2 : W * Wᴴ = 1) (d : K → ℝ)
    (f : ℝ → ℝ) :
    (cfc f (W * diagonal (fun k => (d k : ℂ)) * Wᴴ)).trace.re = ∑ k, f (d k) := by
  rw [S193C_cfc W h1 h2, Matrix.trace_mul_cycle, h1, Matrix.one_mul, Matrix.trace_diagonal,
    Complex.re_sum]
  simp

lemma S193C_spec (A : Matrix X X ℂ) (hA : A.IsHermitian) :
    ∃ U : Matrix X X ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix X X ℂ),
    Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2,
    Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2, ?_⟩
  conv_lhs => rw [hA.spectral_theorem]
  rfl

lemma S193C_normSq (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]; rfl

/-- diagonal entries of a conjugated diagonal matrix -/
lemma S193C_diag_re {Y : Type*} [Fintype Y] [DecidableEq Y] (B : Matrix Y K ℂ) (p : Y → ℝ) (k : K) :
    ((Bᴴ * diagonal (fun i => (p i : ℂ)) * B) k k).re = ∑ i, Complex.normSq (B i k) * p i := by
  rw [Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_diagonal, conjTranspose_apply,
    show star (B i k) * (p i : ℂ) * B i k = (star (B i k) * B i k) * (p i : ℂ) by ring,
    S193C_normSq, ← Complex.ofReal_mul, Complex.ofReal_re]

lemma S193C_rows {Y : Type*} [Fintype Y] [DecidableEq Y] (B : Matrix Y K ℂ) (h : B * Bᴴ = 1)
    (i : Y) : ∑ k, Complex.normSq (B i k) = 1 := by
  have := congrArg Complex.re (congrFun (congrFun h i) i)
  rw [Matrix.mul_apply, Complex.re_sum] at this
  simp only [Matrix.one_apply_eq, Complex.one_re] at this
  rw [← this]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [conjTranspose_apply, mul_comm (B i k), S193C_normSq, Complex.ofReal_re]

lemma S193C_cols {Y : Type*} [Fintype Y] (B : Matrix Y K ℂ) (h : Bᴴ * B = 1)
    (k : K) : ∑ i, Complex.normSq (B i k) = 1 := by
  have := congrArg Complex.re (congrFun (congrFun h k) k)
  rw [Matrix.mul_apply, Complex.re_sum] at this
  simp only [Matrix.one_apply_eq, Complex.one_re] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_apply, S193C_normSq, Complex.ofReal_re]

/-- Klein's inequality, unitary-basis form, generalized (no trace normalization). -/
lemma S193C_KL (ρ : Matrix X X ℂ) (hρ : ρ.PosSemidef) (W : Matrix X K ℂ)
    (h1 : Wᴴ * W = 1) (h2 : W * Wᴴ = 1) (d : K → ℝ) (hd : ∀ k, 0 ≤ d k)
    (H0 : ∀ k, d k = 0 → ((Wᴴ * ρ * W) k k).re = 0) :
    ∑ k, ((Wᴴ * ρ * W) k k).re * Real.log (d k) ≤
      (cfc (fun x : ℝ => x * Real.log x) ρ).trace.re + ∑ k, d k - ρ.trace.re := by
  have hH := hρ.isHermitian
  obtain ⟨U, hU1, hU2, hρU⟩ := S193C_spec ρ hH
  set p := hH.eigenvalues
  set B := Uᴴ * W with hB
  have hr : ∀ k, ((Wᴴ * ρ * W) k k).re = ∑ i, Complex.normSq (B i k) * p i := by
    intro k
    have : Wᴴ * ρ * W = Bᴴ * diagonal (fun i => (p i : ℂ)) * B := by
      rw [hρU, hB, conjTranspose_mul, conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
    rw [this, S193C_diag_re B p k]
  have hBB1 : B * Bᴴ = 1 := by
    rw [hB, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc W, h2, Matrix.one_mul, hU1]
  have hBB2 : Bᴴ * B = 1 := by
    rw [hB, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc U, hU2, Matrix.one_mul, h1]
  have hplog : (cfc (fun x : ℝ => x * Real.log x) ρ).trace.re = ∑ i, p i * Real.log (p i) := by
    rw [hρU, S193C_trf U hU1 hU2]
  have htr : ρ.trace.re = ∑ i, p i := by
    have := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    simpa using this
  have hK := S193C_klein p d (fun i k => Complex.normSq (B i k)) hρ.eigenvalues_nonneg hd
    (fun i k => Complex.normSq_nonneg _) (S193C_rows B hBB1) (S193C_cols B hBB2)
    (fun k hk => by rw [← hr, H0 k hk])
  simp only [hr]
  rw [hplog, htr]
  exact hK

end S193C_gen

section S193C_dens
open Matrix
open scoped Kronecker
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier18.P01

lemma S193C_tc {I : Type} [Fintype I] (X : Matrix I I ℂ) : IsTraceClass X := by
  classical
  let e := Fintype.equivFin (I × I)
  let N := Fintype.card (I × I)
  let L : ℕ → QAlgorithms.RealRegisters.Hilbert I := fun n =>
    if h : n < N then lp.single 2 (e.symm ⟨n, h⟩).1 (X (e.symm ⟨n, h⟩).1 (e.symm ⟨n, h⟩).2)
    else 0
  let R : ℕ → QAlgorithms.RealRegisters.Hilbert I := fun n =>
    if h : n < N then lp.single 2 (e.symm ⟨n, h⟩).2 1 else 0
  have hz : ∀ n, ¬ n < N → L n = 0 ∧ R n = 0 := fun n hn => by simp [L, R, hn]
  refine ⟨{ left := L, right := R, summable := ?_, coefficients := ?_ }⟩
  · apply summable_of_ne_finset_zero (s := Finset.range N)
    intro n hn
    rw [Finset.mem_range] at hn
    simp [(hz n hn).1]
  · intro i j
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => by
      rw [Finset.mem_range] at hn; simp [(hz n hn).1])]
    rw [Finset.sum_range (fun n => L n i * star (R n j))]
    have : ∀ k : Fin N, L k i * star (R k j) =
        (fun ab : I × I => Pi.single (M := fun _ : I => ℂ) ab.1 (X ab.1 ab.2) i * star (Pi.single (M := fun _ : I => ℂ) ab.2 (1 : ℂ) j))
          (e.symm k) := by
      intro k
      simp [L, R, k.2]
    simp_rw [this]
    rw [Equiv.sum_comp e.symm (fun ab : I × I =>
      Pi.single (M := fun _ : I => ℂ) ab.1 (X ab.1 ab.2) i * star (Pi.single (M := fun _ : I => ℂ) ab.2 (1 : ℂ) j)), Fintype.sum_prod_type]
    simp [Pi.single_apply]

lemma S193C_herm_of {I : Type} (X : Matrix I I ℂ)
    (h : ∀ (s : Finset I) (z : I → ℂ),
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).im = 0) : X.IsHermitian := by
  classical
  have hd : ∀ i, (X i i).im = 0 := by
    intro i
    have := h {i} (fun _ => 1)
    simpa using this
  ext i j
  rw [conjTranspose_apply]
  by_cases hij : i = j
  · subst hij
    apply Complex.ext
    · simp
    · simp [hd i]
  have h1 := h {i, j} (fun k => if k = i then 1 else 1)
  have h2 := h {i, j} (fun k => if k = i then 1 else Complex.I)
  rw [Finset.sum_pair hij] at h1 h2
  simp only [Finset.sum_pair hij, if_pos, if_neg (Ne.symm hij)] at h1 h2
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, hd i, hd j] at h1 h2
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]
    linarith
  · simp only [Complex.star_def, Complex.conj_im]
    linarith

lemma S193C_psd_of_density {I : Type} [Fintype I] {X : Matrix I I ℂ} (hX : IsDensity X) :
    X.PosSemidef ∧ X.trace = 1 := by
  classical
  obtain ⟨_, hq, _, ht⟩ := hX
  have hH : X.IsHermitian := S193C_herm_of X (fun s z => (hq s z).1)
  refine ⟨Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_, ?_⟩
  · have hx : star x ⬝ᵥ (X *ᵥ x) = ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
        star (x i) * X i j * x j := by
      simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
    rw [hx, Complex.nonneg_iff]
    exact ⟨(hq _ x).2, (hq _ x).1.symm⟩
  · rw [tsum_fintype] at ht
    have him : ∀ i, (X i i).im = 0 := fun i => by
      have := congrArg Complex.im (congrFun (congrFun hH i) i)
      simp only [conjTranspose_apply, Complex.star_def, Complex.conj_im] at this
      linarith
    apply Complex.ext
    · simp [Matrix.trace, ht]
    · simp [Matrix.trace, Complex.im_sum, him]

lemma S193C_density_of_psd {I : Type} [Fintype I] {X : Matrix I I ℂ} (hX : X.PosSemidef)
    (ht : X.trace = 1) : IsDensity X := by
  classical
  refine ⟨S193C_tc X, fun s z => ?_, (summable_of_ne_finset_zero (s := Finset.univ)
    (by simp)), ?_⟩
  · let z' : I → ℂ := fun i => if i ∈ s then z i else 0
    have := hX.dotProduct_mulVec_nonneg z'
    have hx : star z' ⬝ᵥ (X *ᵥ z') = ∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j := by
      simp only [dotProduct, mulVec, Pi.star_apply, z', Finset.mul_sum]
      rw [← Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by simp [hi])]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← Finset.sum_subset (Finset.subset_univ s) (fun j _ hj => by simp [hj])]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp [hi, hj, mul_assoc]
    rw [hx, Complex.nonneg_iff] at this
    exact ⟨this.2.symm, this.1⟩
  · rw [tsum_fintype]
    have := congrArg Complex.re ht
    simpa [Matrix.trace, Complex.re_sum] using this

/-- conjugation by a unitary is a channel -/
def S193C_uch {I : Type} [Fintype I] [DecidableEq I] (W : Matrix I I ℂ) (h1 : Wᴴ * W = 1)
    (h2 : W * Wᴴ = 1) : Channel I I :=
  ⟨fun Y => W * Y * Wᴴ, by
    refine ⟨fun _ _ => S193C_tc _, fun A B _ _ => by simp [Matrix.mul_add, Matrix.add_mul],
      fun c A _ => by simp, fun n ρ => ?_⟩
    obtain ⟨hp, ht⟩ := S193C_psd_of_density ρ.density
    have heq : tensorApply (fun Y => W * Y * Wᴴ) ρ.coefficients =
        (W ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * ρ.coefficients *
          (W ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ := by
      ext p q
      show (W * (Matrix.of fun i j => ρ.coefficients (i, p.2) (j, q.2)) * Wᴴ) p.1 q.1 = _
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.kroneckerMap_apply, conjTranspose_apply,
        Fintype.sum_prod_type, Matrix.one_apply, Matrix.conjTranspose_kronecker]
      simp [Finset.sum_mul, mul_ite, ite_mul]
    rw [heq]
    refine S193C_density_of_psd ?_ ?_
    · simpa using hp.conjTranspose_mul_mul_same (W ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ
    · rw [Matrix.trace_mul_cycle, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
        h1, conjTranspose_one, Matrix.one_mul, Matrix.one_kronecker_one, Matrix.one_mul, ht]⟩

end S193C_dens

section S193C_dpi
open Matrix
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier18.P01

lemma S193C_xlog {F : Type} [Fintype F] [DecidableEq F] (A : Matrix F F ℂ) :
    cfc (fun x : ℝ => x * Real.log x) A = A * cfc Real.log A := by
  by_cases hA : IsSelfAdjoint A
  · have hfin : (spectrum ℝ A).Finite := by
      have hH : A.IsHermitian := hA
      rw [hH.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
    rw [cfc_mul (fun x : ℝ => x) Real.log A (hfin.continuousOn _) (hfin.continuousOn _),
      cfc_id' ℝ A]
  · rw [cfc_apply_of_not_predicate A hA, cfc_apply_of_not_predicate A hA, Matrix.mul_zero]

lemma S193C_fre_bridge {F : Type} [Fintype F] (i1 i2 : DecidableEq F) (A B : Matrix F F ℂ) :
    @QAlgorithms.Papers.Independent.Frontier18.P07.finiteRelativeEntropy F _ i1 A B =
      @finiteRelativeEntropy F _ i2 A B := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  unfold QAlgorithms.Papers.Independent.Frontier18.P07.finiteRelativeEntropy finiteRelativeEntropy
  rw [S193C_xlog]

theorem S193C_dpi {I : Type} [Fintype I] [Nonempty I] (Phi : Channel I I)
    (X Y : Matrix I I ℂ) (hX : IsDensity X) (hY : IsDensity Y) :
    generalizedRelativeEntropy (Phi.val X) (Phi.val Y) ≤ generalizedRelativeEntropy X Y := by
  have := QAlgorithms.Papers.Independent.Gap48.P45.extendedRelativeEntropy_monotone_of_finite_ssa
    (fun ρ σ h1 h2 h3 h4 => SimpleSSA.Monotone.eq_4 ρ σ h1 h2 h3 h4) Phi X Y hX hY
  have e : ∀ A B : Matrix I I ℂ, generalizedRelativeEntropy A B =
      QAlgorithms.Papers.Independent.Frontier18.P07.extendedRelativeEntropyNats A B := by
    intro A B
    unfold QAlgorithms.Papers.Independent.Frontier18.P07.extendedRelativeEntropyNats
      generalizedRelativeEntropy
    refine iSup_congr fun s => ?_
    exact (S193C_fre_bridge _ _ _ _).symm
  rw [e, e]
  exact this

end S193C_dpi

section S193C_ent
open Matrix Polynomial

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

lemma S193C_unit_sub (U : Matrix I I ℂ) (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1) (e : K ≃ I) :
    (U.submatrix e id)ᴴ * U.submatrix e id = 1 ∧ U.submatrix e id * (U.submatrix e id)ᴴ = 1 := by
  rw [conjTranspose_submatrix]
  constructor
  · rw [show (Uᴴ.submatrix id e) = Uᴴ.submatrix id (e : K → I) from rfl, submatrix_mul_equiv,
      h1, submatrix_id_id]
  · rw [show (U.submatrix e id) = U.submatrix (e : K → I) (Equiv.refl I) from rfl,
      show (Uᴴ.submatrix id e) = Uᴴ.submatrix (Equiv.refl I) (e : K → I) from rfl,
      submatrix_mul_equiv, h2, submatrix_one_equiv]

lemma S193C_cfc_sub (A : Matrix I I ℂ) (hA : A.IsHermitian) (e : K ≃ I) (f : ℝ → ℝ) :
    cfc f (A.submatrix e e) = (cfc f A).submatrix e e := by
  obtain ⟨U, h1, h2, hAU⟩ := S193C_spec A hA
  obtain ⟨k1, k2⟩ := S193C_unit_sub U h1 h2 e
  have hs : ∀ g : I → ℝ, (U * diagonal (fun i => (g i : ℂ)) * Uᴴ).submatrix e e =
      U.submatrix e id * diagonal (fun i => (g i : ℂ)) * (U.submatrix e id)ᴴ := by
    intro g
    rw [conjTranspose_submatrix, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      Matrix.submatrix_mul _ _ _ id _ Function.bijective_id]
    simp
  rw [hAU, hs, S193C_cfc _ k1 k2, S193C_cfc _ h1 h2, hs]

lemma S193C_trace_sub (A : Matrix I I ℂ) (e : K ≃ I) : (A.submatrix e e).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, submatrix_apply]
  exact e.sum_comp (fun i => A i i)

/-- trace of x log x, push-through identity -/
lemma S193C_pow {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Matrix m n ℂ) (k : ℕ) : (B * Bᴴ) ^ (k + 1) = B * (Bᴴ * B) ^ k * Bᴴ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

lemma S193C_trpow {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Matrix m n ℂ) (k : ℕ) (hk : k ≠ 0) : ((B * Bᴴ) ^ k).trace = ((Bᴴ * B) ^ k).trace := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [S193C_pow, Matrix.trace_mul_cycle, ← pow_succ']

lemma S193C_E1 {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Matrix m n ℂ) :
    (cfc (fun x : ℝ => x * Real.log x) (B * Bᴴ)).trace =
      (cfc (fun x : ℝ => x * Real.log x) (Bᴴ * B)).trace := by
  have hA : (B * Bᴴ).IsHermitian := isHermitian_mul_conjTranspose_self B
  have hC : (Bᴴ * B).IsHermitian := isHermitian_conjTranspose_mul_self B
  have fA : (spectrum ℝ (B * Bᴴ)).Finite := by
    rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
  have fC : (spectrum ℝ (Bᴴ * B)).Finite := by
    rw [hC.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
  set S : Finset ℝ := fA.toFinset ∪ fC.toFinset ∪ {0}
  set p : ℝ[X] := Lagrange.interpolate S id (fun x : ℝ => x * Real.log x)
  have hp : ∀ x ∈ S, p.eval x = x * Real.log x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) _ (Set.injOn_id _) hx
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hp 0 (by simp [S])]; simp
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x (by simp [S, hx])).symm),
    cfc_polynomial p _ hA.isSelfAdjoint,
    cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x (by simp [S, hx])).symm),
    cfc_polynomial p _ hC.isSelfAdjoint, aeval_eq_sum_range, aeval_eq_sum_range,
    Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.trace_smul, Matrix.trace_smul]
  by_cases hk : k = 0
  · subst hk; rw [h0]; simp
  · rw [S193C_trpow B k hk]

/-- homogeneous entropy (real form) -/
def S193C_H {F : Type*} [Fintype F] [DecidableEq F] (M : Matrix F F ℂ) : ℝ :=
  -(cfc (fun x : ℝ => x * Real.log x) M).trace.re + M.trace.re * Real.log M.trace.re

lemma S193C_H_sub (A : Matrix I I ℂ) (hA : A.IsHermitian) (e : K ≃ I) :
    S193C_H (A.submatrix e e) = S193C_H A := by
  unfold S193C_H
  rw [S193C_cfc_sub A hA e, S193C_trace_sub, S193C_trace_sub]

lemma S193C_xlogx_le {x T : ℝ} (hx : 0 ≤ x) (hxT : x ≤ T) :
    x * Real.log x ≤ x * Real.log T := by
  rcases hx.lt_or_eq with h | h
  · exact mul_le_mul_of_nonneg_left (Real.log_le_log h hxT) hx
  · rw [← h]; simp

/-- compression monotonicity of homogeneous entropy -/
theorem S193C_Hmono (M : Matrix I I ℂ) (hM : M.PosSemidef) (s : Finset I) :
    S193C_H (M.submatrix (fun i : s => i.val) (fun i : s => i.val)) ≤ S193C_H M := by
  have hH := hM.isHermitian
  obtain ⟨U, h1, h2, hMU⟩ := S193C_spec M hH
  set lam := hH.eigenvalues with hlam
  have hlam0 : ∀ k, 0 ≤ lam k := hM.eigenvalues_nonneg
  set B : Matrix I I ℂ := U * diagonal (fun k => ((Real.sqrt (lam k) : ℝ) : ℂ)) with hB
  have hBB : M = B * Bᴴ := by
    rw [hMU, hB, conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    congr 3
    funext k
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hlam0 k)]
  set Bs : Matrix s I ℂ := B.submatrix (fun i : s => i.val) id
  have hMs : M.submatrix (fun i : s => i.val) (fun i : s => i.val) = Bs * Bsᴴ := by
    rw [hBB, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, conjTranspose_submatrix]
  set Xm := Bsᴴ * Bs
  have hXm : Xm.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Bs
  have hT : M.trace.re = ∑ k, lam k := by
    have := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    simpa using this
  have hHM : S193C_H M = -∑ k, lam k * Real.log (lam k) + (∑ k, lam k) * Real.log (∑ k, lam k) := by
    unfold S193C_H
    rw [hT]
    conv_lhs => rw [hMU]
    rw [S193C_trf U h1 h2]
  have hHs : S193C_H (M.submatrix (fun i : s => i.val) (fun i : s => i.val)) = S193C_H Xm := by
    unfold S193C_H
    rw [hMs, S193C_E1, Matrix.trace_mul_comm]
  rw [hHs, hHM]
  set T := ∑ k, lam k
  -- diagonal of Xm
  have hBik : ∀ i k, B i k = U i k * ((Real.sqrt (lam k) : ℝ) : ℂ) := fun i k => by
    simp [hB, Matrix.mul_diagonal]
  have hXkk : ∀ k, (Xm k k).re = lam k * ∑ i : s, Complex.normSq (U i k) := by
    intro k
    show (∑ i : s, (Bsᴴ) k i * Bs i k).re = _
    simp only [Bs, conjTranspose_apply, submatrix_apply, id, hBik, Complex.re_sum,
      S193C_normSq, Complex.ofReal_re, Complex.normSq_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt (hlam0 k), Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcol := S193C_cols U h1
  have hXk0 : ∀ k, 0 ≤ (Xm k k).re := fun k => by
    rw [hXkk]; exact mul_nonneg (hlam0 k) (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)
  have hXkl : ∀ k, (Xm k k).re ≤ lam k := fun k => by
    rw [hXkk]
    calc lam k * ∑ i : s, Complex.normSq (U i k) ≤ lam k * ∑ i, Complex.normSq (U i k) := by
          apply mul_le_mul_of_nonneg_left _ (hlam0 k)
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (s := Finset.univ.map (Function.Embedding.subtype (· ∈ s))) (by simp)
            (fun i _ _ => Complex.normSq_nonneg _) |>.trans_eq' (by
              rw [Finset.sum_map]; rfl)
      _ = lam k := by rw [hcol, mul_one]
  have hlamT : ∀ k, lam k ≤ T := fun k =>
    Finset.single_le_sum (fun j _ => hlam0 j) (Finset.mem_univ k)
  have htX : Xm.trace.re = ∑ k, (Xm k k).re := by simp [Matrix.trace, Complex.re_sum]
  -- RHS ≥ ...
  have key : ∑ k, (lam k - (Xm k k).re) * Real.log (lam k) ≤
      ∑ k, (lam k - (Xm k k).re) * Real.log T := by
    refine Finset.sum_le_sum fun k _ => ?_
    rcases (hlam0 k).lt_or_eq with h | h
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log h (hlamT k)) (by linarith [hXkl k])
    · have : (Xm k k).re = 0 := le_antisymm (h ▸ hXkl k) (hXk0 k)
      rw [← h, this]; simp
  unfold S193C_H
  rw [htX]
  set tX := ∑ k, (Xm k k).re
  have htXT : tX ≤ T := Finset.sum_le_sum fun k _ => hXkl k
  rcases (Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => hXk0 k).lt_or_eq with htp | htz
  · -- Klein with d = c λ
    have hTp : 0 < T := lt_of_lt_of_le htp htXT
    set c := tX / T
    have hc : 0 < c := div_pos htp hTp
    have hK := S193C_KL Xm hXm (1 : Matrix I I ℂ) (by simp) (by simp) (fun k => c * lam k)
      (fun k => mul_nonneg hc.le (hlam0 k)) (fun k hk => by
        simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
        have : lam k = 0 := by
          rcases mul_eq_zero.1 hk with h | h
          · exact absurd h hc.ne'
          · exact h
        exact le_antisymm (this ▸ hXkl k) (hXk0 k))
    simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at hK
    rw [← Finset.mul_sum, htX] at hK
    have hcT : c * T = tX := div_mul_cancel₀ _ hTp.ne'
    have hsplit : ∑ k, (Xm k k).re * Real.log (c * lam k) =
        tX * Real.log c + ∑ k, (Xm k k).re * Real.log (lam k) := by
      rw [Finset.sum_mul]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rcases (hXk0 k).lt_or_eq with hx | hx
      · have hl : 0 < lam k := lt_of_lt_of_le hx (hXkl k)
        rw [Real.log_mul hc.ne' hl.ne']; ring
      · rw [← hx]; simp
    have hlogc : Real.log c = Real.log tX - Real.log T := Real.log_div htp.ne' hTp.ne'
    rw [hsplit, hcT, hlogc] at hK
    have e1 : ∑ k, (lam k - (Xm k k).re) * Real.log (lam k) =
        ∑ k, lam k * Real.log (lam k) - ∑ k, (Xm k k).re * Real.log (lam k) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∑ k, (lam k - (Xm k k).re) * Real.log T = T * Real.log T - tX * Real.log T := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib]; ring
    rw [e1, e2] at key
    nlinarith
  · -- Xm has zero trace, hence is zero
    have htz0 : tX = 0 := htz.symm
    have hz : ∀ k, (Xm k k).re = 0 := fun k =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hXk0 k)).1 htz.symm k (Finset.mem_univ k)
    have hφ : (cfc (fun x : ℝ => x * Real.log x) Xm).trace.re = 0 := by
      have hK := S193C_KL Xm hXm (1 : Matrix I I ℂ) (by simp) (by simp) (fun _ => 0)
        (fun _ => le_rfl) (fun k _ => by simp [hz k])
      simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Real.log_zero, mul_zero,
        Finset.sum_const_zero, htX] at hK
      -- upper bound: x log x ≤ 0 on eigenvalues in [0, tr] with tr = 0
      have hXH := hXm.isHermitian
      obtain ⟨V, v1, v2, hXV⟩ := S193C_spec Xm hXH
      have hev : ∀ i, hXH.eigenvalues i = 0 := by
        have hs := congrArg Complex.re hXH.trace_eq_sum_eigenvalues
        simp only [Complex.re_sum, Complex.ofReal_re] at hs
        rw [htX, htz0] at hs
        exact fun i => (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => hXm.eigenvalues_nonneg j)).1 hs.symm i (Finset.mem_univ i)
      rw [hXV, S193C_trf V v1 v2]
      simp [hev]
    rw [hφ, htz0]
    simp only [neg_zero, zero_mul, add_zero]
    have := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => S193C_xlogx_le (hlam0 k) (hlamT k)
    rw [← Finset.sum_mul] at this
    linarith

end S193C_ent

section S193C_rel
open Matrix

lemma S193C_cfcdiag {K : Type*} [Fintype K] [DecidableEq K] (d : K → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun k => (d k : ℂ))) = diagonal (fun k => (f (d k) : ℂ)) := by
  have := S193C_cfc (1 : Matrix K K ℂ) (by simp) (by simp) d f
  simpa using this

lemma S193C_tr_diag {K : Type*} [Fintype K] [DecidableEq K] (A : Matrix K K ℂ) (e : K → ℝ) :
    (A * diagonal (fun k => (e k : ℂ))).trace.re = ∑ k, (A k k).re * e k := by
  simp [Matrix.trace, Matrix.mul_diagonal, Complex.re_sum]

variable {I : Type} [Fintype I] [DecidableEq I]

lemma S193C_fre_inst {F : Type} [Fintype F] (i1 i2 : DecidableEq F) (A B : Matrix F F ℂ) :
    @QAlgorithms.Papers.Independent.Frontier18.P01.finiteRelativeEntropy F _ i1 A B =
      @QAlgorithms.Papers.Independent.Frontier18.P01.finiteRelativeEntropy F _ i2 A B := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  rfl

lemma S193C_fe_inst {F : Type} [Fintype F] (i1 i2 : DecidableEq F) (A : Matrix F F ℂ) :
    @QAlgorithms.Papers.Independent.Frontier18.P01.finiteEntropy F _ i1 A =
      @QAlgorithms.Papers.Independent.Frontier18.P01.finiteEntropy F _ i2 A := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  rfl

lemma S193C_split {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    [Fintype {x // p x}] [Fintype {x // ¬ p x}] (f : α → ℝ) :
    ∑ i : {x // p x}, f i + ∑ i : {x // ¬ p x}, f i = ∑ i, f i := by
  convert Fintype.sum_subtype_add_sum_subtype p f

theorem S193C_pinch (X : Matrix I I ℂ) (hX : X.PosSemidef) (p : I → Prop) [DecidablePred p]
    [Fintype {i // p i}] [Fintype {i // ¬ p i}] :
    (cfc (fun x : ℝ => x * Real.log x)
        (X.submatrix (Subtype.val : {i // p i} → I) Subtype.val)).trace.re +
      (cfc (fun x : ℝ => x * Real.log x)
        (X.submatrix (Subtype.val : {i // ¬ p i} → I) Subtype.val)).trace.re ≤
      (cfc (fun x : ℝ => x * Real.log x) X).trace.re := by
  set X1 := X.submatrix (Subtype.val : {i // p i} → I) Subtype.val
  set X2 := X.submatrix (Subtype.val : {i // ¬ p i} → I) Subtype.val
  have hX1 : X1.PosSemidef := hX.submatrix _
  have hX2 : X2.PosSemidef := hX.submatrix _
  obtain ⟨V1, a1, b1, hV1⟩ := S193C_spec X1 hX1.isHermitian
  obtain ⟨V2, a2, b2, hV2⟩ := S193C_spec X2 hX2.isHermitian
  set x1 := hX1.isHermitian.eigenvalues
  set x2 := hX2.isHermitian.eigenvalues
  set e := Equiv.sumCompl p
  set Fb : Matrix ({i // p i} ⊕ {i // ¬ p i}) ({i // p i} ⊕ {i // ¬ p i}) ℂ :=
    fromBlocks V1 0 0 V2
  have hF1 : Fbᴴ * Fb = 1 := by
    simp only [Fb, fromBlocks_conjTranspose, fromBlocks_multiply, a1, a2]; simp
  have hF2 : Fb * Fbᴴ = 1 := by
    simp only [Fb, fromBlocks_conjTranspose, fromBlocks_multiply, b1, b2]; simp
  set W : Matrix I ({i // p i} ⊕ {i // ¬ p i}) ℂ := Fb.submatrix e.symm id
  have hW1 : Wᴴ * W = 1 := by
    simp only [W, conjTranspose_submatrix]
    rw [show Fbᴴ.submatrix id e.symm = Fbᴴ.submatrix id (e.symm : I → _) from rfl,
      submatrix_mul_equiv, hF1, submatrix_id_id]
  have hW2 : W * Wᴴ = 1 := by
    simp only [W, conjTranspose_submatrix]
    rw [show Fb.submatrix e.symm id = Fb.submatrix (e.symm : I → _) (Equiv.refl _) from rfl,
      show Fbᴴ.submatrix id e.symm = Fbᴴ.submatrix (Equiv.refl _) (e.symm : I → _) from rfl,
      submatrix_mul_equiv, hF2, submatrix_one_equiv]
  have hXe : X.submatrix e e = fromBlocks X1 (X.submatrix Subtype.val Subtype.val)
      (X.submatrix Subtype.val Subtype.val) X2 := by
    ext a b <;> rcases a with a | a <;> rcases b with b | b <;> rfl
  have hWXW : Wᴴ * X * W = Fbᴴ * X.submatrix e e * Fb := by
    have : X = (X.submatrix e e).submatrix e.symm e.symm := by simp
    conv_lhs => rw [this]
    simp only [W, conjTranspose_submatrix]
    rw [show Fbᴴ.submatrix id e.symm = Fbᴴ.submatrix id (e.symm : I → _) from rfl,
      show (X.submatrix e e).submatrix e.symm e.symm =
        (X.submatrix e e).submatrix (e.symm : I → _) (e.symm : I → _) from rfl,
      submatrix_mul_equiv,
      show Fb.submatrix e.symm id = Fb.submatrix (e.symm : I → _) id from rfl,
      submatrix_mul_equiv, submatrix_id_id]
  have hD1 : V1ᴴ * X1 * V1 = diagonal (fun i => (x1 i : ℂ)) := by
    rw [hV1]; simp only [Matrix.mul_assoc]; rw [a1, Matrix.mul_one,
      ← Matrix.mul_assoc, a1, Matrix.one_mul]
  have hD2 : V2ᴴ * X2 * V2 = diagonal (fun i => (x2 i : ℂ)) := by
    rw [hV2]; simp only [Matrix.mul_assoc]; rw [a2, Matrix.mul_one,
      ← Matrix.mul_assoc, a2, Matrix.one_mul]
  set d : ({i // p i} ⊕ {i // ¬ p i}) → ℝ := Sum.elim x1 x2
  have hdiag : ∀ k, ((Wᴴ * X * W) k k).re = d k := by
    rw [hWXW, hXe]
    simp only [Fb, fromBlocks_conjTranspose, fromBlocks_multiply]
    intro k
    rcases k with k | k
    · simp only [fromBlocks_apply₁₁, conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero,
        add_zero, zero_add, hD1, d, Sum.elim_inl, diagonal_apply_eq, Complex.ofReal_re]
    · simp only [fromBlocks_apply₂₂, conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero,
        add_zero, zero_add, hD2, d, Sum.elim_inr, diagonal_apply_eq, Complex.ofReal_re]
  have hK := S193C_KL X hX W hW1 hW2 d (fun k => by
      rcases k with k | k
      · exact hX1.eigenvalues_nonneg k
      · exact hX2.eigenvalues_nonneg k) (fun k hk => by rw [hdiag, hk])
  simp only [hdiag] at hK
  have hs1 : (cfc (fun x : ℝ => x * Real.log x) X1).trace.re = ∑ i, x1 i * Real.log (x1 i) := by
    rw [hV1, S193C_trf V1 a1 b1]
  have hs2 : (cfc (fun x : ℝ => x * Real.log x) X2).trace.re = ∑ i, x2 i * Real.log (x2 i) := by
    rw [hV2, S193C_trf V2 a2 b2]
  have ht1 : X1.trace.re = ∑ i, x1 i := by
    have := congrArg Complex.re hX1.isHermitian.trace_eq_sum_eigenvalues; simpa using this
  have ht2 : X2.trace.re = ∑ i, x2 i := by
    have := congrArg Complex.re hX2.isHermitian.trace_eq_sum_eigenvalues; simpa using this
  have htX : X.trace.re = X1.trace.re + X2.trace.re := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum, X1, X2, submatrix_apply]
    exact (S193C_split p (fun i => (X i i).re)).symm
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hK
  simp only [d, Sum.elim_inl, Sum.elim_inr] at hK
  rw [hs1, hs2]
  linarith

/-- real-valued generalized relative entropy -/
def S193C_D {F : Type*} [Fintype F] [DecidableEq F] (A B : Matrix F F ℂ) : ℝ :=
  (cfc (fun x : ℝ => x * Real.log x) A - A * cfc Real.log B + B - A).trace.re

lemma S193C_D_diag {F : Type*} [Fintype F] [DecidableEq F] (A : Matrix F F ℂ) (d : F → ℝ) :
    S193C_D A (diagonal (fun k => (d k : ℂ))) =
      (cfc (fun x : ℝ => x * Real.log x) A).trace.re - ∑ k, (A k k).re * Real.log (d k) +
        ∑ k, d k - ∑ k, (A k k).re := by
  unfold S193C_D
  rw [S193C_cfcdiag]
  simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re, S193C_tr_diag]
  simp [Matrix.trace, Complex.re_sum]

theorem S193C_Rd (X : Matrix I I ℂ) (hX : X.PosSemidef) (d : I → ℝ) (hd : ∀ k, 0 ≤ d k)
    (H0 : ∀ k, d k = 0 → (X k k).re = 0) (s : Finset I) :
    QAlgorithms.Papers.Independent.Frontier18.P01.finiteRelativeEntropy
        (X.submatrix (fun i : s => i.val) (fun i : s => i.val))
        ((diagonal (fun k => (d k : ℂ))).submatrix (fun i : s => i.val) (fun i : s => i.val)) ≤
      ENNReal.ofReal (S193C_D X (diagonal (fun k => (d k : ℂ)))) := by
  set Xs := X.submatrix (fun i : s => i.val) (fun i : s => i.val)
  have hXs : Xs.PosSemidef := hX.submatrix _
  have hDs : (diagonal (fun k => (d k : ℂ))).submatrix (fun i : s => i.val) (fun i : s => i.val) =
      diagonal (fun k : s => (d k.val : ℂ)) := by
    ext a b
    by_cases h : a = b
    · subst h; simp
    · simp [diagonal, h, Subtype.val_injective.ne h]
  have him : ∀ k : s, (Xs k k).im = 0 := fun k => by
    have := congrArg Complex.im (congrFun (congrFun hXs.isHermitian k) k)
    simp only [conjTranspose_apply, Complex.star_def, Complex.conj_im] at this
    linarith
  have hker := S193C_ker Xs hXs (1 : Matrix s s ℂ) (by simp) (by simp) (fun k => d k.val)
    (fun k hk => by
      simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      apply Complex.ext
      · exact H0 k.val hk
      · exact him k)
  simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at hker
  unfold QAlgorithms.Papers.Independent.Frontier18.P01.finiteRelativeEntropy
  rw [hDs, if_pos hker]
  apply ENNReal.ofReal_le_ofReal
  change S193C_D Xs (diagonal (fun k : s => (d k.val : ℂ))) ≤ S193C_D X (diagonal (fun k => (d k : ℂ)))
  rw [S193C_D_diag, S193C_D_diag]
  -- pieces
  letI : Fintype {i // i ∈ s} := Finset.Subtype.fintype s
  have hP := S193C_pinch X hX (· ∈ s)
  set Xc := X.submatrix (Subtype.val : {i // ¬ i ∈ s} → I) Subtype.val
  have hXc : Xc.PosSemidef := hX.submatrix _
  have hKc := S193C_KL Xc hXc (1 : Matrix {i // ¬ i ∈ s} {i // ¬ i ∈ s} ℂ) (by simp) (by simp)
    (fun k : {i // ¬ i ∈ s} => d k.val)
    (fun k => hd _) (fun k hk => by simpa [Xc] using H0 k.val hk)
  simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at hKc
  have htc : Xc.trace.re = ∑ k : {i // ¬ i ∈ s}, (X k.val k.val).re := by
    simp [Matrix.trace, Complex.re_sum, Xc]
  rw [htc] at hKc
  have sp1 := S193C_split (· ∈ s) (fun k => (X k k).re * Real.log (d k))
  have sp2 := S193C_split (· ∈ s) (fun k => d k)
  have sp3 := S193C_split (· ∈ s) (fun k => (X k k).re)
  have hP' : (cfc (fun x : ℝ => x * Real.log x) Xs).trace.re +
      (cfc (fun x : ℝ => x * Real.log x) Xc).trace.re ≤
      (cfc (fun x : ℝ => x * Real.log x) X).trace.re := hP
  have hKc' : ∑ k : {i // ¬ i ∈ s}, (X k k).re * Real.log (d k) ≤
      (cfc (fun x : ℝ => x * Real.log x) Xc).trace.re + ∑ k : {i // ¬ i ∈ s}, d k -
        ∑ k : {i // ¬ i ∈ s}, (X k k).re := hKc
  change (cfc (fun x : ℝ => x * Real.log x) Xs).trace.re - ∑ k : s, (X k k).re * Real.log (d k) +
      ∑ k : s, d k - ∑ k : s, (X k k).re ≤ _
  linarith

end S193C_rel

section S193C_prod
open Matrix
open scoped Kronecker
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

lemma S193C_ts (ρ : Matrix (I × J) (I × J) ℂ) :
    traceSecond ρ = Matrix.of fun a a' => ∑ b, ρ (a, b) (a', b) := by
  ext a a'; simp [traceSecond, tsum_fintype]

lemma S193C_tf (ρ : Matrix (I × J) (I × J) ℂ) :
    traceFirst ρ = Matrix.of fun b b' => ∑ a, ρ (a, b) (a, b') := by
  ext a a'; simp [traceFirst, tsum_fintype]

lemma S193C_ts_psd (ρ : Matrix (I × J) (I × J) ℂ) (hρ : ρ.PosSemidef) :
    (traceSecond ρ).PosSemidef ∧ (traceSecond ρ).trace = ρ.trace := by
  rw [S193C_ts]
  have : (Matrix.of fun a a' => ∑ b, ρ (a, b) (a', b)) =
      ∑ b : J, ρ.submatrix (fun a => (a, b)) (fun a => (a, b)) := by
    ext; simp [Matrix.sum_apply]
  refine ⟨?_, ?_⟩
  · rw [this]; exact Matrix.posSemidef_sum _ fun b _ => hρ.submatrix _
  · simp [Matrix.trace, Fintype.sum_prod_type]

lemma S193C_tf_psd (ρ : Matrix (I × J) (I × J) ℂ) (hρ : ρ.PosSemidef) :
    (traceFirst ρ).PosSemidef ∧ (traceFirst ρ).trace = ρ.trace := by
  rw [S193C_tf]
  have : (Matrix.of fun b b' => ∑ a, ρ (a, b) (a, b')) =
      ∑ a : I, ρ.submatrix (fun b => (a, b)) (fun b => (a, b)) := by
    ext; simp [Matrix.sum_apply]
  refine ⟨?_, ?_⟩
  · rw [this]; exact Matrix.posSemidef_sum _ fun b _ => hρ.submatrix _
  · simp [Matrix.trace, Fintype.sum_prod_type]
    exact Finset.sum_comm

lemma S193C_L1 (ρ : Matrix (I × J) (I × J) ℂ) (P : Matrix I I ℂ) :
    (ρ * (P ⊗ₖ (1 : Matrix J J ℂ))).trace = (traceSecond ρ * P).trace := by
  rw [S193C_ts]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, kroneckerMap_apply,
    Fintype.sum_prod_type, one_apply, Matrix.of_apply, Finset.sum_mul]
  simp [mul_ite]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm

lemma S193C_L2 (ρ : Matrix (I × J) (I × J) ℂ) (Q : Matrix J J ℂ) :
    (ρ * ((1 : Matrix I I ℂ) ⊗ₖ Q)).trace = (traceFirst ρ * Q).trace := by
  rw [S193C_tf]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, kroneckerMap_apply,
    Fintype.sum_prod_type, one_apply, Matrix.of_apply, Finset.sum_mul]
  simp [ite_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

lemma S193C_kunit (U1 : Matrix I I ℂ) (U2 : Matrix J J ℂ) (a1 : U1ᴴ * U1 = 1) (b1 : U1 * U1ᴴ = 1)
    (a2 : U2ᴴ * U2 = 1) (b2 : U2 * U2ᴴ = 1) :
    (U1 ⊗ₖ U2)ᴴ * (U1 ⊗ₖ U2) = 1 ∧ (U1 ⊗ₖ U2) * (U1 ⊗ₖ U2)ᴴ = 1 := by
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, a1, a2, b1, b2,
    one_kronecker_one]
  exact ⟨rfl, rfl⟩

/-- marginal of the diagonal in a product basis -/
lemma S193C_marg1 (ρ : Matrix (I × J) (I × J) ℂ) (U1 : Matrix I I ℂ) (U2 : Matrix J J ℂ)
    (b2 : U2 * U2ᴴ = 1) (k1 : I) :
    ∑ k2, ((U1 ⊗ₖ U2)ᴴ * ρ * (U1 ⊗ₖ U2)) (k1, k2) (k1, k2) =
      (U1ᴴ * traceSecond ρ * U1) k1 k1 := by
  set E1 : Matrix I I ℂ := diagonal (fun a => if a = k1 then 1 else 0)
  have hL : ∑ k2, ((U1 ⊗ₖ U2)ᴴ * ρ * (U1 ⊗ₖ U2)) (k1, k2) (k1, k2) =
      ((U1 ⊗ₖ U2)ᴴ * ρ * (U1 ⊗ₖ U2) * (E1 ⊗ₖ (1 : Matrix J J ℂ))).trace := by
    rw [← diagonal_one, diagonal_kronecker_diagonal]
    simp [Matrix.trace, Matrix.mul_diagonal, Fintype.sum_prod_type, E1]
    rw [Finset.sum_eq_single k1 (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have hR : (U1ᴴ * traceSecond ρ * U1) k1 k1 = (U1ᴴ * traceSecond ρ * U1 * E1).trace := by
    simp [Matrix.trace, Matrix.mul_diagonal, E1]
  have h2 : (U1 ⊗ₖ U2) * (E1 ⊗ₖ (1 : Matrix J J ℂ)) * (U1 ⊗ₖ U2)ᴴ =
      (U1 * E1 * U1ᴴ) ⊗ₖ (1 : Matrix J J ℂ) := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, b2]
  have h1 : ((U1 ⊗ₖ U2)ᴴ * ρ * (U1 ⊗ₖ U2) * (E1 ⊗ₖ (1 : Matrix J J ℂ))).trace =
      (ρ * ((U1 ⊗ₖ U2) * (E1 ⊗ₖ (1 : Matrix J J ℂ)) * (U1 ⊗ₖ U2)ᴴ)).trace := by
    rw [show (U1 ⊗ₖ U2)ᴴ * ρ * (U1 ⊗ₖ U2) * (E1 ⊗ₖ (1 : Matrix J J ℂ)) =
      (U1 ⊗ₖ U2)ᴴ * (ρ * ((U1 ⊗ₖ U2) * (E1 ⊗ₖ (1 : Matrix J J ℂ)))) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h4 : (traceSecond ρ * (U1 * E1 * U1ᴴ)).trace = (U1ᴴ * traceSecond ρ * U1 * E1).trace := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm U1ᴴ]
    simp only [Matrix.mul_assoc]
  rw [hL, hR, h1, h2, S193C_L1, h4]

lemma S193C_marg2 (ρ : Matrix (I × J) (I × J) ℂ) (U1 : Matrix I I ℂ) (U2 : Matrix J J ℂ)
    (b1 : U1 * U1ᴴ = 1) (k2 : J) :
    ∑ k1, ((U1 ⊗ₖ U2)ᴴ * ρ * (U1 ⊗ₖ U2)) (k1, k2) (k1, k2) =
      (U2ᴴ * traceFirst ρ * U2) k2 k2 := by
  set E2 : Matrix J J ℂ := diagonal (fun a => if a = k2 then 1 else 0)
  have hL : ∑ k1, ((U1 ⊗ₖ U2)ᴴ * ρ * (U1 ⊗ₖ U2)) (k1, k2) (k1, k2) =
      ((U1 ⊗ₖ U2)ᴴ * ρ * (U1 ⊗ₖ U2) * ((1 : Matrix I I ℂ) ⊗ₖ E2)).trace := by
    rw [← diagonal_one, diagonal_kronecker_diagonal]
    simp [Matrix.trace, Matrix.mul_diagonal, Fintype.sum_prod_type]
  have hR : (U2ᴴ * traceFirst ρ * U2) k2 k2 = (U2ᴴ * traceFirst ρ * U2 * E2).trace := by
    simp [Matrix.trace, Matrix.mul_diagonal, E2]
  have h2 : (U1 ⊗ₖ U2) * ((1 : Matrix I I ℂ) ⊗ₖ E2) * (U1 ⊗ₖ U2)ᴴ =
      (1 : Matrix I I ℂ) ⊗ₖ (U2 * E2 * U2ᴴ) := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, b1]
  have h1 : ((U1 ⊗ₖ U2)ᴴ * ρ * (U1 ⊗ₖ U2) * ((1 : Matrix I I ℂ) ⊗ₖ E2)).trace =
      (ρ * ((U1 ⊗ₖ U2) * ((1 : Matrix I I ℂ) ⊗ₖ E2) * (U1 ⊗ₖ U2)ᴴ)).trace := by
    rw [show (U1 ⊗ₖ U2)ᴴ * ρ * (U1 ⊗ₖ U2) * ((1 : Matrix I I ℂ) ⊗ₖ E2) =
      (U1 ⊗ₖ U2)ᴴ * (ρ * ((U1 ⊗ₖ U2) * ((1 : Matrix I I ℂ) ⊗ₖ E2))) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h4 : (traceFirst ρ * (U2 * E2 * U2ᴴ)).trace = (U2ᴴ * traceFirst ρ * U2 * E2).trace := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm U2ᴴ]
    simp only [Matrix.mul_assoc]
  rw [hL, hR, h1, h2, S193C_L2, h4]

theorem S193C_prodD (ρ : Matrix (I × J) (I × J) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1) :
    ∃ W : Matrix (I × J) (I × J) ℂ, ∃ d : I × J → ℝ, Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      (∀ k, 0 ≤ d k) ∧ ∑ k, d k = 1 ∧
      productCoeff (traceSecond ρ) (traceFirst ρ) = W * diagonal (fun k => (d k : ℂ)) * Wᴴ ∧
      (∀ k, d k = 0 → ((Wᴴ * ρ * W) k k).re = 0) ∧
      ∑ k, ((Wᴴ * ρ * W) k k).re * Real.log (d k) =
        (cfc (fun x : ℝ => x * Real.log x) (traceSecond ρ)).trace.re +
          (cfc (fun x : ℝ => x * Real.log x) (traceFirst ρ)).trace.re := by
  obtain ⟨h1p, h1t⟩ := S193C_ts_psd ρ hρ
  obtain ⟨h2p, h2t⟩ := S193C_tf_psd ρ hρ
  obtain ⟨U1, a1, b1, hU1⟩ := S193C_spec _ h1p.isHermitian
  obtain ⟨U2, a2, b2, hU2⟩ := S193C_spec _ h2p.isHermitian
  set l1 := h1p.isHermitian.eigenvalues
  set l2 := h2p.isHermitian.eigenvalues
  obtain ⟨wa, wb⟩ := S193C_kunit U1 U2 a1 b1 a2 b2
  set W := U1 ⊗ₖ U2
  set X := Wᴴ * ρ * W
  have hX : X.PosSemidef := hρ.conjTranspose_mul_mul_same W
  have hD1 : U1ᴴ * traceSecond ρ * U1 = diagonal (fun i => (l1 i : ℂ)) := by
    rw [hU1]; simp only [Matrix.mul_assoc]; rw [a1, Matrix.mul_one, ← Matrix.mul_assoc, a1,
      Matrix.one_mul]
  have hD2 : U2ᴴ * traceFirst ρ * U2 = diagonal (fun i => (l2 i : ℂ)) := by
    rw [hU2]; simp only [Matrix.mul_assoc]; rw [a2, Matrix.mul_one, ← Matrix.mul_assoc, a2,
      Matrix.one_mul]
  have hm1 : ∀ k1, ∑ k2, (X (k1, k2) (k1, k2)).re = l1 k1 := fun k1 => by
    rw [← Complex.re_sum, S193C_marg1 ρ U1 U2 b2 k1, hD1]; simp
  have hm2 : ∀ k2, ∑ k1, (X (k1, k2) (k1, k2)).re = l2 k2 := fun k2 => by
    rw [← Complex.re_sum, S193C_marg2 ρ U1 U2 b1 k2, hD2]; simp
  have hXk : ∀ k, 0 ≤ (X k k).re := fun k => by
    have := hX.diag_nonneg (i := k)
    exact (Complex.nonneg_iff.1 this).1
  have hz1 : ∀ k : I × J, l1 k.1 = 0 → (X k k).re = 0 := fun k hk => by
    have := hm1 k.1
    rw [hk] at this
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k2 _ => hXk (k.1, k2))).1 this k.2
      (Finset.mem_univ _)
  have hz2 : ∀ k : I × J, l2 k.2 = 0 → (X k k).re = 0 := fun k hk => by
    have := hm2 k.2
    rw [hk] at this
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k1 _ => hXk (k1, k.2))).1 this k.1
      (Finset.mem_univ _)
  have hsum1 : ∑ i, l1 i = 1 := by
    have := congrArg Complex.re h1p.isHermitian.trace_eq_sum_eigenvalues
    rw [h1t, ht] at this; simpa using this.symm
  have hsum2 : ∑ i, l2 i = 1 := by
    have := congrArg Complex.re h2p.isHermitian.trace_eq_sum_eigenvalues
    rw [h2t, ht] at this; simpa using this.symm
  refine ⟨W, fun k => l1 k.1 * l2 k.2, wa, wb,
    fun k => mul_nonneg (h1p.eigenvalues_nonneg _) (h2p.eigenvalues_nonneg _), ?_, ?_, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, hsum1, hsum2, one_mul]
  · change traceSecond ρ ⊗ₖ traceFirst ρ = _
    rw [hU1, hU2, mul_kronecker_mul, mul_kronecker_mul, diagonal_kronecker_diagonal,
      ← conjTranspose_kronecker]
    congr 3
    funext k
    push_cast; rfl
  · intro k hk
    rcases mul_eq_zero.1 hk with h | h
    · exact hz1 k h
    · exact hz2 k h
  · have hrw : ∀ k : I × J, (X k k).re * Real.log (l1 k.1 * l2 k.2) =
        (X k k).re * Real.log (l1 k.1) + (X k k).re * Real.log (l2 k.2) := by
      intro k
      by_cases h : (X k k).re = 0
      · simp [h]
      · have h1 : l1 k.1 ≠ 0 := fun h' => h (hz1 k h')
        have h2 : l2 k.2 ≠ 0 := fun h' => h (hz2 k h')
        rw [Real.log_mul h1 h2]; ring
    show ∑ k : I × J, (X k k).re * Real.log (l1 k.1 * l2 k.2) = _
    simp_rw [hrw]
    rw [Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm
      (f := fun x y => (X (x, y) (x, y)).re * Real.log (l2 (x, y).2))]
    simp_rw [← Finset.sum_mul, hm1, hm2]
    rw [hU1, hU2, S193C_trf U1 a1 b1, S193C_trf U2 a2 b2]

end S193C_prod

section S193C_cond
open Matrix
open scoped Kronecker
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier18.P01

lemma S193C_H_nonneg {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ)
    (hM : M.PosSemidef) : 0 ≤ S193C_H M := by
  have hH := hM.isHermitian
  obtain ⟨U, h1, h2, hMU⟩ := S193C_spec M hH
  have hT : M.trace.re = ∑ k, hH.eigenvalues k := by
    have := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    simpa using this
  have hφ : (cfc (fun x : ℝ => x * Real.log x) M).trace.re =
      ∑ k, hH.eigenvalues k * Real.log (hH.eigenvalues k) := by
    conv_lhs => rw [hMU]
    rw [S193C_trf U h1 h2]
  unfold S193C_H
  rw [hT, hφ]
  have := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) =>
    S193C_xlogx_le (hM.eigenvalues_nonneg k)
      (Finset.single_le_sum (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ k))
  rw [← Finset.sum_mul] at this
  linarith

theorem S193C_hE {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ)
    (hM : M.PosSemidef) : homogeneousEntropy M = ENNReal.ofReal (S193C_H M) := by
  unfold homogeneousEntropy
  apply le_antisymm
  · refine iSup_le fun s => ?_
    rw [S193C_fe_inst _ inferInstance]
    exact ENNReal.ofReal_le_ofReal (S193C_Hmono M hM s)
  · refine le_iSup_of_le Finset.univ ?_
    rw [S193C_fe_inst _ inferInstance]
    show ENNReal.ofReal (S193C_H (M.submatrix
      (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x)) (Equiv.subtypeUnivEquiv
        (fun x => Finset.mem_univ x)))) ≥ _
    rw [S193C_H_sub M hM.isHermitian]

lemma S193C_D_sub {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (e : K ≃ I) :
    S193C_D (A.submatrix e e) (B.submatrix e e) = S193C_D A B := by
  unfold S193C_D
  rw [S193C_cfc_sub A hA, S193C_cfc_sub B hB,
    show A.submatrix e e * (cfc Real.log B).submatrix e e = (A * cfc Real.log B).submatrix e e
      from submatrix_mul_equiv _ _ _ _ _]
  rw [show (cfc (fun x : ℝ => x * Real.log x) A).submatrix e e -
      (A * cfc Real.log B).submatrix e e + B.submatrix e e - A.submatrix e e =
      (cfc (fun x : ℝ => x * Real.log x) A - A * cfc Real.log B + B - A).submatrix e e by
    ext; simp, S193C_trace_sub]

lemma S193C_ker_sub {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (A B : Matrix I I ℂ) (h : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) (e : K ≃ I) :
    LinearMap.ker (B.submatrix e e).mulVecLin ≤ LinearMap.ker (A.submatrix e e).mulVecLin := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  rw [submatrix_mulVec_equiv] at hv ⊢
  have hB : B *ᵥ (v ∘ e.symm) = 0 := by
    funext x
    have := congrFun hv (e.symm x)
    simpa using this
  have hA : A *ᵥ (v ∘ e.symm) = 0 := by
    have := h (show v ∘ e.symm ∈ LinearMap.ker B.mulVecLin by simpa using hB)
    simpa using this
  rw [hA]; rfl

theorem S193C_gRE {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (ρ : Matrix (I × J) (I × J) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1) :
    generalizedRelativeEntropy ρ (productCoeff (traceSecond ρ) (traceFirst ρ)) =
      ENNReal.ofReal ((cfc (fun x : ℝ => x * Real.log x) ρ).trace.re -
        (cfc (fun x : ℝ => x * Real.log x) (traceSecond ρ)).trace.re -
        (cfc (fun x : ℝ => x * Real.log x) (traceFirst ρ)).trace.re) ∧
      0 ≤ (cfc (fun x : ℝ => x * Real.log x) ρ).trace.re -
        (cfc (fun x : ℝ => x * Real.log x) (traceSecond ρ)).trace.re -
        (cfc (fun x : ℝ => x * Real.log x) (traceFirst ρ)).trace.re := by
  obtain ⟨W, d, wa, wb, hd, hds, hσ, H0, hlog⟩ := S193C_prodD ρ hρ ht
  set σ := productCoeff (traceSecond ρ) (traceFirst ρ)
  set X := Wᴴ * ρ * W
  have hX : X.PosSemidef := hρ.conjTranspose_mul_mul_same W
  have hXim : ∀ k, (X k k).im = 0 := fun k => by
    have := congrArg Complex.im (congrFun (congrFun hX.isHermitian k) k)
    simp only [conjTranspose_apply, Complex.star_def, Complex.conj_im] at this
    linarith
  have H0c : ∀ k, d k = 0 → X k k = 0 := fun k hk => Complex.ext (H0 k hk) (hXim k)
  have hXtr : X.trace = 1 := by
    rw [Matrix.trace_mul_cycle, wb, Matrix.one_mul, ht]
  -- value of S193C_D ρ σ
  have hρφ : (cfc (fun x : ℝ => x * Real.log x) X).trace.re =
      (cfc (fun x : ℝ => x * Real.log x) ρ).trace.re := by
    obtain ⟨U, u1, u2, hU⟩ := S193C_spec ρ hρ.isHermitian
    generalize hρ.isHermitian.eigenvalues = p at hU
    have hXU : X = (Wᴴ * U) * diagonal (fun i => (p i : ℂ)) *
        (Wᴴ * U)ᴴ := by
      simp only [X]; rw [hU]; simp only [conjTranspose_mul, conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    have v1 : (Wᴴ * U)ᴴ * (Wᴴ * U) = 1 := by
      rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc W,
        wb, Matrix.one_mul, u1]
    have v2 : (Wᴴ * U) * (Wᴴ * U)ᴴ = 1 := by
      rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc U,
        u2, Matrix.one_mul, wa]
    rw [hXU, S193C_trf _ v1 v2, hU, S193C_trf U u1 u2]
  have hXre : ∑ k, (X k k).re = 1 := by
    have := congrArg Complex.re hXtr
    simpa [Matrix.trace, Complex.re_sum] using this
  have hDX : S193C_D X (diagonal (fun k => (d k : ℂ))) =
      (cfc (fun x : ℝ => x * Real.log x) ρ).trace.re -
        (cfc (fun x : ℝ => x * Real.log x) (traceSecond ρ)).trace.re -
        (cfc (fun x : ℝ => x * Real.log x) (traceFirst ρ)).trace.re := by
    rw [S193C_D_diag, hρφ, hlog, hds, hXre]; ring
  have hDρ : S193C_D ρ σ = S193C_D X (diagonal (fun k => (d k : ℂ))) := by
    rw [hDX]
    unfold S193C_D
    rw [hσ, S193C_cfc W wa wb]
    simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re, S193C_tr,
      Complex.re_sum]
    have h1 : (W * diagonal (fun k => (d k : ℂ)) * Wᴴ).trace.re = 1 := by
      rw [Matrix.trace_mul_cycle, wa, Matrix.one_mul, Matrix.trace_diagonal, Complex.re_sum]
      simpa using hds
    rw [h1, ht]
    have : ∀ k, ((Wᴴ * ρ * W) k k * ((Real.log (d k) : ℝ) : ℂ)).re =
        ((Wᴴ * ρ * W) k k).re * Real.log (d k) := fun k => by simp
    simp only [this]
    rw [hlog]; simp; ring
  have hnn : 0 ≤ S193C_D X (diagonal (fun k => (d k : ℂ))) := by
    have hK := S193C_KL ρ hρ W wa wb d hd H0
    rw [hlog, hds] at hK
    rw [hDX]
    have : ρ.trace.re = 1 := by rw [ht]; simp
    linarith
  rw [← hDX]
  refine ⟨?_, hnn⟩
  apply le_antisymm
  · -- DPI with unitary channel
    have hne : Nonempty (I × J) := by
      by_contra h
      rw [not_nonempty_iff] at h
      have : ρ.trace = 0 := by simp [Matrix.trace]
      rw [this] at ht; exact zero_ne_one ht
    have hXd : IsDensity X := S193C_density_of_psd hX hXtr
    have hDd : IsDensity (diagonal (fun k => (d k : ℂ))) := by
      refine S193C_density_of_psd ?_ ?_
      · rw [posSemidef_diagonal_iff]; intro k; exact_mod_cast hd k
      · rw [Matrix.trace_diagonal]; exact_mod_cast hds
    have hdpi := S193C_dpi (S193C_uch W wa wb) X (diagonal (fun k => (d k : ℂ))) hXd hDd
    have e1 : (S193C_uch W wa wb).val X = ρ := by
      show W * (Wᴴ * ρ * W) * Wᴴ = ρ
      simp only [← Matrix.mul_assoc]; rw [wb, Matrix.one_mul, Matrix.mul_assoc, wb, Matrix.mul_one]
    have e2 : (S193C_uch W wa wb).val (diagonal (fun k => (d k : ℂ))) = σ := by
      show W * diagonal (fun k => (d k : ℂ)) * Wᴴ = σ
      rw [hσ]
    rw [e1, e2] at hdpi
    refine hdpi.trans ?_
    unfold generalizedRelativeEntropy
    refine iSup_le fun s => ?_
    rw [S193C_fre_inst _ inferInstance]
    exact S193C_Rd X hX d hd H0 s
  · rw [hDρ.symm]
    unfold generalizedRelativeEntropy
    refine le_iSup_of_le Finset.univ ?_
    rw [S193C_fre_inst _ inferInstance]
    set e := Equiv.subtypeUnivEquiv (fun x : I × J => Finset.mem_univ x)
    have hσH : σ.IsHermitian := by rw [hσ]; exact S193C_herm W d
    have hker := S193C_ker ρ hρ W wa wb d H0c
    rw [← hσ] at hker
    have hk2 := S193C_ker_sub ρ σ hker e
    show ENNReal.ofReal (S193C_D ρ σ) ≤ finiteRelativeEntropy (ρ.submatrix e e) (σ.submatrix e e)
    unfold finiteRelativeEntropy
    rw [if_pos hk2]
    exact le_of_eq (congrArg ENNReal.ofReal (S193C_D_sub ρ σ hρ.isHermitian hσH e).symm)

end S193C_cond

section S193C_fin
open Matrix
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier18.P01
open QAlgorithms.Papers.Independent.Claimed50.P18

lemma S193C_ofReal {t : ℝ} (ht : 0 ≤ t) : ((ENNReal.ofReal t : ENNReal) : EReal) = (t : EReal) := by
  rw [EReal.coe_ennreal_ofReal, max_eq_left ht]

theorem S193C_cond {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (ρ : Matrix (I × J) (I × J) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1) :
    finiteFirstConditionalEntropy ρ =
      (((cfc (fun x : ℝ => x * Real.log x) (traceFirst ρ)).trace.re -
        (cfc (fun x : ℝ => x * Real.log x) ρ).trace.re : ℝ) : EReal) := by
  obtain ⟨h1p, h1t⟩ := S193C_ts_psd ρ hρ
  obtain ⟨hg, hnn⟩ := S193C_gRE ρ hρ ht
  unfold finiteFirstConditionalEntropy
  rw [S193C_hE _ h1p, hg, S193C_ofReal (S193C_H_nonneg _ h1p), S193C_ofReal hnn]
  have hH : S193C_H (traceSecond ρ) =
      -(cfc (fun x : ℝ => x * Real.log x) (traceSecond ρ)).trace.re := by
    unfold S193C_H; rw [h1t, ht]; simp
  rw [hH, ← EReal.coe_sub]
  congr 1
  ring

lemma S193C_dm {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (Y : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hY : Y.PosSemidef) :
    (dropMiddle Y).PosSemidef ∧ (dropMiddle Y).trace = Y.trace := by
  classical
  have h : dropMiddle Y = ∑ b : B, Y.submatrix (fun p : A × C => (p.1, (b, p.2)))
      (fun p : A × C => (p.1, (b, p.2))) := by
    ext p q; simp [dropMiddle, tsum_fintype, Matrix.sum_apply]
  refine ⟨?_, ?_⟩
  · rw [h]; exact Matrix.posSemidef_sum _ fun b _ => hY.submatrix _
  · rw [h, Matrix.trace_sum]
    simp only [Matrix.trace, Matrix.diag, submatrix_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]

end S193C_fin

open Filter
open scoped ENNReal BigOperators
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier18.P01
open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)
open QAlgorithms.Papers.Independent.Claimed50.P18

attribute [local instance] Classical.propDecidable

theorem solution {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (rho : State ((A × B) × (C × D))) :
    finiteFirstConditionalEntropy rho.coefficients =
      finiteFirstConditionalEntropy (dropMiddle (associateRight rho.coefficients)) +
        finiteFirstConditionalEntropy (traceFirst (associateRight rho.coefficients)) -
          (finiteFirstConditionalEntropy (dropMiddle (associateRight rho.coefficients)) -
            finiteFirstConditionalEntropy (associateRight rho.coefficients)) := by
  obtain ⟨hR, hRt⟩ := S193C_psd_of_density rho.density
  set R := rho.coefficients
  have hM4 : associateRight R = R.submatrix (Equiv.prodAssoc A B (C × D)).symm
      (Equiv.prodAssoc A B (C × D)).symm := rfl
  have hM4p : (associateRight R).PosSemidef := by rw [hM4]; exact hR.submatrix _
  have hM4t : (associateRight R).trace = 1 := by rw [hM4, S193C_trace_sub, hRt]
  obtain ⟨hM3p, hM3t⟩ := S193C_tf_psd (associateRight R) hM4p
  obtain ⟨hM2p, hM2t⟩ := S193C_dm (associateRight R) hM4p
  rw [S193C_cond R hR hRt, S193C_cond _ hM2p (hM2t.trans hM4t),
    S193C_cond _ hM3p (hM3t.trans hM4t), S193C_cond _ hM4p hM4t]
  have i1 : traceFirst (traceFirst (associateRight R)) = traceFirst R := by
    ext p q
    simp [traceFirst, associateRight, tsum_fintype, Fintype.sum_prod_type]
    exact Finset.sum_comm
  have i2 : (cfc (fun x : ℝ => x * Real.log x) (associateRight R)).trace.re =
      (cfc (fun x : ℝ => x * Real.log x) R).trace.re := by
    rw [hM4, S193C_cfc_sub R hR.isHermitian, S193C_trace_sub]
  rw [i1, i2, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub]
  congr 1
  ring
