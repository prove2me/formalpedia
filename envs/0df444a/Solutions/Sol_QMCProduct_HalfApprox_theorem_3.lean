-- Prove2me | solution 1 for QMCProduct.HalfApprox.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T10:15:28.546831+00:00
-- url     : https://prove2.me/submissions/d4d873e7-9908-446d-9ad9-fe70f908a233
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QMCProduct_HalfApprox_Algorithm
import Theorems.Thm_QMCProduct_HalfApprox_remark_3
import Theorems.Thm_QMCProduct_HalfApprox_fact_2
import Theorems.Thm_QMCProduct_HalfApprox_lemma_9
import Theorems.Thm_QMCProduct_HalfApprox_lemma_5
import Theorems.Thm_QMCProduct_HalfApprox_fact_1
import Theorems.Thm_QMCProduct_HalfApprox_deltaL_edge

set_option autoImplicit false

namespace QMCHalfAux

open QMCProduct.HalfApprox QAlgorithms Matrix

lemma kronAll_mul {n : ℕ} (f g : Fin n → Matrix Bool Bool ℂ) :
    kronAll f * kronAll g = kronAll (fun q => f q * g q) := by
  ext y x
  simp only [kronAll, Matrix.mul_apply, Matrix.of_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.prod_mul_distrib]

lemma kronAll_trace {n : ℕ} (f : Fin n → Matrix Bool Bool ℂ) :
    (kronAll f).trace = ∏ q, (f q).trace := by
  simp only [kronAll, Matrix.trace, Matrix.diag, Matrix.of_apply]
  rw [Fintype.prod_sum]

lemma kronAll_conjTranspose {n : ℕ} (f : Fin n → Matrix Bool Bool ℂ) :
    (kronAll f)ᴴ = kronAll (fun q => (f q)ᴴ) := by
  ext y x
  simp [kronAll, Matrix.conjTranspose_apply]

lemma kronAll_one {n : ℕ} : kronAll (fun _ : Fin n => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext y x
  simp only [kronAll, Matrix.of_apply, Matrix.one_apply]
  by_cases h : y = x
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨q, hq⟩ : ∃ q, y q ≠ x q := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hq])

lemma onSite_eq {n : ℕ} (i : Fin n) (A : Matrix Bool Bool ℂ) :
    onSite i A = kronAll (fun q => if q = i then A else 1) := rfl

lemma onSite_mul_onSite {n : ℕ} (i j : Fin n) (A B : Matrix Bool Bool ℂ) :
    onSite i A * onSite j B =
      kronAll (fun q => (if q = i then A else 1) * (if q = j then B else 1)) := by
  rw [onSite_eq, onSite_eq, kronAll_mul]

lemma onSite_comm {n : ℕ} (i j : Fin n) (hij : i ≠ j) (A B : Matrix Bool Bool ℂ) :
    onSite i A * onSite j B = onSite j B * onSite i A := by
  rw [onSite_mul_onSite, onSite_mul_onSite]
  congr 1; funext q
  by_cases hi : q = i
  · subst hi; simp [hij]
  · by_cases hj : q = j
    · subst hj; simp [hi]
    · simp [hi, hj]

end QMCHalfAux

namespace QMCHalfAux
open QMCProduct.HalfApprox QAlgorithms Matrix
open scoped MatrixOrder ComplexOrder

lemma psd_exists_sqrt (A : Matrix Bool Bool ℂ) (hA : A.PosSemidef) : ∃ B : Matrix Bool Bool ℂ, A = Bᴴ * B := by
  have h0 : (0 : Matrix Bool Bool ℂ) ≤ A := hA.nonneg
  obtain ⟨X, hX, -, hXX⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts (A := Matrix Bool Bool ℂ) (a := A)
      hA.isHermitian (QuasispectrumRestricts.nnreal_of_nonneg h0)
  refine ⟨X, ?_⟩
  rw [← hXX]
  have : Xᴴ = X := hX.star_eq
  rw [this]

lemma kronAll_psd {n : ℕ} (f : Fin n → Matrix Bool Bool ℂ) (hf : ∀ q, (f q).PosSemidef) :
    (kronAll f).PosSemidef := by
  choose B hB using fun q => psd_exists_sqrt (f q) (hf q)
  have : kronAll f = (kronAll B)ᴴ * kronAll B := by
    rw [kronAll_conjTranspose, kronAll_mul]
    congr 1; funext q; exact hB q
  rw [this]
  exact posSemidef_conjTranspose_mul_self _

end QMCHalfAux

namespace QMCHalfAux
open QMCProduct.HalfApprox QAlgorithms Matrix
open scoped MatrixOrder ComplexOrder

lemma blochState_ff (θ : EuclideanSpace ℝ (Fin 3)) : blochState θ false false = ((1 + θ 2 : ℝ) : ℂ) / 2 := by
  simp [blochState, pauliX, pauliY, pauliZ]; ring
lemma blochState_tt (θ : EuclideanSpace ℝ (Fin 3)) : blochState θ true true = ((1 - θ 2 : ℝ) : ℂ) / 2 := by
  simp [blochState, pauliX, pauliY, pauliZ]; ring
lemma blochState_ft (θ : EuclideanSpace ℝ (Fin 3)) :
    blochState θ false true = ((θ 0 : ℂ) - (θ 1 : ℂ) * Complex.I) / 2 := by
  simp [blochState, pauliX, pauliY, pauliZ]; ring
lemma blochState_tf (θ : EuclideanSpace ℝ (Fin 3)) :
    blochState θ true false = ((θ 0 : ℂ) + (θ 1 : ℂ) * Complex.I) / 2 := by
  simp [blochState, pauliX, pauliY, pauliZ]; ring

end QMCHalfAux

namespace QMCHalfAux
open QMCProduct.HalfApprox QAlgorithms Matrix
open scoped MatrixOrder ComplexOrder

lemma blochState_psd (θ : EuclideanSpace ℝ (Fin 3)) (hθ : θ 0 ^ 2 + θ 1 ^ 2 + θ 2 ^ 2 ≤ 1) :
    (blochState θ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext a b
    cases a <;> cases b <;>
      simp [conjTranspose_apply, blochState_ff, blochState_tt, blochState_ft, blochState_tf,
        Complex.ext_iff]
  · intro x
    simp only [dotProduct, mulVec, Fintype.sum_bool, blochState_ff, blochState_tt, blochState_ft,
      blochState_tf]
    rw [Complex.nonneg_iff]
    set p1 := (x true).re; set p2 := (x true).im; set q1 := (x false).re; set q2 := (x false).im
    set a := θ 0; set b := θ 1; set c := θ 2
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.div_re, Complex.div_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
    norm_num
    constructor
    · have hc1 : 0 ≤ 1 - c := by nlinarith [sq_nonneg a, sq_nonneg b]
      have hc2 : 0 ≤ 1 + c := by nlinarith [sq_nonneg a, sq_nonneg b]
      set A := p1 ^ 2 + p2 ^ 2 with hA
      set B := q1 ^ 2 + q2 ^ 2 with hB
      set C := p1 * q1 + p2 * q2 with hC
      set D := p2 * q1 - p1 * q2 with hD
      have hA0 : 0 ≤ A := by positivity
      have hB0 : 0 ≤ B := by positivity
      have hCD : C ^ 2 + D ^ 2 = A * B := by rw [hA, hB, hC, hD]; ring
      have hcs : (a * C + b * D) ^ 2 ≤ (a ^ 2 + b ^ 2) * (C ^ 2 + D ^ 2) := by
        nlinarith [sq_nonneg (a * D - b * C)]
      have hab : (a ^ 2 + b ^ 2) * (A * B) ≤ ((1 - c) * A) * ((1 + c) * B) := by
        have : a ^ 2 + b ^ 2 ≤ (1 - c) * (1 + c) := by nlinarith
        have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
        nlinarith
      have hS0 : 0 ≤ (1 - c) * A + (1 + c) * B := by positivity
      have hsq : (2 * (a * C + b * D)) ^ 2 ≤ ((1 - c) * A + (1 + c) * B) ^ 2 := by
        nlinarith [sq_nonneg ((1 - c) * A - (1 + c) * B)]
      have h3 := (abs_le_of_sq_le_sq' hsq hS0).1
      have e : (x true).re * ((1 - c) * 2 / 4 * (x true).re + (a * 2 / 4 * (x false).re - b * 2 / 4 * (x false).im)) +
        (x true).im * ((1 - c) * 2 / 4 * (x true).im + (a * 2 / 4 * (x false).im + b * 2 / 4 * (x false).re)) +
      ((x false).re * (a * 2 / 4 * (x true).re - -(b * 2) / 4 * (x true).im + (1 + c) * 2 / 4 * (x false).re) +
        (x false).im * (a * 2 / 4 * (x true).im + -(b * 2) / 4 * (x true).re + (1 + c) * 2 / 4 * (x false).im))
        = ((1 - c) * A + (1 + c) * B + 2 * (a * C + b * D)) / 2 := by
        rw [hA, hB, hC, hD]; ring
      rw [e]; linarith
    · ring
end QMCHalfAux

namespace QMCHalfAux
open QMCProduct.HalfApprox QAlgorithms Matrix
open scoped MatrixOrder ComplexOrder

/-- sign of a Z eigenvalue -/
def zf (b : Bool) : ℂ := if b then -1 else 1

lemma zf_not (b : Bool) : zf (!b) = - zf b := by cases b <;> simp [zf]
lemma zf_sq (b : Bool) : zf b * zf b = 1 := by cases b <;> simp [zf]

lemma kronAll_diagonal {n : ℕ} (d : Fin n → Bool → ℂ) :
    kronAll (fun q => diagonal (d q)) = diagonal (fun y => ∏ q, d q (y q)) := by
  ext y x
  simp only [kronAll, Matrix.of_apply, diagonal_apply]
  by_cases h : y = x
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨q, hq⟩ : ∃ q, y q ≠ x q := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hq])

lemma pauliZ_eq : pauliZ = diagonal zf := by
  unfold pauliZ zf; congr 1

lemma Z_eq {n : ℕ} (i : Fin n) : (Z i : Op n) = diagonal (fun y => zf (y i)) := by
  have : (fun q : Fin n => if q = i then pauliZ else (1 : Matrix Bool Bool ℂ)) =
      fun q => diagonal (fun b => if q = i then zf b else 1) := by
    funext q; by_cases h : q = i <;> simp [h, pauliZ_eq]
  simp only [Z, onSite_eq, this, kronAll_diagonal]
  congr 1; funext y
  simp

lemma list_prod_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    (l : List α) (f : α → ι → ℂ) :
    (l.map (fun e => diagonal (f e))).prod = diagonal (fun y => (l.map (fun e => f e y)).prod) := by
  induction l with
  | nil => simp
  | cons e l ih => simp [ih, diagonal_mul_diagonal]

lemma largeState_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ρt : Op n) (γ : ℝ) :
    largeState G ρt γ = diagonal (fun y => ∏ e ∈ large G ρt γ,
      (1 / 4 : ℂ) * (1 - zf (y e.1) * zf (y e.2))) := by
  have h1 : ∀ e : Fin n × Fin n, (1 / 4 : ℂ) • (1 - Z e.1 * Z e.2 : Op n) =
      diagonal (fun y => (1 / 4 : ℂ) * (1 - zf (y e.1) * zf (y e.2))) := by
    intro e
    rw [Z_eq, Z_eq, diagonal_mul_diagonal]
    ext y x
    by_cases h : y = x
    · subst h; simp [diagonal_apply]
    · simp [diagonal_apply, h, one_apply]
  unfold largeState
  simp_rw [h1]
  rw [list_prod_diagonal]
  congr 1; funext y
  rw [Finset.prod_map_toList]

/-- Trace of `P * (diag a * K)` for Kronecker-product `P`, `K`. -/
lemma trace_kron_diag_kron {n : ℕ} (p k : Fin n → Matrix Bool Bool ℂ) (a : Qubits n → ℂ) :
    (kronAll p * (diagonal a * kronAll k)).trace =
      ∑ y, a y * ∏ q, (k q * p q) (y q) (y q) := by
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc, kronAll_mul]
  simp only [Matrix.trace, Matrix.diag, diagonal_mul, kronAll, Matrix.of_apply]

/-- flipping one qubit -/
def flipAt {n : ℕ} (i : Fin n) : Equiv.Perm (Qubits n) where
  toFun y := Function.update y i (!y i)
  invFun y := Function.update y i (!y i)
  left_inv y := by
    funext q; by_cases h : q = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  right_inv y := by
    funext q; by_cases h : q = i
    · subst h; simp
    · simp [Function.update_of_ne h]

lemma flipAt_apply_self {n : ℕ} (i : Fin n) (y : Qubits n) : flipAt i y i = !y i := by
  simp [flipAt]

lemma flipAt_apply_ne {n : ℕ} (i q : Fin n) (h : q ≠ i) (y : Qubits n) : flipAt i y q = y q := by
  simp [flipAt, Function.update_of_ne h]

lemma sum_eq_zero_of_antiinv {n : ℕ} (σ : Equiv.Perm (Qubits n)) (F : Qubits n → ℂ)
    (h : ∀ y, F (σ y) = - F y) : ∑ y, F y = 0 := by
  have h1 : ∑ y, F y = ∑ y, F (σ y) := (Equiv.sum_comp σ F).symm
  simp_rw [h] at h1
  rw [Finset.sum_neg_distrib] at h1
  have : (2 : ℂ) * ∑ y, F y = 0 := by linear_combination h1
  simpa using this

end QMCHalfAux

namespace QMCHalfAux
open QMCProduct.HalfApprox QAlgorithms Matrix
open scoped MatrixOrder ComplexOrder

lemma sum_prod_matching {n : ℕ} (L : Finset (Fin n × Fin n))
    (hm : ∀ e ∈ L, ∀ f ∈ L, e ≠ f → e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)
    (hne : ∀ e ∈ L, e.1 ≠ e.2)
    (m : Fin n → Bool → ℂ) (hconst : ∀ e ∈ L, ∀ b, m e.1 (!b) = m e.1 b) :
    ∀ L' ⊆ L, ∑ y : Qubits n, (∏ e ∈ L', (1 - zf (y e.1) * zf (y e.2))) * ∏ q, m q (y q) =
      ∑ y : Qubits n, ∏ q, m q (y q) := by
  intro L'
  induction L' using Finset.induction_on with
  | empty => intro _; simp
  | insert e s he ih =>
    intro hsub
    have heL : e ∈ L := hsub (Finset.mem_insert_self e s)
    have hsL : s ⊆ L := fun x hx => hsub (Finset.mem_insert_of_mem hx)
    simp_rw [Finset.prod_insert he, sub_mul, one_mul, Finset.sum_sub_distrib, ih hsL]
    rw [sub_eq_self]
    simp_rw [mul_assoc]
    apply sum_eq_zero_of_antiinv (flipAt e.1)
    intro y
    have h1 : zf (flipAt e.1 y e.1) = -zf (y e.1) := by
      rw [flipAt_apply_self, zf_not]
    have h1' : zf (flipAt e.1 y e.2) = zf (y e.2) := by
      rw [flipAt_apply_ne _ _ (hne e heL).symm]
    have h2 : ∏ f ∈ s, (1 - zf (flipAt e.1 y f.1) * zf (flipAt e.1 y f.2)) =
        ∏ f ∈ s, (1 - zf (y f.1) * zf (y f.2)) := by
      refine Finset.prod_congr rfl (fun f hf => ?_)
      have hfe : e ≠ f := fun h => he (h ▸ hf)
      obtain ⟨a1, a2, -, -⟩ := hm e heL f (hsL hf) hfe
      rw [flipAt_apply_ne _ _ (Ne.symm a1), flipAt_apply_ne _ _ (Ne.symm a2)]
    have h3 : ∏ q, m q (flipAt e.1 y q) = ∏ q, m q (y q) := by
      refine Finset.prod_congr rfl (fun q _ => ?_)
      by_cases hq : q = e.1
      · subst hq; rw [flipAt_apply_self, hconst e heL]
      · rw [flipAt_apply_ne _ _ hq]
    rw [h1, h1', h2, h3]; ring

lemma sum_prod_eq_prod_sum {n : ℕ} (m : Fin n → Bool → ℂ) :
    ∑ y : Qubits n, ∏ q, m q (y q) = ∏ q, (m q true + m q false) := by
  rw [← Fintype.prod_sum]
  simp [Fintype.sum_bool]

/-- the generic trace functional -/
noncomputable def Tf {n : ℕ} (a : Qubits n → ℂ) (k p : Fin n → Matrix Bool Bool ℂ) : ℂ :=
  ∑ y, a y * ∏ q, (k q * p q) (y q) (y q)

lemma Tf_eq_zero {n : ℕ} (a : Qubits n → ℂ) (k p : Fin n → Matrix Bool Bool ℂ) (q0 : Fin n)
    (h : ∀ b, (k q0 * p q0) b b = 0) : Tf a k p = 0 := by
  unfold Tf
  refine Finset.sum_eq_zero (fun y _ => ?_)
  rw [Finset.prod_eq_zero (Finset.mem_univ q0) (h _), mul_zero]

lemma Tf_diag {n : ℕ} (a : Qubits n → ℂ) (k : Fin n → Matrix Bool Bool ℂ) (d : Fin n → Bool → ℂ) :
    Tf a k (fun q => diagonal (d q)) = ∑ y, a y * (∏ q, k q (y q) (y q)) * ∏ q, d q (y q) := by
  unfold Tf
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl (fun q _ => ?_)
  rw [mul_diagonal]

lemma hQMC_eq {n : ℕ} (i j : Fin n) :
    hQMC i j = (1 / 4 : ℂ) • (kronAll (fun _ => 1) -
      kronAll (fun q => (if q = i then pauliX else 1) * (if q = j then pauliX else 1)) -
      kronAll (fun q => (if q = i then pauliY else 1) * (if q = j then pauliY else 1)) -
      kronAll (fun q => diagonal ((fun q b => (if q = i then zf b else 1) * (if q = j then zf b else 1)) q))) := by
  have hz : (fun q => diagonal ((fun q b => (if q = i then zf b else 1) * (if q = j then zf b else 1)) q)) =
      fun q => (if q = i then pauliZ else 1) * (if q = j then pauliZ else (1 : Matrix Bool Bool ℂ)) := by
    funext q
    simp only []
    rw [← diagonal_mul_diagonal]
    congr 1 <;> split_ifs <;> simp [pauliZ_eq]
  rw [hz, kronAll_one, ← onSite_mul_onSite, ← onSite_mul_onSite, ← onSite_mul_onSite]
  rfl

lemma hQMC_trace {n : ℕ} (i j : Fin n) (a : Qubits n → ℂ) (k : Fin n → Matrix Bool Bool ℂ) :
    (hQMC i j * (diagonal a * kronAll k)).trace = (1 / 4 : ℂ) * (Tf a k (fun _ => 1) -
      Tf a k (fun q => (if q = i then pauliX else 1) * (if q = j then pauliX else 1)) -
      Tf a k (fun q => (if q = i then pauliY else 1) * (if q = j then pauliY else 1)) -
      Tf a k (fun q => diagonal ((fun q b => (if q = i then zf b else 1) * (if q = j then zf b else 1)) q))) := by
  rw [hQMC_eq]
  simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.trace_smul, Matrix.trace_sub,
    trace_kron_diag_kron, smul_eq_mul]
  rfl

end QMCHalfAux

namespace QMCHalfAux
open QMCProduct.HalfApprox QAlgorithms Matrix
open scoped MatrixOrder ComplexOrder

lemma val_swap {n : ℕ} (ρt : Op n) (i j : Fin n) (A : Matrix Bool Bool ℂ) :
    val ρt (onSite i A * onSite j A) = val ρt (onSite j A * onSite i A) := by
  by_cases h : i = j
  · subst h; rfl
  · rw [onSite_comm i j h]

lemma v_symm {n : ℕ} (ρt : Op n) (i j : Fin n) : v ρt i j = v ρt j i := by
  unfold v X Y Z
  rw [val_swap ρt i j, val_swap ρt i j pauliY, val_swap ρt i j pauliZ]

lemma mu_symm {n : ℕ} (ρt : Op n) (i j : Fin n) : mu ρt i j = mu ρt j i := by
  unfold mu X Y Z
  rw [val_swap ρt i j, val_swap ρt i j pauliY, val_swap ρt i j pauliZ]

lemma hQMC_symm {n : ℕ} (i j : Fin n) : hQMC i j = hQMC j i := by
  by_cases h : i = j
  · subst h; rfl
  · unfold hQMC X Y Z
    rw [onSite_comm i j h, onSite_comm i j h pauliY, onSite_comm i j h pauliZ]

section structure_facts
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ρt : Op n) (γ : ℝ)

lemma large_spec {e : Fin n × Fin n} (he : e ∈ large G ρt γ) :
    e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ γ < v ρt e.1 e.2 := by
  simp only [large, edges, Finset.mem_filter, Finset.mem_univ, true_and] at he
  exact ⟨he.1.1, he.1.2, he.2⟩

lemma large_not_inB1 {e : Fin n × Fin n} (he : e ∈ large G ρt γ) : ¬ inB G ρt γ e.1 := by
  obtain ⟨-, hadj, hv⟩ := large_spec G ρt γ he
  intro hB; have := hB e.2 hadj; linarith

lemma large_not_inB2 {e : Fin n × Fin n} (he : e ∈ large G ρt γ) : ¬ inB G ρt γ e.2 := by
  obtain ⟨-, hadj, hv⟩ := large_spec G ρt γ he
  intro hB; have := hB e.1 hadj.symm; rw [v_symm] at this; linarith

lemma mem_large_of {i j : Fin n} (hij : i < j) (hadj : G.Adj i j) (hv : γ < v ρt i j) :
    (i, j) ∈ large G ρt γ := by
  simp only [large, edges, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨⟨hij, hadj⟩, hv⟩

lemma exists_large_of_adj {i j : Fin n} (hadj : G.Adj i j) (hv : γ < v ρt i j) :
    ∃ e ∈ large G ρt γ, (e.1 = i ∧ e.2 = j) ∨ (e.1 = j ∧ e.2 = i) := by
  rcases lt_trichotomy i j with h | h | h
  · exact ⟨(i, j), mem_large_of G ρt γ h hadj hv, Or.inl ⟨rfl, rfl⟩⟩
  · exact absurd h (G.ne_of_adj hadj)
  · refine ⟨(j, i), mem_large_of G ρt γ h hadj.symm (by rw [v_symm]; exact hv), Or.inr ⟨rfl, rfl⟩⟩

lemma not_inB_exists {q : Fin n} (hq : ¬ inB G ρt γ q) :
    ∃ e ∈ large G ρt γ, q = e.1 ∨ q = e.2 := by
  unfold inB at hq; push Not at hq
  obtain ⟨j, hadj, hv⟩ := hq
  obtain ⟨e, he, h⟩ := exists_large_of_adj G ρt γ hadj hv
  rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact ⟨e, he, Or.inl h1.symm⟩
  · exact ⟨e, he, Or.inr h2.symm⟩

end structure_facts

end QMCHalfAux

namespace QMCHalfAux
open QMCProduct.HalfApprox QAlgorithms Matrix
open scoped MatrixOrder ComplexOrder

lemma unitVec_norm_le {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : ‖unitVec x‖ ≤ 1 := by
  unfold unitVec
  rw [norm_smul, norm_inv, norm_norm]
  by_cases h : ‖x‖ = 0
  · simp [h]
  · rw [inv_mul_cancel₀ h]

lemma bloch_sq_le {n d : ℕ} {Ω : Type} (W : Fin n → EuclideanSpace ℝ (Fin d))
    (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) (i : Fin n) :
    (bloch W R ω i) 0 ^ 2 + (bloch W R ω i) 1 ^ 2 + (bloch W R ω i) 2 ^ 2 ≤ 1 := by
  have h := unitVec_norm_le (gaussianProject R ω (W i))
  have h2 := EuclideanSpace.real_norm_sq_eq (bloch W R ω i)
  rw [Fin.sum_univ_three] at h2
  have h' : ‖bloch W R ω i‖ ≤ 1 := h
  have : ‖bloch W R ω i‖ ^ 2 ≤ 1 := by
    have h0 := norm_nonneg (bloch W R ω i)
    nlinarith
  linarith

end QMCHalfAux

namespace QMCHalfAux
open QMCProduct.HalfApprox QAlgorithms Matrix
open scoped MatrixOrder ComplexOrder

section main
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ρt : Op n)

noncomputable def kq {d : ℕ} {Ω : Type} (W : Fin n → EuclideanSpace ℝ (Fin d))
    (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) : Fin n → Matrix Bool Bool ℂ := by
  classical
  exact fun i => if inB G ρt (911 / 1000 : ℝ) i then blochState (bloch W R ω i) else 1

noncomputable def aL (y : Qubits n) : ℂ :=
  ∏ e ∈ large G ρt (911 / 1000 : ℝ), (1 / 4 : ℂ) * (1 - zf (y e.1) * zf (y e.2))

lemma alg4State_eq {d : ℕ} {Ω : Type} (W : Fin n → EuclideanSpace ℝ (Fin d))
    (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) :
    alg4State G ρt (911 / 1000 : ℝ) W R ω = diagonal (aL G ρt) * kronAll (kq G ρt W R ω) := by
  unfold alg4State; rw [largeState_eq]; rfl

lemma kq_nonB {d : ℕ} {Ω : Type} (W : Fin n → EuclideanSpace ℝ (Fin d))
    (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) (q : Fin n) (hq : ¬ inB G ρt (911 / 1000 : ℝ) q) :
    kq G ρt W R ω q = 1 := by
  classical
  unfold kq; simp [hq]

lemma kq_B {d : ℕ} {Ω : Type} (W : Fin n → EuclideanSpace ℝ (Fin d))
    (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) (q : Fin n) (hq : inB G ρt (911 / 1000 : ℝ) q) :
    kq G ρt W R ω q = blochState (bloch W R ω q) := by
  classical
  unfold kq; simp [hq]

lemma matching (hρ : IsPseudoDensity 2 ρt) :
    ∀ e ∈ large G ρt (911 / 1000 : ℝ), ∀ f ∈ large G ρt (911 / 1000 : ℝ), e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 :=
  fun e he f hf hef => remark_3 G ρt hρ e f he hf hef

lemma large_ne : ∀ e ∈ large G ρt (911 / 1000 : ℝ), e.1 ≠ e.2 :=
  fun e he => ne_of_lt (large_spec G ρt _ he).1

lemma aL_eq (y : Qubits n) : aL G ρt y = (1 / 4 : ℂ) ^ (large G ρt (911 / 1000 : ℝ)).card *
    ∏ e ∈ large G ρt (911 / 1000 : ℝ), (1 - zf (y e.1) * zf (y e.2)) := by
  unfold aL; rw [Finset.prod_mul_distrib, Finset.prod_const]

open Classical in
lemma card_nonB (hρ : IsPseudoDensity 2 ρt) :
    (Finset.univ.filter (fun q => ¬ inB G ρt (911 / 1000 : ℝ) q)).card =
      2 * (large G ρt (911 / 1000 : ℝ)).card := by
  classical
  have hset : (Finset.univ.filter (fun q => ¬ inB G ρt (911 / 1000 : ℝ) q)) =
      (large G ρt (911 / 1000 : ℝ)).biUnion (fun e => {e.1, e.2}) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hq; exact not_inB_exists G ρt _ hq
    · rintro ⟨e, he, h | h⟩
      · rw [h]; exact large_not_inB1 G ρt _ he
      · rw [h]; exact large_not_inB2 G ρt _ he
  rw [hset, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun e he => Finset.card_pair (large_ne G ρt e he))]
    simp [mul_comm]
  · intro e he f hf hef
    obtain ⟨a1, a2, a3, a4⟩ := matching G ρt hρ e he f hf hef
    simp [Finset.disjoint_left, a1, a2, a3, a4]

lemma trace_density (hρ : IsPseudoDensity 2 ρt) {d : ℕ} {Ω : Type}
    (W : Fin n → EuclideanSpace ℝ (Fin d)) (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) :
    Tf (aL G ρt) (kq G ρt W R ω) (fun _ => 1) = 1 := by
  classical
  unfold Tf
  simp_rw [Matrix.mul_one, aL_eq, mul_assoc, ← Finset.mul_sum]
  rw [sum_prod_matching (large G ρt (911 / 1000 : ℝ)) (matching G ρt hρ) (large_ne G ρt)
    (fun q b => kq G ρt W R ω q b b) ?_ _ subset_rfl]
  · rw [sum_prod_eq_prod_sum (fun q b => kq G ρt W R ω q b b)]
    have : ∀ q, kq G ρt W R ω q true true + kq G ρt W R ω q false false =
        if inB G ρt (911 / 1000 : ℝ) q then 1 else 2 := by
      intro q
      by_cases hq : inB G ρt (911 / 1000 : ℝ) q
      · rw [kq_B G ρt W R ω q hq, if_pos hq, blochState_tt, blochState_ff]
        push_cast; ring
      · rw [kq_nonB G ρt W R ω q hq, if_neg hq]; simp; norm_num
    simp_rw [this]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, card_nonB G ρt hρ,
      pow_mul, ← mul_pow]
    norm_num
  · intro e he b
    rw [kq_nonB G ρt W R ω _ (large_not_inB1 G ρt _ he)]
    simp [one_apply]

end main

end QMCHalfAux

namespace QMCHalfAux
open QMCProduct.HalfApprox QAlgorithms Matrix
open scoped MatrixOrder ComplexOrder

section main2
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ρt : Op n)

noncomputable def zr (b : Bool) : ℝ := if b then -1 else 1

noncomputable def rL (y : Qubits n) : ℝ :=
  ∏ e ∈ large G ρt (911 / 1000 : ℝ), (1 / 4 : ℝ) * (1 - zr (y e.1) * zr (y e.2))

lemma aL_ofReal (y : Qubits n) : aL G ρt y = (rL G ρt y : ℂ) := by
  unfold aL rL
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  cases y e.1 <;> cases y e.2 <;> simp [zf, zr] <;> norm_num

lemma rL_nonneg (y : Qubits n) : 0 ≤ rL G ρt y := by
  unfold rL
  refine Finset.prod_nonneg (fun e _ => ?_)
  cases y e.1 <;> cases y e.2 <;> simp [zr] <;> norm_num

lemma rL_congr (y x : Qubits n) (h : ∀ q, ¬ inB G ρt (911 / 1000 : ℝ) q → y q = x q) :
    rL G ρt y = rL G ρt x := by
  unfold rL
  refine Finset.prod_congr rfl (fun e he => ?_)
  rw [h _ (large_not_inB1 G ρt _ he), h _ (large_not_inB2 G ρt _ he)]

lemma density_psd {d : ℕ} {Ω : Type}
    (W : Fin n → EuclideanSpace ℝ (Fin d)) (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) :
    (diagonal (aL G ρt) * kronAll (kq G ρt W R ω)).PosSemidef := by
  classical
  set K := kronAll (kq G ρt W R ω) with hKdef
  have hK : K.PosSemidef := by
    apply kronAll_psd
    intro q
    by_cases hq : inB G ρt (911 / 1000 : ℝ) q
    · rw [kq_B G ρt W R ω q hq]; exact blochState_psd _ (bloch_sq_le W R ω q)
    · rw [kq_nonB G ρt W R ω q hq]; exact PosSemidef.one
  set S : Op n := diagonal (fun y => ((Real.sqrt (rL G ρt y) : ℝ) : ℂ)) with hS
  have hSH : Sᴴ = S := by
    rw [hS, diagonal_conjTranspose]
    congr 1; funext y; simp
  have heq : diagonal (aL G ρt) * K = Sᴴ * K * S := by
    rw [hSH]
    ext y x
    rw [mul_diagonal, diagonal_mul, diagonal_mul]
    by_cases hKyx : K y x = 0
    · simp [hKyx]
    · have hc : ∀ q, ¬ inB G ρt (911 / 1000 : ℝ) q → y q = x q := by
        intro q hq
        by_contra hne
        apply hKyx
        rw [hKdef]
        simp only [kronAll, Matrix.of_apply]
        refine Finset.prod_eq_zero (Finset.mem_univ q) ?_
        rw [kq_nonB G ρt W R ω q hq, one_apply_ne hne]
      rw [aL_ofReal, ← rL_congr G ρt y x hc]
      have hr := Real.mul_self_sqrt (rL_nonneg G ρt y)
      have : ((Real.sqrt (rL G ρt y) : ℝ) : ℂ) * ((Real.sqrt (rL G ρt y) : ℝ) : ℂ) =
          ((rL G ρt y : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, hr]
      linear_combination (K y x) * this.symm
  rw [heq]
  exact hK.conjTranspose_mul_mul_same S

theorem alg4_density (hρ : IsPseudoDensity 2 ρt) {d : ℕ} {Ω : Type}
    (W : Fin n → EuclideanSpace ℝ (Fin d)) (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) :
    IsDensityMatrix (alg4State G ρt (911 / 1000 : ℝ) W R ω) := by
  rw [alg4State_eq]
  refine ⟨density_psd G ρt W R ω, ?_⟩
  have := trace_kron_diag_kron (fun _ => (1 : Matrix Bool Bool ℂ)) (kq G ρt W R ω) (aL G ρt)
  rw [kronAll_one, Matrix.one_mul] at this
  rw [this]
  exact trace_density G ρt hρ W R ω

end main2
end QMCHalfAux

namespace QMCHalfAux
open QMCProduct.HalfApprox QAlgorithms Matrix
open scoped MatrixOrder ComplexOrder

section main3
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ρt : Op n)

lemma prod_dz {i j : Fin n} (hij : i ≠ j) (y : Qubits n) :
    ∏ q, (fun q b => (if q = i then zf b else 1) * (if q = j then zf b else 1)) q (y q) =
      zf (y i) * zf (y j) := by
  simp only []
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp

lemma pauliX_diag (b : Bool) : pauliX b b = 0 := by simp [pauliX]
lemma pauliY_diag (b : Bool) : pauliY b b = 0 := by simp [pauliY]

lemma TX_zero {d : ℕ} {Ω : Type} (W : Fin n → EuclideanSpace ℝ (Fin d))
    (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) (i j : Fin n) (hij : i ≠ j)
    (hi : ¬ inB G ρt (911 / 1000 : ℝ) i) (A : Matrix Bool Bool ℂ) (hA : ∀ b, A b b = 0) :
    Tf (aL G ρt) (kq G ρt W R ω) (fun q => (if q = i then A else 1) * (if q = j then A else 1)) = 0 := by
  apply Tf_eq_zero _ _ _ i
  intro b
  simp [kq_nonB G ρt W R ω i hi, hij, hA]

lemma TZ_eq {d : ℕ} {Ω : Type} (W : Fin n → EuclideanSpace ℝ (Fin d))
    (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) (i j : Fin n) (hij : i ≠ j) :
    Tf (aL G ρt) (kq G ρt W R ω)
      (fun q => diagonal ((fun q b => (if q = i then zf b else 1) * (if q = j then zf b else 1)) q)) =
      ∑ y, aL G ρt y * (∏ q, kq G ρt W R ω q (y q) (y q)) * (zf (y i) * zf (y j)) := by
  rw [Tf_diag]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [prod_dz hij]

lemma T1_eq {d : ℕ} {Ω : Type} (W : Fin n → EuclideanSpace ℝ (Fin d))
    (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) :
    Tf (aL G ρt) (kq G ρt W R ω) (fun _ => 1) =
      ∑ y, aL G ρt y * (∏ q, kq G ρt W R ω q (y q) (y q)) := by
  unfold Tf; simp

theorem large_edge_energy (hρ : IsPseudoDensity 2 ρt) {d : ℕ} {Ω : Type}
    (W : Fin n → EuclideanSpace ℝ (Fin d)) (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω)
    (e : Fin n × Fin n) (he : e ∈ large G ρt (911 / 1000 : ℝ)) :
    (hQMC e.1 e.2 * alg4State G ρt (911 / 1000 : ℝ) W R ω).trace.re = 1 / 2 := by
  have hne := large_ne G ρt e he
  rw [alg4State_eq, hQMC_trace, TX_zero G ρt W R ω _ _ hne (large_not_inB1 G ρt _ he) _ pauliX_diag,
    TX_zero G ρt W R ω _ _ hne (large_not_inB1 G ρt _ he) _ pauliY_diag, TZ_eq G ρt W R ω _ _ hne]
  have h1 := trace_density G ρt hρ W R ω
  rw [T1_eq] at h1
  have hZ : ∑ y, aL G ρt y * (∏ q, kq G ρt W R ω q (y q) (y q)) * (zf (y e.1) * zf (y e.2)) =
      - ∑ y, aL G ρt y * (∏ q, kq G ρt W R ω q (y q) (y q)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have ha : aL G ρt y * (zf (y e.1) * zf (y e.2)) = - aL G ρt y := by
      unfold aL
      rw [← Finset.mul_prod_erase _ _ he]
      have hu : (zf (y e.1) * zf (y e.2)) * (zf (y e.1) * zf (y e.2)) = 1 := by
        have := zf_sq (y e.1); have := zf_sq (y e.2)
        linear_combination (zf (y e.2) * zf (y e.2)) * zf_sq (y e.1) + zf_sq (y e.2)
      linear_combination (-(1/4 : ℂ) * ∏ x ∈ (large G ρt (911 / 1000 : ℝ)).erase e,
        (1 / 4 : ℂ) * (1 - zf (y x.1) * zf (y x.2))) * hu
    linear_combination (∏ q, kq G ρt W R ω q (y q) (y q)) * ha
  rw [hZ, h1, trace_density G ρt hρ W R ω]
  norm_num

/-- the double flip at `i` and `k` -/
def flip2 {n : ℕ} (i k : Fin n) : Equiv.Perm (Qubits n) := (flipAt k).trans (flipAt i)

lemma flip2_apply {n : ℕ} (i k : Fin n) (hik : i ≠ k) (y : Qubits n) (q : Fin n) :
    flip2 i k y q = if q = i ∨ q = k then !y q else y q := by
  simp only [flip2, Equiv.trans_apply]
  by_cases hi : q = i
  · subst hi; rw [flipAt_apply_self, flipAt_apply_ne _ _ hik]; simp
  · rw [flipAt_apply_ne _ _ hi]
    by_cases hk : q = k
    · subst hk; rw [flipAt_apply_self]; simp
    · rw [flipAt_apply_ne _ _ hk]; simp [hi, hk]

theorem deltaL_trace (hρ : IsPseudoDensity 2 ρt) {d : ℕ} {Ω : Type}
    (W : Fin n → EuclideanSpace ℝ (Fin d)) (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : inLarge G ρt (911 / 1000 : ℝ) i k) :
    (hQMC i j * alg4State G ρt (911 / 1000 : ℝ) W R ω).trace.re = 1 / 4 := by
  obtain ⟨e, he, hek⟩ := hik
  have hne := large_ne G ρt e he
  have hiB : ¬ inB G ρt (911 / 1000 : ℝ) i := by
    rcases hek with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [← h1]; exact large_not_inB1 G ρt _ he
    · rw [← h2]; exact large_not_inB2 G ρt _ he
  have hkB : ¬ inB G ρt (911 / 1000 : ℝ) k := by
    rcases hek with ⟨-, h2⟩ | ⟨h1, -⟩
    · rw [← h2]; exact large_not_inB2 G ρt _ he
    · rw [← h1]; exact large_not_inB1 G ρt _ he
  have hik' : i ≠ k := by
    rcases hek with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hne
    · rw [← h1, ← h2]; exact hne.symm
  have hcov : ∀ q, (q = e.1 ∨ q = e.2) ↔ (q = i ∨ q = k) := by
    intro q
    rcases hek with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]; tauto
  rw [alg4State_eq, hQMC_trace, TX_zero G ρt W R ω _ _ hij hiB _ pauliX_diag,
    TX_zero G ρt W R ω _ _ hij hiB _ pauliY_diag, TZ_eq G ρt W R ω _ _ hij]
  have h1 := trace_density G ρt hρ W R ω
  rw [T1_eq] at h1
  have hZ : ∑ y, aL G ρt y * (∏ q, kq G ρt W R ω q (y q) (y q)) * (zf (y i) * zf (y j)) = 0 := by
    apply sum_eq_zero_of_antiinv (flip2 i k)
    intro y
    have hA : aL G ρt (flip2 i k y) = aL G ρt y := by
      unfold aL
      refine Finset.prod_congr rfl (fun f hf => ?_)
      rw [flip2_apply i k hik', flip2_apply i k hik']
      by_cases hfe : f = e
      · subst hfe
        rw [if_pos ((hcov _).1 (Or.inl rfl)), if_pos ((hcov _).1 (Or.inr rfl)), zf_not, zf_not]
        ring
      · obtain ⟨a1, a2, a3, a4⟩ := matching G ρt hρ e he f hf (Ne.symm hfe)
        have n1 : ¬ (f.1 = i ∨ f.1 = k) := by
          rw [← hcov]; rintro (h | h)
          · exact a1 h.symm
          · exact a3 h.symm
        have n2 : ¬ (f.2 = i ∨ f.2 = k) := by
          rw [← hcov]; rintro (h | h)
          · exact a2 h.symm
          · exact a4 h.symm
        rw [if_neg n1, if_neg n2]
    have hC : ∏ q, kq G ρt W R ω q (flip2 i k y q) (flip2 i k y q) =
        ∏ q, kq G ρt W R ω q (y q) (y q) := by
      refine Finset.prod_congr rfl (fun q _ => ?_)
      rw [flip2_apply i k hik']
      by_cases hq : q = i ∨ q = k
      · rw [if_pos hq]
        have hqB : ¬ inB G ρt (911 / 1000 : ℝ) q := by
          rcases hq with h | h <;> (subst h; assumption)
        rw [kq_nonB G ρt W R ω q hqB]; simp
      · rw [if_neg hq]
    have hzi : zf (flip2 i k y i) = - zf (y i) := by
      rw [flip2_apply i k hik', if_pos (Or.inl rfl), zf_not]
    have hzj : zf (flip2 i k y j) = zf (y j) := by
      rw [flip2_apply i k hik', if_neg (by rintro (h | h); exact hij h.symm; exact hjk h)]
    rw [hA, hC, hzi, hzj]; ring
  rw [hZ, trace_density G ρt hρ W R ω]
  norm_num

end main3
end QMCHalfAux

namespace QMCHalfAux
open QMCProduct.HalfApprox QAlgorithms Matrix

lemma mu_eq_v {n : ℕ} (ρt : Op n) (i j : Fin n) : mu ρt i j = (1 + 3 * v ρt i j) / 4 := by
  unfold mu v; ring

theorem deltaL_full {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ρt : Op n) (hρ : IsPseudoDensity 2 ρt)
    (W : Fin n → EuclideanSpace ℝ (Fin d)) (hW : IsRoundingInput ρt W)
    {Ω : Type} (R : Fin 3 → Fin d → Ω → ℝ)
    (i j k : Fin n) (hij : G.Adj i j) (hjk : j ≠ k)
    (hik : inLarge G ρt (911 / 1000 : ℝ) i k) :
    (∀ ω, (hQMC i j * alg4State G ρt (911 / 1000 : ℝ) W R ω).trace.re = 1 / 4) ∧
      (1 / 2 : ℝ) * mu ρt i j < 1 / 4 := by
  have hij' : i ≠ j := G.ne_of_adj hij
  refine ⟨fun ω => deltaL_trace G ρt hρ W R ω i j k hij' hjk hik, ?_⟩
  obtain ⟨e, he, hek⟩ := hik
  have hne := large_ne G ρt e he
  obtain ⟨-, -, hv⟩ := large_spec G ρt _ he
  have hik' : i ≠ k := by
    rcases hek with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hne
    · rw [← h1, ← h2]; exact hne.symm
  have hvik : (911 / 1000 : ℝ) < v ρt i k := by
    rcases hek with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hv; exact hv
    · rw [h1, h2, v_symm] at hv; exact hv
  have := fact_2 ρt hρ i k j hik' hij' hjk.symm hvik
  rw [mu_eq_v]; linarith

end QMCHalfAux

namespace QMCHalfAux
open QMCProduct.HalfApprox QAlgorithms Matrix MeasureTheory

noncomputable def bs (t : Fin 3 → ℝ) : Matrix Bool Bool ℂ :=
  (1 / 2 : ℂ) • (1 + (t 0 : ℂ) • pauliX + (t 1 : ℂ) • pauliY + (t 2 : ℂ) • pauliZ)

lemma continuous_kronAll {X : Type*} [TopologicalSpace X] {n : ℕ}
    (F : X → Fin n → Matrix Bool Bool ℂ) (hF : ∀ q, Continuous fun x => F x q) :
    Continuous fun x => kronAll (F x) := by
  unfold kronAll
  refine Continuous.matrixOf ?_
  refine continuous_pi fun y => continuous_pi fun z => ?_
  exact continuous_finsetProd _ fun q _ => (hF q).matrix_elem _ _

lemma continuous_bs : Continuous bs := by
  unfold bs; fun_prop

section integ
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ρt : Op n)

noncomputable def kqt (t : Fin n → Fin 3 → ℝ) : Fin n → Matrix Bool Bool ℂ := by
  classical
  exact fun i => if inB G ρt (911 / 1000 : ℝ) i then bs (t i) else 1

noncomputable def thetaOf {d : ℕ} {Ω : Type} (W : Fin n → EuclideanSpace ℝ (Fin d))
    (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) : Fin n → Fin 3 → ℝ :=
  fun q a => bloch W R ω q a

lemma kq_eq_kqt {d : ℕ} {Ω : Type} (W : Fin n → EuclideanSpace ℝ (Fin d))
    (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) :
    kq G ρt W R ω = kqt G ρt (thetaOf W R ω) := rfl

lemma continuous_kqt (A : Op n) :
    Continuous fun t => (A * (diagonal (aL G ρt) * kronAll (kqt G ρt t))).trace.re := by
  classical
  have hk : Continuous fun t => kronAll (kqt G ρt t) := by
    apply continuous_kronAll
    intro q
    unfold kqt
    by_cases hq : inB G ρt (911 / 1000 : ℝ) q
    · simp only [hq, if_true]
      exact continuous_bs.comp (continuous_apply q)
    · simp only [hq, if_false]; exact continuous_const
  fun_prop

lemma measurable_thetaOf {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : Fin n → EuclideanSpace ℝ (Fin d))
    (R : Fin 3 → Fin d → Ω → ℝ) (hR : IsStdGaussianMatrix P R) :
    Measurable (thetaOf W R) := by
  have hRm : ∀ a c, Measurable (R a c) := by
    intro a c
    have := hR.1 (finProdFinEquiv (a, c))
    simpa using this
  have hg : ∀ q a, Measurable fun ω => (gaussianProject R ω (W q)) a := by
    intro q a
    simp only [gaussianProject]
    exact Finset.measurable_sum _ fun c _ => (hRm a c).mul_const _
  refine measurable_pi_lambda _ fun q => measurable_pi_lambda _ fun a => ?_
  simp only [thetaOf, bloch, unitVec, PiLp.smul_apply, smul_eq_mul]
  refine Measurable.mul ?_ (hg q a)
  refine Measurable.inv ?_
  simp_rw [EuclideanSpace.norm_eq]
  refine Measurable.sqrt ?_
  exact Finset.measurable_sum _ fun b _ => ((hg q b).norm).pow_const _

end integ
end QMCHalfAux

namespace QMCHalfAux
open QMCProduct.HalfApprox QAlgorithms Matrix MeasureTheory

lemma abs_le_one_of_sq {a b c : ℝ} (h : a ^ 2 + b ^ 2 + c ^ 2 ≤ 1) : |a| ≤ 1 := by
  rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg b, sq_nonneg c]

lemma blochState_entry_le (θ : EuclideanSpace ℝ (Fin 3)) (hθ : θ 0 ^ 2 + θ 1 ^ 2 + θ 2 ^ 2 ≤ 1)
    (a b : Bool) : ‖blochState θ a b‖ ≤ 1 := by
  have h0 : |θ 0| ≤ 1 := abs_le_one_of_sq hθ
  have h1 : |θ 1| ≤ 1 := abs_le_one_of_sq (b := θ 0) (c := θ 2) (by linarith)
  have h2 : |θ 2| ≤ 1 := abs_le_one_of_sq (b := θ 0) (c := θ 1) (by linarith)
  have hb0 := abs_le.mp h0; have hb1 := abs_le.mp h1; have hb2 := abs_le.mp h2
  refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
  cases a <;> cases b
  · rw [blochState_ff]; simp
    rw [abs_le]; constructor <;> linarith
  · rw [blochState_ft]; simp
    rw [abs_div, abs_div, abs_neg]; norm_num
    linarith
  · rw [blochState_tf]; simp
    rw [abs_div, abs_div]; norm_num
    linarith
  · rw [blochState_tt]; simp
    rw [abs_le]; constructor <;> linarith

lemma trace_bound {N : Type*} [Fintype N] [DecidableEq N] (A D K : Matrix N N ℂ)
    (hK : ∀ x y, ‖K x y‖ ≤ 1) :
    ‖(A * (D * K)).trace‖ ≤ ∑ y, ∑ z, ‖A y z‖ * ∑ x, ‖D z x‖ := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun y _ => ?_)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun z _ => ?_)
  rw [norm_mul]
  gcongr
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun x _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hK _ _)

section integ2
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ρt : Op n)

lemma kronAll_kq_le {d : ℕ} {Ω : Type} (W : Fin n → EuclideanSpace ℝ (Fin d))
    (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) (x y : Qubits n) :
    ‖kronAll (kq G ρt W R ω) x y‖ ≤ 1 := by
  classical
  simp only [kronAll, Matrix.of_apply, norm_prod]
  refine Finset.prod_le_one (fun q _ => norm_nonneg _) (fun q _ => ?_)
  by_cases hq : inB G ρt (911 / 1000 : ℝ) q
  · rw [kq_B G ρt W R ω q hq]; exact blochState_entry_le _ (bloch_sq_le W R ω q) _ _
  · rw [kq_nonB G ρt W R ω q hq]
    by_cases h : x q = y q
    · rw [h, one_apply_eq]; simp
    · rw [one_apply_ne h]; simp

theorem integrable_trace {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (W : Fin n → EuclideanSpace ℝ (Fin d))
    (R : Fin 3 → Fin d → Ω → ℝ) (hR : IsStdGaussianMatrix P R) (A : Op n) :
    Integrable (fun ω => (A * alg4State G ρt (911 / 1000 : ℝ) W R ω).trace.re) P := by
  have hfun : (fun ω => (A * alg4State G ρt (911 / 1000 : ℝ) W R ω).trace.re) =
      (fun t => (A * (diagonal (aL G ρt) * kronAll (kqt G ρt t))).trace.re) ∘ thetaOf W R := by
    funext ω
    simp only [Function.comp_apply, alg4State_eq, kq_eq_kqt]
  refine Integrable.of_bound (C := ∑ y, ∑ z, ‖A y z‖ * ∑ x, ‖(diagonal (aL G ρt)) z x‖) ?_ ?_
  · rw [hfun]
    exact ((continuous_kqt G ρt A).measurable.comp (measurable_thetaOf P W R hR)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, alg4State_eq]
    exact le_trans (Complex.abs_re_le_norm _) (trace_bound _ _ _ (kronAll_kq_le G ρt W R ω))

end integ2
end QMCHalfAux

namespace QMCHalfAux
open QMCProduct.HalfApprox QAlgorithms Matrix MeasureTheory

lemma onSite_conjTranspose {n : ℕ} (i : Fin n) (A : Matrix Bool Bool ℂ) :
    (onSite i A)ᴴ = onSite i Aᴴ := by
  rw [onSite_eq, onSite_eq, kronAll_conjTranspose]
  congr 1; funext q; split_ifs <;> simp

lemma pair_herm {n : ℕ} (i j : Fin n) (A : Matrix Bool Bool ℂ) (hA : Aᴴ = A) :
    (onSite i A * onSite j A)ᴴ = onSite i A * onSite j A := by
  rw [conjTranspose_mul, onSite_conjTranspose, onSite_conjTranspose, hA]
  by_cases h : i = j
  · subst h; rfl
  · rw [onSite_comm j i (Ne.symm h)]

lemma pauliX_herm : pauliXᴴ = pauliX := by
  ext a b; cases a <;> cases b <;> simp [pauliX, conjTranspose_apply]
lemma pauliY_herm : pauliYᴴ = pauliY := by
  ext a b; cases a <;> cases b <;> simp [pauliY, conjTranspose_apply]
lemma pauliZ_herm : pauliZᴴ = pauliZ := by
  ext a b; cases a <;> cases b <;> simp [pauliZ, conjTranspose_apply]

lemma hQMC_herm {n : ℕ} (i j : Fin n) : (hQMC i j)ᴴ = hQMC i j := by
  unfold hQMC X Y Z
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_sub, conjTranspose_sub,
    conjTranspose_one, pair_herm _ _ _ pauliX_herm, pair_herm _ _ _ pauliY_herm,
    pair_herm _ _ _ pauliZ_herm]
  congr 1; simp

lemma qmcH_herm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Fin n → Fin n → ℝ) :
    (qmcHamiltonian G w).IsHermitian := by
  unfold qmcHamiltonian IsHermitian
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [conjTranspose_smul, hQMC_herm]
  simp

lemma trace_qmcH {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Fin n → Fin n → ℝ)
    (M : Op n) :
    (qmcHamiltonian G w * M).trace.re = ∑ e ∈ edges G, w e.1 e.2 * (hQMC e.1 e.2 * M).trace.re := by
  unfold qmcHamiltonian
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

lemma trace_hQMC_rho {n : ℕ} (ρt : Op n) (hρ : IsPseudoDensity 2 ρt) (i j : Fin n) :
    (hQMC i j * ρt).trace.re = mu ρt i j := by
  unfold hQMC mu val
  rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.sub_mul, Matrix.sub_mul, Matrix.sub_mul,
    Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.one_mul, hρ.2.1,
    Matrix.trace_mul_comm (X i * X j), Matrix.trace_mul_comm (Y i * Y j),
    Matrix.trace_mul_comm (Z i * Z j)]
  simp only [smul_eq_mul, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im,
    Complex.one_im]
  norm_num
  ring

end QMCHalfAux

namespace QMCHalfAux
open QMCProduct.HalfApprox QAlgorithms Matrix MeasureTheory

theorem edge_bound {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ρt : Op n) (hρ : IsPseudoDensity 2 ρt)
    (W : Fin n → EuclideanSpace ℝ (Fin d)) (hW : IsRoundingInput ρt W)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Fin 3 → Fin d → Ω → ℝ) (hR : IsStdGaussianMatrix P R)
    (e : Fin n × Fin n) (he : e ∈ edges G) :
    (1 / 2 : ℝ) * mu ρt e.1 e.2 ≤
      ∫ ω, (hQMC e.1 e.2 * alg4State G ρt (911 / 1000 : ℝ) W R ω).trace.re ∂P := by
  classical
  have hE : e.1 < e.2 ∧ G.Adj e.1 e.2 := by
    simpa [edges] using he
  have hadj := hE.2
  have hne : e.1 ≠ e.2 := ne_of_lt hE.1
  by_cases hL : e ∈ large G ρt (911 / 1000 : ℝ)
  · have h := fun ω => large_edge_energy G ρt hρ W R ω e hL
    simp_rw [h]
    rw [integral_const]; simp
    have := (lemma_5 (le_refl 2) ρt hρ e.1 e.2 hne).1.2
    linarith
  · by_cases hB : inB G ρt (911 / 1000 : ℝ) e.1 ∧ inB G ρt (911 / 1000 : ℝ) e.2
    · exact fact_1 G ρt hρ W hW P R hR e.1 e.2 hadj hB.1 hB.2
    · have hvL : ¬ (911 / 1000 : ℝ) < v ρt e.1 e.2 := by
        intro hv; exact hL (by
          simp only [large, Finset.mem_filter]; exact ⟨he, hv⟩)
      rcases not_and_or.mp hB with h1 | h2
      · unfold inB at h1; push Not at h1
        obtain ⟨k, hk, hvk⟩ := h1
        have hk2 : e.2 ≠ k := by
          rintro rfl; exact hvL hvk
        obtain ⟨hc, hlt⟩ := deltaL_edge G ρt hρ W hW R e.1 e.2 k hadj hk2
          (exists_large_of_adj G ρt _ hk hvk)
        simp_rw [hc]
        rw [integral_const]; simp; linarith
      · unfold inB at h2; push Not at h2
        obtain ⟨k, hk, hvk⟩ := h2
        have hk1 : e.1 ≠ k := by
          rintro rfl; rw [v_symm] at hvk; exact hvL hvk
        obtain ⟨hc, hlt⟩ := deltaL_edge G ρt hρ W hW R e.2 e.1 k hadj.symm hk1
          (exists_large_of_adj G ρt _ hk hvk)
        rw [hQMC_symm] at hc
        rw [mu_symm] at hlt
        simp_rw [hc]
        rw [integral_const]; simp; linarith

theorem main_theorem : ∃ γ : ℝ, -(1 / 3 : ℝ) < γ ∧ γ ≤ 1 ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (w : Fin n → Fin n → ℝ),
      (∀ e ∈ edges G, 0 ≤ w e.1 e.2) →
      ∀ ρt : Op n, IsOptimalL2 (qmcHamiltonian G w) ρt →
      ∀ (d : ℕ) (W : Fin n → EuclideanSpace ℝ (Fin d)),
        IsRoundingInput ρt W →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (R : Fin 3 → Fin d → Ω → ℝ),
        IsStdGaussianMatrix P R →
        (∀ ω, QAlgorithms.IsDensityMatrix (alg4State G ρt γ W R ω)) ∧
        ∀ σ : Op n, QAlgorithms.IsDensityMatrix σ →
          (1 / 2 : ℝ) * (qmcHamiltonian G w * σ).trace.re ≤
            ∫ ω, (qmcHamiltonian G w * alg4State G ρt γ W R ω).trace.re ∂P := by
  refine ⟨911 / 1000, by norm_num, by norm_num, ?_⟩
  intro n G _ w hw ρt hopt d W hW Ω _ P _ R hR
  have hρ : IsPseudoDensity 2 ρt := hopt.1
  refine ⟨fun ω => alg4_density G ρt hρ W R ω, ?_⟩
  intro σ hσ
  have h9 := lemma_9 2 (qmcHamiltonian G w) (qmcH_herm G w) ρt hopt σ hσ
  simp_rw [trace_qmcH G w]
  rw [trace_qmcH G w σ, trace_qmcH G w ρt] at h9
  rw [integral_finsetSum _ (fun e _ => (integrable_trace G ρt P W R hR _).const_mul _)]
  simp_rw [integral_const_mul]
  have hstep : ∑ e ∈ edges G, w e.1 e.2 * (hQMC e.1 e.2 * ρt).trace.re ≤
      2 * ∑ e ∈ edges G, w e.1 e.2 *
        ∫ ω, (hQMC e.1 e.2 * alg4State G ρt (911 / 1000 : ℝ) W R ω).trace.re ∂P := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun e he => ?_)
    rw [trace_hQMC_rho ρt hρ]
    have := edge_bound G ρt hρ W hW P R hR e he
    have hw0 := hw e he
    nlinarith
  linarith

end QMCHalfAux

open QMCProduct.HalfApprox MeasureTheory in
theorem solution : ∃ γ : ℝ, -(1 / 3 : ℝ) < γ ∧ γ ≤ 1 ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (w : Fin n → Fin n → ℝ),
      (∀ e ∈ edges G, 0 ≤ w e.1 e.2) →
      ∀ ρt : Op n, IsOptimalL2 (qmcHamiltonian G w) ρt →
      ∀ (d : ℕ) (W : Fin n → EuclideanSpace ℝ (Fin d)),
        IsRoundingInput ρt W →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (R : Fin 3 → Fin d → Ω → ℝ),
        IsStdGaussianMatrix P R →
        (∀ ω, QAlgorithms.IsDensityMatrix (alg4State G ρt γ W R ω)) ∧
        ∀ σ : Op n, QAlgorithms.IsDensityMatrix σ →
          (1 / 2 : ℝ) * (qmcHamiltonian G w * σ).trace.re ≤
            ∫ ω, (qmcHamiltonian G w * alg4State G ρt γ W R ω).trace.re ∂P :=
  QMCHalfAux.main_theorem
