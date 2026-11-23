-- Prove2me | solution 1 for OptimalTraceDistance.Estimation.proposition_4_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T05:30:50.886192+00:00
-- url     : https://prove2.me/submissions/894d38a5-d851-4398-9062-cd1cd58f2b47
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OptimalTraceDistance_Estimation_proposition_4_3
import Theorems.Thm_OptimalTraceDistance_Estimation_proposition_2_6
import Theorems.Thm_OptimalTraceDistance_Estimation_proposition_2_1

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder Nat
noncomputable section

namespace OTDRoot
open Matrix OptimalTraceDistance.Estimation

variable {d : ℕ}

/-- quadratic form of a conjugated matrix -/
lemma quad_conj (U : Mat d) (B : Mat d) (x : Fin d → ℂ) :
    star x ⬝ᵥ ((U * B * star U) *ᵥ x) = star (star U *ᵥ x) ⬝ᵥ (B *ᵥ (star U *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
  simp [Matrix.star_eq_conjTranspose]

lemma quad_diag (w : Fin d → ℂ) (y : Fin d → ℂ) :
    star y ⬝ᵥ (diagonal w *ᵥ y) = ∑ i, w i * (star (y i) * y i) := by
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl (fun i _ => by ring)

lemma quad_cfc {A : Mat d} (hA : A.IsHermitian) (f : ℝ → ℝ) (x : Fin d → ℂ) :
    star x ⬝ᵥ (cfc f A *ᵥ x) =
      ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) *
        (star ((star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i) *
          ((star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i)) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, quad_conj, quad_diag]
  rfl

lemma unitary_norm (U : Mat d) (hU : U ∈ unitary (Mat d)) (x : Fin d → ℂ) :
    star (star U *ᵥ x) ⬝ᵥ (star U *ᵥ x) = star x ⬝ᵥ x := by
  have := quad_conj U 1 x
  rw [mul_one, Unitary.mul_star_self_of_mem hU, one_mulVec, one_mulVec] at this
  exact this.symm

lemma sum_normsq (y : Fin d → ℂ) : star y ⬝ᵥ y = ∑ i, ((‖y i‖^2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm]
  show y i * (starRingEnd ℂ) (y i) = _
  rw [Complex.mul_conj', Complex.ofReal_pow]


lemma inner_eq (A : Mat d) (x : EuclideanSpace ℂ (Fin d)) :
    RCLike.re (inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) A x) x) =
      (star (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x)).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM]
  simp only [dotProduct, Pi.star_apply, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma normsq_eq (x : EuclideanSpace ℂ (Fin d)) :
    ‖x‖^2 = (star (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp x)).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

lemma opNorm_le_of_quad {A : Mat d} (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : Fin d → ℂ, |(star x ⬝ᵥ (A *ᵥ x)).re| ≤ c * (star x ⬝ᵥ x).re) :
    opNorm A ≤ c := by
  unfold opNorm
  have hT : (Matrix.toEuclideanCLM (𝕜 := ℂ) A : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] _).IsSymmetric := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hT]
  refine ciSup_le (fun x => ?_)
  simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf]
  rw [inner_eq, normsq_eq]
  rcases eq_or_lt_of_le (sq_nonneg ‖x‖) with h0 | hpos
  · rw [normsq_eq] at h0; rw [← h0]; simp [hc]
  · rw [normsq_eq] at hpos
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact h _

lemma quad_le_opNorm (A : Mat d) (x : Fin d → ℂ) :
    |(star x ⬝ᵥ (A *ᵥ x)).re| ≤ opNorm A * (star x ⬝ᵥ x).re := by
  have := ContinuousLinearMap.rayleighQuotient_le_norm (Matrix.toEuclideanCLM (𝕜 := ℂ) A)
    (WithLp.toLp 2 x)
  simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf] at this
  rw [inner_eq, normsq_eq] at this
  simp only [WithLp.ofLp_toLp] at this
  rcases eq_or_lt_of_le (show 0 ≤ (star x ⬝ᵥ x).re from by
      rw [sum_normsq]; simp only [Complex.re_sum, Complex.ofReal_re]; positivity) with h0 | hpos
  · have hx : x = 0 := by
      have := (h0.symm)
      rw [sum_normsq] at this
      simp only [Complex.re_sum, Complex.ofReal_re] at this
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖x i‖)).mp this
      funext i; have := h2 i (Finset.mem_univ i); simpa using this
    subst hx; simp
  · rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos] at this
    exact this


section spectral
variable {A : Mat d} (hA : A.IsHermitian)
include hA

lemma U_mem : (hA.eigenvectorUnitary : Mat d) ∈ unitary (Mat d) := (hA.eigenvectorUnitary).2

lemma cfc_explicit (f : ℝ → ℝ) : cfc f A =
    (hA.eigenvectorUnitary : Mat d) * diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Mat d) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]; rfl

lemma cfc_mul' (f g : ℝ → ℝ) : cfc f A * cfc g A = cfc (fun t => f t * g t) A := by
  rw [cfc_explicit hA, cfc_explicit hA, cfc_explicit hA]
  set U := (hA.eigenvectorUnitary : Mat d)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (U_mem hA)
  calc U * diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) * star U *
        (U * diagonal (fun i => ((g (hA.eigenvalues i) : ℝ) : ℂ)) * star U)
      = U * diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) * (star U * U) *
          diagonal (fun i => ((g (hA.eigenvalues i) : ℝ) : ℂ)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]; push_cast; rfl

lemma cfc_congr' {f g : ℝ → ℝ} (h : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) :
    cfc f A = cfc g A := by
  rw [cfc_explicit hA, cfc_explicit hA]; simp only [h]

lemma cfc_one' : cfc (fun _ => (1:ℝ)) A = 1 := by
  rw [cfc_explicit hA]; simp only [Complex.ofReal_one]
  rw [diagonal_one, Matrix.mul_one, Unitary.mul_star_self_of_mem (U_mem hA)]

lemma cfc_id'' : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A hA.isSelfAdjoint

lemma cfc_herm (f : ℝ → ℝ) : (cfc f A).IsHermitian := by
  rw [cfc_explicit hA]
  exact isHermitian_mul_mul_conjTranspose _
    (isHermitian_diagonal_of_self_adjoint _ (funext fun i => by simp [Complex.conj_ofReal]))

lemma trace_cfc (f : ℝ → ℝ) : (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [cfc_explicit hA, Matrix.trace_mul_cycle, Unitary.star_mul_self_of_mem (U_mem hA),
    Matrix.one_mul, trace_diagonal]

lemma quad_re (f : ℝ → ℝ) (x : Fin d → ℂ) :
    (star x ⬝ᵥ (cfc f A *ᵥ x)).re =
      ∑ i, f (hA.eigenvalues i) * ‖(star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i‖^2 := by
  rw [quad_cfc hA, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm (star _), show star ((star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i) =
    (starRingEnd ℂ) ((star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i) from rfl, Complex.mul_conj',
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

lemma quad_re_self (x : Fin d → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re =
      ∑ i, hA.eigenvalues i * ‖(star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i‖^2 := by
  conv_lhs => rw [← cfc_id'' hA]
  exact quad_re hA _ x

lemma sum_normsq_U (x : Fin d → ℂ) :
    ∑ i, ‖(star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i‖^2 = (star x ⬝ᵥ x).re := by
  rw [← unitary_norm _ (U_mem hA) x, sum_normsq, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.ofReal_re]

end spectral

lemma normsq_nonneg (x : Fin d → ℂ) : 0 ≤ (star x ⬝ᵥ x).re := by
  rw [sum_normsq, Complex.re_sum]; simp only [Complex.ofReal_re]; positivity


lemma trace_cfc_sq {A : Mat d} (hA : A.IsHermitian) (h : ℝ → ℝ) :
    (cfc h (Aᴴ * A)).trace.re = ∑ i, h (hA.eigenvalues i ^ 2) := by
  have e : Aᴴ * A = cfc (fun t : ℝ => t * t) A := by
    rw [hA.eq, ← cfc_mul' hA, cfc_id'' hA]
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  rw [e, ← cfc_comp h (fun t : ℝ => t * t) A hA.isSelfAdjoint
    ((hfin.image _).continuousOn _) (hfin.continuousOn _), trace_cfc hA, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [sq]

lemma mulVec_col (A B : Mat d) (k j : Fin d) : (A *ᵥ fun i => B i k) j = (A * B) j k := by
  simp [mulVec, dotProduct, mul_apply]

lemma col_normsq (B : Mat d) (k : Fin d) :
    star (fun i => B i k) ⬝ᵥ (fun i => B i k) = (star B * B) k k := by
  simp [dotProduct, mul_apply, Matrix.star_eq_conjTranspose]


lemma quad_sub (A B : Mat d) (x : Fin d → ℂ) :
    star x ⬝ᵥ ((A - B) *ᵥ x) = star x ⬝ᵥ (A *ᵥ x) - star x ⬝ᵥ (B *ᵥ x) := by
  rw [sub_mulVec, dotProduct_sub]

lemma quad_add (A B : Mat d) (x : Fin d → ℂ) :
    star x ⬝ᵥ ((A + B) *ᵥ x) = star x ⬝ᵥ (A *ᵥ x) + star x ⬝ᵥ (B *ᵥ x) := by
  rw [add_mulVec, dotProduct_add]

lemma re_nonneg_of_psd {A : Mat d} (hA : A.PosSemidef) (x : Fin d → ℂ) :
    0 ≤ (star x ⬝ᵥ (A *ᵥ x)).re := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg x)).1

/-! ### zero-copy measurement -/

def zeroOp (d : ℕ) (B : Set ℝ) : Matrix (Register d 0 × Register d 0) (Register d 0 × Register d 0) ℂ :=
  if (0:ℝ) ∈ B then 1 else 0

def zeroPOVM (d : ℕ) : TwoStateMeasurement d 0 where
  operator := zeroOp d
  empty := by simp [zeroOp]
  total := by simp [zeroOp]
  positive := fun B _ => by
    unfold zeroOp; split_ifs
    · exact PosSemidef.one
    · exact PosSemidef.zero
  additive := by
    intro B _ hd
    by_cases h : (0:ℝ) ∈ ⋃ i, B i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
      have : (fun j => zeroOp d (B j)) = fun j => if j = i then 1 else 0 := by
        funext j; unfold zeroOp
        by_cases hj : j = i
        · subst hj; simp [hi]
        · have : (0:ℝ) ∉ B j := fun h' => (Set.disjoint_left.mp (hd hj)) h' hi
          simp [this, hj]
      rw [this]
      have := hasSum_ite_eq i (1 : Matrix (Register d 0 × Register d 0) (Register d 0 × Register d 0) ℂ)
      simpa [zeroOp, h] using this
    · have h' : ∀ j, (0:ℝ) ∉ B j := fun j hj => h (Set.mem_iUnion.mpr ⟨j, hj⟩)
      simp only [zeroOp, h', h, if_false]
      exact hasSum_zero

lemma law_zero {d : ℕ} (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ) :
    outcomeLaw (zeroPOVM d) ρ σ hρ hσ = Measure.dirac 0 := by
  ext B hB
  rw [outcomeLaw, QAlgorithms.Measurements.bornLaw_apply _ _ _ B hB, Measure.dirac_apply' _ hB]
  have ht := (jointInput_density 0 ρ σ hρ hσ).2
  show ENNReal.ofReal (QAlgorithms.effectProb (zeroOp d B) (jointInput 0 ρ σ)) = _
  unfold zeroOp QAlgorithms.effectProb
  by_cases h : (0:ℝ) ∈ B
  · simp [h, ht]
  · simp [h]

/-! ### distance bounds -/

lemma traceNorm_eq {A : Mat d} (hA : A.IsHermitian) :
    QAlgorithms.traceNorm A = ∑ i, |hA.eigenvalues i| := by
  unfold QAlgorithms.traceNorm
  rw [trace_cfc_sq hA]
  simp only [Real.sqrt_sq_eq_abs]

lemma eig_quad {A : Mat d} (hA : A.IsHermitian) (k : Fin d) :
    (star (fun i => (hA.eigenvectorUnitary : Mat d) i k) ⬝ᵥ
      (A *ᵥ (fun i => (hA.eigenvectorUnitary : Mat d) i k))).re = hA.eigenvalues k := by
  have hVV : star (hA.eigenvectorUnitary : Mat d) * (hA.eigenvectorUnitary : Mat d) = 1 :=
    Unitary.star_mul_self_of_mem (U_mem hA)
  rw [quad_re_self hA]
  simp only [mulVec_col]
  rw [hVV, Finset.sum_eq_single k]
  · simp
  · intro i _ hi; simp [one_apply_ne hi]
  · simp

lemma col_quad_eq (V A : Mat d) (k : Fin d) :
    star (fun i => V i k) ⬝ᵥ (A *ᵥ (fun i => V i k)) = (star V * A * V) k k := by
  simp [dotProduct, mulVec, mul_apply, Matrix.star_eq_conjTranspose, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma sum_col_quad {ρ : Mat d} (V : Mat d) (hV : V * star V = 1) :
    ∑ k, (star (fun i => V i k) ⬝ᵥ (ρ *ᵥ (fun i => V i k))) = ρ.trace := by
  simp only [col_quad_eq]
  rw [show (∑ k, (star V * ρ * V) k k) = (star V * ρ * V).trace from rfl, Matrix.trace_mul_cycle,
    hV, Matrix.one_mul]

lemma traceNorm_sub_le {ρ σ : Mat d} (hρ : Density ρ) (hσ : Density σ) :
    QAlgorithms.traceNorm (ρ - σ) ≤ 2 := by
  have hH : (ρ - σ).IsHermitian := hρ.1.1.sub hσ.1.1
  rw [traceNorm_eq hH]
  set V := (hH.eigenvectorUnitary : Mat d)
  have hV : V * star V = 1 := Unitary.mul_star_self_of_mem (U_mem hH)
  have hk : ∀ k, |hH.eigenvalues k| ≤ (star (fun i => V i k) ⬝ᵥ (ρ *ᵥ (fun i => V i k))).re +
      (star (fun i => V i k) ⬝ᵥ (σ *ᵥ (fun i => V i k))).re := by
    intro k
    rw [← eig_quad hH k, quad_sub, Complex.sub_re]
    have a := re_nonneg_of_psd hρ.1 (fun i => V i k)
    have b := re_nonneg_of_psd hσ.1 (fun i => V i k)
    rw [abs_le]; constructor <;> linarith
  calc ∑ k, |hH.eigenvalues k| ≤ ∑ k, ((star (fun i => V i k) ⬝ᵥ (ρ *ᵥ (fun i => V i k))).re +
        (star (fun i => V i k) ⬝ᵥ (σ *ᵥ (fun i => V i k))).re) := Finset.sum_le_sum (fun k _ => hk k)
    _ = (ρ.trace).re + (σ.trace).re := by
        rw [Finset.sum_add_distrib, ← Complex.re_sum, ← Complex.re_sum, sum_col_quad V hV,
          sum_col_quad V hV]
    _ = 2 := by rw [hρ.2, hσ.2]; norm_num

lemma distance_nonneg (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ) : 0 ≤ distance ρ σ := by
  unfold distance
  rw [traceNorm_eq (hρ.1.1.sub hσ.1.1)]
  positivity

lemma distance_le_one (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ) : distance ρ σ ≤ 1 := by
  unfold distance; linarith [traceNorm_sub_le hρ hσ]

lemma density_one {ρ : Mat 1} (hρ : Density ρ) : ρ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  have := hρ.2
  simpa [Matrix.trace] using this

lemma traceNorm_zero : QAlgorithms.traceNorm (0 : Mat d) = 0 := by
  rw [traceNorm_eq isHermitian_zero]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  have := eig_quad (isHermitian_zero (n := Fin d) (α := ℂ)) k
  simp at this; simp [← this]


/-! ### norms -/

lemma frob_sq {A : Mat d} (hA : A.IsHermitian) :
    QAlgorithms.frobNorm A ^ 2 = ∑ i, hA.eigenvalues i ^ 2 := by
  have h1 : QAlgorithms.frobNorm A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    unfold QAlgorithms.frobNorm
    rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have h2 : (∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) = (Aᴴ * A).trace.re := by
    simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [show star (A j i) = (starRingEnd ℂ) (A j i) from rfl, mul_comm, Complex.mul_conj',
      ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [h1, h2]
  have := trace_cfc_sq hA (fun t => t)
  rw [cfc_id' ℝ (Aᴴ * A) (isHermitian_conjTranspose_mul_self A).isSelfAdjoint] at this
  rw [this]

lemma frob_nonneg (A : Mat d) : 0 ≤ QAlgorithms.frobNorm A := by
  unfold QAlgorithms.frobNorm; rw [Matrix.frobenius_norm_def]; positivity

lemma traceNorm_le_frob {A : Mat d} (hA : A.IsHermitian) :
    QAlgorithms.traceNorm A ≤ Real.sqrt d * QAlgorithms.frobNorm A := by
  rw [traceNorm_eq hA]
  have hf : 0 ≤ QAlgorithms.frobNorm A := frob_nonneg A
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin d => (1:ℝ))
    (fun i => |hA.eigenvalues i|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, sq_abs] at hcs
  rw [← frob_sq hA] at hcs
  have h0 : 0 ≤ ∑ i, |hA.eigenvalues i| := by positivity
  rw [← Real.sqrt_sq h0, ← Real.sqrt_sq hf, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt hcs

lemma opNorm_le_frob {A : Mat d} (hA : A.IsHermitian) : opNorm A ≤ QAlgorithms.frobNorm A := by
  refine opNorm_le_of_quad hA (frob_nonneg A) (fun x => ?_)
  rw [quad_re_self hA, ← sum_normsq_U hA, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul, abs_of_nonneg (sq_nonneg ‖(star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i‖)]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have h := frob_sq hA
  have : hA.eigenvalues i ^ 2 ≤ QAlgorithms.frobNorm A ^ 2 := by
    rw [h]; exact Finset.single_le_sum (f := fun j => hA.eigenvalues j ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  exact abs_le_of_sq_le_sq' this (frob_nonneg A) |> fun h => abs_le.mpr ⟨h.1, h.2⟩

lemma opNorm_add (A B : Mat d) : opNorm (A + B) ≤ opNorm A + opNorm B := by
  unfold opNorm; rw [map_add]; exact norm_add_le _ _

lemma row_normsq (M : Mat d) (hM : M * star M = 1) (j : Fin d) :
    ∑ k, ‖M j k‖^2 = 1 := by
  have h := congrArg (fun A : Mat d => (A j j).re) hM
  simp only [mul_apply, Matrix.star_eq_conjTranspose, conjTranspose_apply, one_apply_eq,
    Complex.one_re, Complex.re_sum] at h
  rw [← h]; refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show star (M j k) = (starRingEnd ℂ) (M j k) from rfl, Complex.mul_conj',
    ← Complex.ofReal_pow, Complex.ofReal_re]

/-- diagonal quadratic forms in any orthonormal basis are dominated by the trace norm -/
lemma sum_abs_diag_le {A : Mat d} (hA : A.IsHermitian) (V : Mat d) (hV : star V * V = 1)
    (hV' : V * star V = 1) :
    ∑ k, |(star (fun i => V i k) ⬝ᵥ (A *ᵥ (fun i => V i k))).re| ≤ QAlgorithms.traceNorm A := by
  rw [traceNorm_eq hA]
  set W := (hA.eigenvectorUnitary : Mat d)
  have hWW' : W * star W = 1 := Unitary.mul_star_self_of_mem (U_mem hA)
  have hWW : star W * W = 1 := Unitary.star_mul_self_of_mem (U_mem hA)
  set Mx := star W * V
  have hMx : Mx * star Mx = 1 := by
    simp only [Mx, star_mul, star_star]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc V, hV', Matrix.one_mul, hWW]
  have hMx' : star Mx * Mx = 1 := by
    simp only [Mx, star_mul, star_star]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc W, hWW', Matrix.one_mul, hV]
  have hk : ∀ k, (star (fun i => V i k) ⬝ᵥ (A *ᵥ (fun i => V i k))).re =
      ∑ j, hA.eigenvalues j * ‖Mx j k‖^2 := by
    intro k; rw [quad_re_self hA]; simp only [mulVec_col, Mx]; rfl
  calc ∑ k, |(star (fun i => V i k) ⬝ᵥ (A *ᵥ (fun i => V i k))).re|
      ≤ ∑ k, ∑ j, |hA.eigenvalues j| * ‖Mx j k‖^2 := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [hk]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [abs_mul, abs_of_nonneg (sq_nonneg ‖Mx j k‖)]
    _ = ∑ j, |hA.eigenvalues j| * ∑ k, ‖Mx j k‖^2 := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun j _ => by rw [Finset.mul_sum])
    _ = ∑ j, |hA.eigenvalues j| := by simp [row_normsq Mx hMx]

lemma traceNorm_add_le {A B : Mat d} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    QAlgorithms.traceNorm (A + B) ≤ QAlgorithms.traceNorm A + QAlgorithms.traceNorm B := by
  have hAB : (A + B).IsHermitian := hA.add hB
  set V := (hAB.eigenvectorUnitary : Mat d)
  have hV : star V * V = 1 := Unitary.star_mul_self_of_mem (U_mem hAB)
  have hV' : V * star V = 1 := Unitary.mul_star_self_of_mem (U_mem hAB)
  rw [traceNorm_eq hAB]
  calc ∑ k, |hAB.eigenvalues k| = ∑ k, |(star (fun i => V i k) ⬝ᵥ ((A + B) *ᵥ (fun i => V i k))).re| := by
        refine Finset.sum_congr rfl (fun k _ => ?_); rw [eig_quad hAB k]
    _ ≤ ∑ k, (|(star (fun i => V i k) ⬝ᵥ (A *ᵥ (fun i => V i k))).re| +
          |(star (fun i => V i k) ⬝ᵥ (B *ᵥ (fun i => V i k))).re|) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [quad_add, Complex.add_re]; exact abs_add_le _ _
    _ ≤ _ := by
        rw [Finset.sum_add_distrib]
        exact add_le_add (sum_abs_diag_le hA V hV hV') (sum_abs_diag_le hB V hV hV')

lemma traceNorm_neg (A : Mat d) : QAlgorithms.traceNorm (-A) = QAlgorithms.traceNorm A := by
  unfold QAlgorithms.traceNorm; simp

lemma quad_conj_herm' {G : Mat d} (hG : G.IsHermitian) (B : Mat d) (x : Fin d → ℂ) :
    star x ⬝ᵥ ((G * B * G) *ᵥ x) = star (G *ᵥ x) ⬝ᵥ (B *ᵥ (G *ᵥ x)) := by
  have h := quad_conj G B x
  have hs : star G = G := by rw [Matrix.star_eq_conjTranspose, hG.eq]
  rwa [hs] at h

lemma herm_compress {Q A : Mat d} (hQ : projector Q) (hA : A.IsHermitian) :
    (Q * A * Q).IsHermitian := by
  have := isHermitian_mul_mul_conjTranspose Q hA
  rwa [hQ.1.eq] at this

lemma proj_normsq {Q : Mat d} (hQ : projector Q) (x : Fin d → ℂ) :
    (star (Q *ᵥ x) ⬝ᵥ (Q *ᵥ x)).re ≤ (star x ⬝ᵥ x).re := by
  have hQ' : projector (1 - Q) := by
    refine ⟨(isHermitian_one).sub hQ.1, ?_⟩
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hQ.2]; simp
  have e1 : star (Q *ᵥ x) ⬝ᵥ (Q *ᵥ x) = star x ⬝ᵥ ((Q * 1 * Q) *ᵥ x) := by
    rw [quad_conj_herm' hQ.1, one_mulVec]
  have e2 : star ((1 - Q) *ᵥ x) ⬝ᵥ ((1 - Q) *ᵥ x) = star x ⬝ᵥ (((1 - Q) * 1 * (1 - Q)) *ᵥ x) := by
    rw [quad_conj_herm' hQ'.1, one_mulVec]
  rw [Matrix.mul_one, hQ.2] at e1
  rw [Matrix.mul_one, hQ'.2] at e2
  have h0 := normsq_nonneg ((1 - Q) *ᵥ x)
  rw [e2, sub_mulVec, one_mulVec, dotProduct_sub, Complex.sub_re] at h0
  rw [e1]; linarith

lemma opNorm_compress {Q A : Mat d} (hQ : projector Q) (hA : A.IsHermitian) :
    opNorm (Q * A * Q) ≤ opNorm A := by
  refine opNorm_le_of_quad (herm_compress hQ hA) (norm_nonneg _) (fun x => ?_)
  rw [quad_conj_herm' hQ.1]
  refine (quad_le_opNorm A _).trans ?_
  exact mul_le_mul_of_nonneg_left (proj_normsq hQ x) (norm_nonneg _)


/-! ### the report projector -/

def ind (d : ℕ) (t : ℝ) : ℝ := if 0 ≤ t ∧ t < 1/(2*Real.log d) then 1 else 0

lemma rp_eq (a : Mat d) : reportProjector d a = cfc (ind d) a := rfl

lemma rp_projector {a : Mat d} (ha : a.IsHermitian) : projector (reportProjector d a) := by
  refine ⟨cfc_herm ha _, ?_⟩
  rw [rp_eq, cfc_mul' ha]
  congr 1; funext t; unfold ind; split_ifs <;> norm_num

lemma rank_one_sub_rp {a : Mat d} (ha : Density a) (hd : 2 ≤ d) :
    ((1 - reportProjector d a).rank : ℝ) ≤ 2 * Real.log d := by
  have hH := ha.1.1
  set U := (hH.eigenvectorUnitary : Mat d)
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem (U_mem hH)
  have hL : 0 < Real.log d := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  set δ := 1/(2*Real.log d) with hδ
  have hδ0 : 0 < δ := by positivity
  have e : 1 - reportProjector d a = U * diagonal (fun i => (((1 - ind d (hH.eigenvalues i)) : ℝ) : ℂ)) * star U := by
    rw [rp_eq, cfc_explicit hH]
    conv_lhs => rw [← hUU]
    rw [show U * star U = U * diagonal (fun _ => (1:ℂ)) * star U by rw [diagonal_one, Matrix.mul_one]]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
    congr 2; funext i; push_cast; ring
  have hrk : (1 - reportProjector d a).rank ≤
      Fintype.card {i // (((1 - ind d (hH.eigenvalues i)) : ℝ) : ℂ) ≠ 0} := by
    rw [e, ← rank_diagonal]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  set S := Finset.univ.filter (fun i => δ ≤ hH.eigenvalues i)
  have hcard : Fintype.card {i // (((1 - ind d (hH.eigenvalues i)) : ℝ) : ℂ) ≠ 0} ≤ S.card := by
    rw [Fintype.card_subtype]
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hi ⊢
    have hnn := ha.1.eigenvalues_nonneg i
    by_contra hlt; push Not at hlt
    apply hi
    unfold ind; rw [if_pos ⟨by convert hnn, hlt⟩]; simp
  have hsum : (S.card : ℝ) * δ ≤ 1 := by
    have h1 : ∑ i, hH.eigenvalues i = 1 := by
      have := congrArg Complex.re (hH.trace_eq_sum_eigenvalues)
      rw [ha.2, Complex.re_sum] at this; simpa using this.symm
    calc (S.card : ℝ) * δ = ∑ _i ∈ S, δ := by simp
      _ ≤ ∑ i ∈ S, hH.eigenvalues i := Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
      _ ≤ ∑ i, hH.eigenvalues i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => by convert ha.1.eigenvalues_nonneg i)
      _ = 1 := h1
  have : (S.card : ℝ) ≤ 2 * Real.log d := by
    rw [hδ] at hsum
    have := (le_div_iff₀ hδ0).mpr hsum
    rwa [hδ, one_div_one_div] at this
  calc ((1 - reportProjector d a).rank : ℝ) ≤ S.card := by exact_mod_cast hrk.trans hcard
    _ ≤ _ := this

lemma opNorm_compress_rp {a P : Mat d} (ha : Density a) (hP : P.IsHermitian) (hd : 2 ≤ d)
    (hclose : opNorm (P - a) ≤ 1/(2*Real.log d)) :
    opNorm (compress (reportProjector d a) P) ≤ 1/Real.log d := by
  have hH := ha.1.1
  set Q := reportProjector d a
  have hQ := rp_projector (d := d) hH
  have hL : 0 < Real.log d := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  have e : compress Q P = Q * a * Q + Q * (P - a) * Q := by
    unfold compress; simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
  have h1 : opNorm (Q * a * Q) ≤ 1/(2*Real.log d) := by
    have eQ : Q * a * Q = cfc (fun t => ind d t * t * ind d t) a := by
      have : Q * a * Q = cfc (ind d) a * cfc (fun t : ℝ => t) a * cfc (ind d) a := by
        rw [cfc_id'' hH]; rfl
      rw [this, cfc_mul' hH, cfc_mul' hH]
    rw [eQ]
    refine opNorm_le_of_quad (cfc_herm hH _) (by positivity) (fun x => ?_)
    rw [quad_re hH, ← sum_normsq_U hH, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖(star (hH.eigenvectorUnitary : Mat d) *ᵥ x) i‖)]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    unfold ind; split_ifs with h
    · simp only [one_mul, mul_one]; rw [abs_of_nonneg h.1]; exact h.2.le
    · simp; positivity
  have h2 : opNorm (Q * (P - a) * Q) ≤ 1/(2*Real.log d) :=
    (opNorm_compress hQ (hP.sub hH)).trans hclose
  rw [e]
  calc opNorm (Q * a * Q + Q * (P - a) * Q) ≤ opNorm (Q * a * Q) + opNorm (Q * (P - a) * Q) :=
        opNorm_add _ _
    _ ≤ 1/(2*Real.log d) + 1/(2*Real.log d) := add_le_add h1 h2
    _ = 1/Real.log d := by field_simp; ring

lemma matrixEval_eq_aeval (p : Polynomial ℝ) (A : Mat d) :
    matrixEval p A = Polynomial.aeval A p := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, matrixEval, Polynomial.sum_def]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [show ((p.coeff k : ℝ) : ℂ) • A ^ k = (p.coeff k : ℝ) • A ^ k from
    (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm]

def varOf (X Y : Mat d) (t : Bool) : Mat d := if t then Y else X

def exprEval (u : MatrixExpression d) (X Y : Mat d) : Mat d :=
  (u.map (fun w => wordEval w X Y)).sum

lemma wordEval_mul (u v : Word d) (X Y : Mat d) :
    wordEval (wordMul u v) X Y = wordEval u X Y * wordEval v X Y := by
  unfold wordMul
  rcases v with ⟨vf, vt⟩
  cases vf with
  | nil => simp [wordEval, Matrix.mul_assoc]
  | cons At xs =>
    rcases At with ⟨A, t⟩
    simp only [wordEval, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    simp only [Matrix.mul_assoc]

lemma exprEval_append (u v : MatrixExpression d) (X Y : Mat d) :
    exprEval (u ++ v) X Y = exprEval u X Y + exprEval v X Y := by
  simp [exprEval]

lemma exprEval_mul (u v : MatrixExpression d) (X Y : Mat d) :
    exprEval (exprMul u v) X Y = exprEval u X Y * exprEval v X Y := by
  unfold exprMul exprEval
  induction u with
  | nil => simp
  | cons a u ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      Matrix.add_mul]
    rw [ih]; congr 1
    rw [List.map_map]
    simp only [Function.comp_def, wordEval_mul]
    rw [← List.sum_map_mul_left]

lemma exprEval_const (A : Mat d) (X Y : Mat d) : exprEval (exprConst A) X Y = A := by
  simp [exprEval, exprConst, wordEval]

lemma exprEval_var (t : Bool) (X Y : Mat d) : exprEval (exprVar d t) X Y = varOf X Y t := by
  simp [exprEval, exprVar, wordEval, varOf]

lemma exprEval_scale (c : ℝ) (u : MatrixExpression d) (X Y : Mat d) :
    exprEval (exprScale c u) X Y = (c : ℂ) • exprEval u X Y := by
  unfold exprScale exprEval
  induction u with
  | nil => simp
  | cons a u ih =>
    simp only [List.map_cons, List.sum_cons, List.map_map, smul_add] at ih ⊢
    rw [← ih]
    simp [wordEval, Function.comp_def]

lemma exprEval_pow (u : MatrixExpression d) (X Y : Mat d) (k : ℕ) :
    exprEval (exprPow u k) X Y = exprEval u X Y ^ k := by
  induction k with
  | zero => simp [exprPow, exprEval_const]
  | succ k ih => rw [exprPow, exprEval_mul, ih, pow_succ]

lemma exprEval_flatMap {α : Type*} (l : List α) (g : α → MatrixExpression d) (X Y : Mat d) :
    exprEval (l.flatMap g) X Y = (l.map (fun k => exprEval (g k) X Y)).sum := by
  induction l with
  | nil => simp [exprEval]
  | cons k l ih => simp only [List.flatMap_cons, List.map_cons, List.sum_cons, exprEval_append, ih]

lemma exprEval_poly (p : Polynomial ℝ) (u : MatrixExpression d) (X Y : Mat d) :
    exprEval (exprPoly p u) X Y = matrixEval p (exprEval u X Y) := by
  unfold exprPoly matrixEval
  rw [exprEval_flatMap, Finset.sum_map_toList]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [exprEval_scale, exprEval_pow]

lemma evaluate_traceExpr (u : MatrixExpression d) (X Y : Mat d) :
    evaluate (traceExpr u) X Y = (exprEval u X Y).trace := by
  simp only [evaluate, traceExpr, exprEval, zero_add]
  rw [Matrix.trace_list_sum, List.map_map]; rfl


lemma evaluate_eq (g : TraceExpression d) (X Y : Mat d) :
    evaluate g X Y = g.constant + (exprEval g.words X Y).trace := by
  simp only [evaluate, exprEval]
  rw [Matrix.trace_list_sum, List.map_map]; rfl

lemma prod_sub (Q X Y : Mat d) (xs : List (Mat d × Bool)) :
    (xs.map (fun At => Q * At.1 * Q * (if At.2 then Y else X))).prod * Q =
      Q * (xs.map (fun At => At.1 * (if At.2 then Q * Y * Q else Q * X * Q))).prod := by
  induction xs with
  | nil => simp
  | cons At xs ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [Matrix.mul_assoc, ih]
    rcases At with ⟨A, t⟩
    cases t <;> simp [Matrix.mul_assoc]

lemma evaluate_subst (Q : Mat d) (f : TraceExpression d) (X Y : Mat d) :
    evaluate (substituteCompression Q f) X Y = evaluate f (Q * X * Q) (Q * Y * Q) := by
  simp only [evaluate, substituteCompression, List.map_map]
  congr 2
  refine List.map_congr_left (fun w _ => ?_)
  rcases w with ⟨fs, tl⟩
  cases fs with
  | nil => simp [wordEval]
  | cons At xs =>
    rcases At with ⟨A, t⟩
    simp only [Function.comp_apply, wordEval, List.map_cons, List.prod_cons, List.map_map]
    have h := prod_sub Q X Y xs
    simp only [Function.comp_def] at h ⊢
    congr 1
    calc A * Q * (if t = true then Y else X) *
          (List.map (fun x => Q * x.1 * Q * if x.2 = true then Y else X) xs).prod * (Q * tl)
        = A * Q * (if t = true then Y else X) *
          ((List.map (fun x => Q * x.1 * Q * if x.2 = true then Y else X) xs).prod * Q) * tl := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [h]; cases t <;> simp [Matrix.mul_assoc]

lemma evaluate_estimator (A C₀ : ℝ) (ε : ℝ) (Q X Y : Mat d) :
    evaluate (estimatorExpression A C₀ d ε Q) X Y =
      evaluate (if ε * Real.log d ≤ 1 then
          traceExpr (exprPoly (q ⌈C₀*d/ε⌉₊) (exprVar d true))
        else multiscale A d (ε/8)) (Q * X * Q) (Q * Y * Q) +
      (matrixEval (q ⌈C₀*Real.log d/ε⌉₊) Y).trace -
      (matrixEval (q ⌈C₀*Real.log d/ε⌉₊) (Q * Y * Q)).trace := by
  simp only [estimatorExpression]
  set fr := (if ε * Real.log d ≤ 1 then
          traceExpr (exprPoly (q ⌈C₀*d/ε⌉₊) (exprVar d true))
        else multiscale A d (ε/8)) with hfr
  set corr := exprPoly (q ⌈C₀*Real.log d/ε⌉₊) (exprVar d true) with hcorr
  have h1 : evaluate (substituteCompression Q fr) X Y =
      (substituteCompression Q fr).constant + (exprEval (substituteCompression Q fr).words X Y).trace :=
    evaluate_eq _ X Y
  have h2 : (substituteCompression Q (traceExpr corr)).constant +
      (exprEval (substituteCompression Q (traceExpr corr)).words X Y).trace =
      (matrixEval (q ⌈C₀*Real.log d/ε⌉₊) (Q * Y * Q)).trace := by
    rw [← evaluate_eq, evaluate_subst, evaluate_traceExpr, hcorr, exprEval_poly, exprEval_var]; rfl
  have h3 : exprEval corr X Y = matrixEval (q ⌈C₀*Real.log d/ε⌉₊) Y := by
    rw [hcorr, exprEval_poly, exprEval_var]; rfl
  rw [evaluate_eq, exprEval_append, exprEval_append, exprEval_scale, ← evaluate_subst, h1, h3]
  simp only [trace_add, trace_smul, Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul,
    trace_neg]
  rw [← h2]
  ring




/-! ### reality of the estimator polynomial -/

lemma trace_im_herm {A : Mat d} (hA : A.IsHermitian) : (A.trace).im = 0 := by
  simp only [Matrix.trace, Matrix.diag, Complex.im_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have := congrFun (congrFun hA i) i
  simp only [conjTranspose_apply] at this
  have h2 : (starRingEnd ℂ) (A i i) = A i i := this
  exact Complex.conj_eq_iff_im.mp h2

lemma matrixEval_herm (p : Polynomial ℝ) {A : Mat d} (hA : A.IsHermitian) :
    (matrixEval p A).IsHermitian := by
  rw [matrixEval_eq_aeval, ← cfc_polynomial p A hA.isSelfAdjoint]; exact cfc_herm hA _

lemma herm_list_sum (l : List (Mat d)) (h : ∀ A ∈ l, A.IsHermitian) : l.sum.IsHermitian := by
  induction l with
  | nil => exact isHermitian_zero
  | cons A l ih =>
    rw [List.sum_cons]
    exact (h A (List.mem_cons_self)).add (ih (fun B hB => h B (List.mem_cons_of_mem _ hB)))

lemma herm_smul_real (c : ℝ) {A : Mat d} (hA : A.IsHermitian) : ((c : ℂ) • A).IsHermitian := by
  unfold IsHermitian at hA ⊢; rw [conjTranspose_smul, hA]; simp [Complex.conj_ofReal]

lemma filteredY_herm (l : ℕ) {X Y : Mat d} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (exprEval (filteredY d l) X Y).IsHermitian := by
  unfold filteredY
  split_ifs
  · rw [exprEval_var]; exact hY
  · simp only
    rw [exprEval_mul, exprEval_mul, exprEval_poly, exprEval_var, exprEval_var]
    simp only [varOf, if_true, Bool.false_eq_true, if_false]
    have hr := matrixEval_herm (filter ((2:ℝ)^(-(l:ℤ)))) hX
    have := isHermitian_mul_mul_conjTranspose (matrixEval (filter ((2:ℝ)^(-(l:ℤ)))) X) hY
    rwa [hr.eq] at this

lemma multiscale_herm (A : ℝ) (ε : ℝ) {X Y : Mat d} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (exprEval (multiscale A d ε).words X Y).IsHermitian := by
  unfold multiscale traceExpr
  simp only
  rw [exprEval_flatMap]
  apply herm_list_sum
  intro B hB
  rw [List.mem_map] at hB
  obtain ⟨i, _, rfl⟩ := hB
  rw [exprEval_scale, exprEval_append, exprEval_scale, exprEval_poly, exprEval_poly,
    exprEval_scale, exprEval_scale]
  refine herm_smul_real _ ((matrixEval_herm _ (herm_smul_real _ (filteredY_herm _ hX hY))).add
    (herm_smul_real _ (matrixEval_herm _ (herm_smul_real _ (filteredY_herm _ hX hY)))))

lemma realOnHermitian_f (dd : ℕ) (ε : ℝ) {Q : Mat d} (hQ : projector Q) :
    realOnHermitian (f d ε Q) := by
  intro X Y hX hY
  rw [show f d ε Q = estimatorExpression constructionA constructionC₀ d ε Q from rfl,
    evaluate_estimator]
  have hX' := herm_compress hQ hX
  have hY' := herm_compress hQ hY
  rw [Complex.sub_im, Complex.add_im, trace_im_herm (matrixEval_herm _ hY),
    trace_im_herm (matrixEval_herm _ hY')]
  split_ifs
  · rw [evaluate_traceExpr, exprEval_poly, exprEval_var]
    simp only [varOf, if_true]
    rw [trace_im_herm (matrixEval_herm _ hY')]; ring
  · rw [evaluate_eq]
    simp only [multiscale, traceExpr, Complex.add_im, Complex.zero_im, zero_add]
    have := trace_im_herm (multiscale_herm constructionA (ε/8) hX' hY')
    simp only [multiscale, traceExpr] at this
    rw [this]; ring


end OTDRoot

namespace OTDProp45

lemma add_pow_ge {x S : ℝ} (hx : 0 ≤ x) (hS : 0 ≤ S) : ∀ a : ℕ, 1 ≤ a → x^a + S^a ≤ (x + S)^a
  | 0, h => by omega
  | 1, _ => by simp
  | (a+2), _ => by
    have ih := add_pow_ge hx hS (a+1) (by omega)
    calc x^(a+2) + S^(a+2) ≤ (x + S) * (x^(a+1) + S^(a+1)) := by
          rw [pow_succ x, pow_succ S]
          nlinarith [pow_nonneg hx (a+1), pow_nonneg hS (a+1)]
      _ ≤ (x + S) * (x + S)^(a+1) := mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (x + S)^(a+2) := by ring

lemma sum_pow_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) (a : ℕ) (ha : 1 ≤ a) :
    ∑ i ∈ s, c i ^ a ≤ (∑ i ∈ s, c i) ^ a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_pow (by omega : a ≠ 0)]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have h1 := ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    have h2 := add_pow_ge (hc i (Finset.mem_insert_self i s))
      (Finset.sum_nonneg (fun j hj => hc j (Finset.mem_insert_of_mem hj))) a ha
    linarith

/-- (51): Σ w^j/(j!)^a ≤ exp(a w^{1/a}) over any range -/
lemma series_bound (w : ℝ) (hw : 0 ≤ w) (a : ℕ) (ha : 1 ≤ a) (S : Finset ℕ) :
    ∑ j ∈ S, w^j / ((j ! : ℝ))^a ≤ Real.exp (a * w ^ (1 / (a:ℝ))) := by
  set u := w ^ (1 / (a:ℝ)) with hu
  have hu0 : 0 ≤ u := by positivity
  have hua : u ^ a = w := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hw, one_div_mul_cancel (by positivity), Real.rpow_one]
  have e : ∀ j, w^j / ((j ! : ℝ))^a = (u^j / j !)^a := by
    intro j; rw [div_pow, ← pow_mul, mul_comm j a, pow_mul, hua]
  simp only [e]
  refine (sum_pow_le S _ (fun j _ => by positivity) a ha).trans ?_
  rw [show a * u = u * a by ring, Real.exp_mul]
  have hS : ∑ j ∈ S, u^j / (j ! : ℝ) ≤ Real.exp u := by
    have hsub : S ⊆ Finset.range (S.sup id + 1) := by
      intro j hj; simp; have := Finset.le_sup (f := id) hj; simp at this; omega
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)) ?_
    exact Real.sum_le_exp_of_nonneg hu0 _
  rw [Real.rpow_natCast]
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => by positivity)) hS a

lemma choose_inv_le {n j : ℕ} (h : 2 * j ≤ n) (hn : 0 < n) :
    ((n.choose j : ℕ) : ℝ)⁻¹ ≤ (j ! : ℝ) * (2 / n)^j := by
  have h1 : ((n / 2 : ℝ))^j ≤ (n.descFactorial j : ℝ) := by
    have := Nat.pow_sub_le_descFactorial n j
    have h2 : (n / 2 : ℝ) ≤ ((n + 1 - j : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      have : (2 * j : ℝ) ≤ n := by exact_mod_cast h
      push_cast; linarith
    calc ((n / 2 : ℝ))^j ≤ ((n + 1 - j : ℕ) : ℝ)^j := pow_le_pow_left₀ (by positivity) h2 j
      _ ≤ _ := by exact_mod_cast this
  have h3 : (n.descFactorial j : ℝ) = (j ! : ℝ) * n.choose j := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose n j
  have hc : (0:ℝ) < n.choose j := by exact_mod_cast Nat.choose_pos (by omega)
  have hf : (0:ℝ) < j ! := by exact_mod_cast Nat.factorial_pos j
  rw [h3] at h1
  rw [inv_le_iff_one_le_mul₀ hc]
  calc (1:ℝ) = (j ! : ℝ) * (2/n)^j * ((n/2)^j / j !) := by
        rw [div_pow, div_pow]; field_simp
    _ ≤ (j ! : ℝ) * (2/n)^j * n.choose j := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_iff₀ hf]; linarith

lemma fact_two_ge (j : ℕ) : 2^j * ((j ! : ℝ))^2 ≤ ((2*j) ! : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j+1) = 2 * j + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have h0 : (0:ℝ) ≤ 2 * ((j:ℝ) + 1)^2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left ih h0
    have h2 : 2 * ((j:ℝ) + 1)^2 ≤ (2 * j + 1 + 1) * (2 * j + 1) := by nlinarith
    have h3 : 0 ≤ (((2 * j) ! : ℕ) : ℝ) := by positivity
    calc (2:ℝ)^(j+1) * (((j:ℝ) + 1) * j !)^2 = 2 * ((j:ℝ) + 1)^2 * (2^j * ((j ! : ℝ))^2) := by ring
      _ ≤ 2 * ((j:ℝ) + 1)^2 * ((2*j) ! : ℝ) := h1
      _ ≤ (2 * j + 1 + 1) * (2 * j + 1) * ((2*j) ! : ℝ) := mul_le_mul_of_nonneg_right h2 h3
      _ = _ := by ring

lemma prod_le (β : ℝ) (hβ : 0 < β) (j : ℕ) :
    ∏ l ∈ Finset.range j, (1 + (l:ℝ) * β) ≤ 2^j * (1 + (j * β)^j) := by
  calc ∏ l ∈ Finset.range j, (1 + (l:ℝ) * β) ≤ ∏ _l ∈ Finset.range j, (1 + (j:ℝ) * β) := by
        apply Finset.prod_le_prod (fun l _ => by positivity)
        intro l hl; simp at hl
        have : (l:ℝ) ≤ j := by exact_mod_cast hl.le
        nlinarith
    _ = (1 + j * β)^j := by simp
    _ ≤ (2 * max 1 (j * β))^j := pow_le_pow_left₀ (by positivity)
        (by have := le_max_left 1 ((j:ℝ) * β); have := le_max_right 1 ((j:ℝ) * β); linarith) j
    _ = 2^j * (max 1 (j * β))^j := by ring
    _ ≤ 2^j * (1 + (j * β)^j) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rcases le_total 1 ((j:ℝ) * β) with h | h
        · rw [max_eq_right h]; linarith [pow_nonneg (by positivity : (0:ℝ) ≤ j * β) j]
        · rw [max_eq_left h, one_pow]; linarith [pow_nonneg (by positivity : (0:ℝ) ≤ j * β) j]


lemma pow_le_two_pow (j : ℕ) : (j:ℝ) ≤ 2^j := by
  have := Nat.lt_two_pow_self (n := j); exact_mod_cast this.le

lemma jpow_le (j : ℕ) : ((j:ℝ))^j ≤ 3^j * (j ! : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (x := (j:ℝ)) (by positivity) j
  have he : Real.exp j ≤ 3^j := by
    rw [← Real.exp_one_rpow, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) (by have := Real.exp_one_lt_d9; norm_num at this; linarith) j
  have hf : (0:ℝ) < j ! := by exact_mod_cast Nat.factorial_pos j
  rw [div_le_iff₀ hf] at h
  nlinarith

def cf (β : ℝ) (j : ℕ) : ℝ := (∏ l ∈ Finset.range j, (1 + (l:ℝ)*β)) / ((j-1) ! : ℝ)

lemma term_bound {K β d ε : ℝ} (hK : 0 < K) (hβ : 0 < β) (hd : 0 < d) (hε : 0 < ε)
    {n j : ℕ} (hj : 2 ≤ j) (hjn : 2 * j ≤ n) (hn : 0 < n) :
    ((n.choose j : ℕ) : ℝ)⁻¹ * ((K * d / ε^2)^j / (d * ε * ((2*j) ! : ℝ)))^2 * cf β j ≤
      1 / (d^2 * ε^2) * ((2 * (K^2 * d^2 / (ε^4 * n)))^j / ((j ! : ℝ))^4 +
        (6 * β * (K^2 * d^2 / (ε^4 * n)))^j / ((j ! : ℝ))^3) := by
  set F := (j ! : ℝ) with hF
  set z := K^2 * d^2 / (ε^4 * n) with hz
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hFpos : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos j
  have hF1 : ((j - 1) ! : ℝ) * j = F := by
    rw [hF]; obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp [Nat.factorial_succ]; ring
  have hF1pos : (0:ℝ) < ((j - 1) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hjR : (0:ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hC := choose_inv_le hjn hn
  have h2j := fact_two_ge j
  have hP := prod_le β hβ j
  have hzpos : 0 < z := by positivity
  -- step 1
  have step1 : ((n.choose j : ℕ) : ℝ)⁻¹ * ((K * d / ε^2)^j / (d * ε * ((2*j) ! : ℝ)))^2 * cf β j ≤
      (F * (2 / n)^j) * ((K * d / ε^2)^j / (d * ε * (2^j * F^2)))^2 *
        (2^j * (1 + (j * β)^j) / ((j - 1) ! : ℝ)) := by
    apply mul_le_mul (mul_le_mul hC _ (by positivity) (by positivity)) _ (by unfold cf; positivity)
      (by positivity)
    · apply pow_le_pow_left₀ (by positivity)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left h2j (by positivity)
    · unfold cf; exact div_le_div_of_nonneg_right hP hF1pos.le
  -- step 2: algebra
  have step2 : (F * (2 / n)^j) * ((K * d / ε^2)^j / (d * ε * (2^j * F^2)))^2 *
        (2^j * (1 + (j * β)^j) / ((j - 1) ! : ℝ)) =
      1 / (d^2 * ε^2) * ((j:ℝ) * z^j * (1 + (j * β)^j) / F^4) := by
    rw [hz, ← hF1]
    field_simp
    ring
  -- step 3
  have step3 : (j:ℝ) * z^j * (1 + (j * β)^j) / F^4 ≤ (2 * z)^j / F^4 + (6 * β * z)^j / F^3 := by
    have hj2 := pow_le_two_pow j
    have hjj := jpow_le j
    have e1 : (j:ℝ) * z^j * (1 + (j * β)^j) / F^4 = (j:ℝ) * z^j / F^4 + (j:ℝ) * z^j * (j:ℝ)^j * β^j / F^4 := by
      rw [mul_pow]; ring
    rw [e1]
    apply add_le_add
    · apply div_le_div_of_nonneg_right _ (by positivity)
      rw [mul_pow]; exact mul_le_mul_of_nonneg_right hj2 (by positivity)
    · rw [show (6 * β * z)^j / F^3 = (2^j * z^j * (3^j * F) * β^j) / F^4 by
        rw [mul_pow, mul_pow, show (6:ℝ)^j = 2^j * 3^j by rw [← mul_pow]; norm_num]; field_simp]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h1 : (j:ℝ) * z^j * (j:ℝ)^j * β^j ≤ 2^j * z^j * (j:ℝ)^j * β^j := by
        have : 0 ≤ z^j * (j:ℝ)^j * β^j := by positivity
        nlinarith
      have h2 : 2^j * z^j * (j:ℝ)^j * β^j ≤ 2^j * z^j * (3^j * F) * β^j := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hjj (by positivity)
      linarith
  calc _ ≤ _ := step1
    _ = _ := step2
    _ ≤ 1 / (d^2 * ε^2) * ((2 * z)^j / F^4 + (6 * β * z)^j / F^3) :=
        mul_le_mul_of_nonneg_left step3 (by positivity)


lemma root_le' {y w : ℝ} (hw : 0 ≤ w) (hy : 0 ≤ y) (k : ℕ) (hk : 0 < k) (h : w ≤ y ^ k) :
    w ^ (1 / (k:ℝ)) ≤ y := by
  have := Real.rpow_le_rpow hw h (by positivity : (0:ℝ) ≤ 1 / (k:ℝ))
  rwa [← Real.rpow_natCast, ← Real.rpow_mul hy, mul_one_div_cancel (by positivity), Real.rpow_one] at this

lemma rpow_cube_le (c : ℝ) (hc : 0 ≤ c) : c ^ (1/(3:ℝ)) ≤ 1 + c := by
  rcases le_total c 1 with h | h
  · have : c ^ (1/(3:ℝ)) ≤ 1 := Real.rpow_le_one hc h (by norm_num)
    linarith
  · have : c ^ (1/(3:ℝ)) ≤ c ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le h (by norm_num)
    rw [Real.rpow_one] at this; linarith

def Cp (K : ℝ) : ℝ := 1 + K^2 + 4 * (1 + 2 * K^2) + 3 * (1 + 6 * K^2)

lemma sum_bound {K β d ε L : ℝ} (hK : 0 < K) (hβ : 0 < β) (hd : 0 < d) (hε : 0 < ε) (hL : 0 ≤ L)
    {n D : ℕ} (h2D : 2 * D ≤ n) (hn : 0 < n) :
    ∑ j ∈ Finset.Icc 1 D, ((n.choose j : ℕ) : ℝ)⁻¹ *
        (if j = 1 then K * L / ε^3 else (K * d / ε^2)^j / (d * ε * ((2*j) ! : ℝ)))^2 * cf β j ≤
      Cp K * L^2 / (ε^6 * n) + Cp K / (d^2 * ε^2) *
        (Real.exp (Cp K * Real.sqrt d / (ε * (n:ℝ)^(1/4:ℝ))) +
          Real.exp (Cp K * (β * d^2 / (ε^4 * n))^(1/3:ℝ))) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hCp : K^2 + 1 ≤ Cp K := by unfold Cp; nlinarith [sq_nonneg K]
  have hCp1 : 1 ≤ Cp K := by nlinarith [sq_nonneg K]
  set z := K^2 * d^2 / (ε^4 * n) with hz
  have hzpos : 0 < z := by positivity
  set E1 := Real.exp (Cp K * Real.sqrt d / (ε * (n:ℝ)^(1/4:ℝ)))
  set E2 := Real.exp (Cp K * (β * d^2 / (ε^4 * n))^(1/3:ℝ))
  have hRHS0 : 0 ≤ Cp K / (d^2 * ε^2) * (E1 + E2) := by positivity
  -- tail
  have htail : ∑ j ∈ Finset.Icc 2 D, ((n.choose j : ℕ) : ℝ)⁻¹ *
        (if j = 1 then K * L / ε^3 else (K * d / ε^2)^j / (d * ε * ((2*j) ! : ℝ)))^2 * cf β j ≤
      1 / (d^2 * ε^2) * (E1 + E2) := by
    calc _ ≤ ∑ j ∈ Finset.Icc 2 D, 1 / (d^2 * ε^2) * ((2 * z)^j / ((j ! : ℝ))^4 +
          (6 * β * z)^j / ((j ! : ℝ))^3) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          simp at hj
          rw [if_neg (by omega)]
          exact term_bound hK hβ hd hε hj.1 (by omega) hn
      _ = 1 / (d^2 * ε^2) * (∑ j ∈ Finset.Icc 2 D, (2 * z)^j / ((j ! : ℝ))^4 +
          ∑ j ∈ Finset.Icc 2 D, (6 * β * z)^j / ((j ! : ℝ))^3) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 1 / (d^2 * ε^2) * (Real.exp (4 * (2 * z) ^ (1/(4:ℝ))) +
          Real.exp (3 * (6 * β * z) ^ (1/(3:ℝ)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have a1 := series_bound (2 * z) (by positivity) 4 (by norm_num) (Finset.Icc 2 D)
          have a2 := series_bound (6 * β * z) (by positivity) 3 (by norm_num) (Finset.Icc 2 D)
          push_cast at a1 a2
          linarith
      _ ≤ 1 / (d^2 * ε^2) * (E1 + E2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply add_le_add
          · apply Real.exp_le_exp.mpr
            -- 4 (2z)^{1/4} ≤ Cp K √d / (ε n^{1/4})
            have hn4 : 0 < (n:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos hnR _
            have hn4' : ((n:ℝ)^(1/4:ℝ))^4 = n := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]; norm_num
            set y := (Cp K / 4) * Real.sqrt d / (ε * (n:ℝ)^(1/4:ℝ))
            have hy0 : 0 ≤ y := by positivity
            have hyy : 2 * z ≤ y^4 := by
              have e : y^4 = (Cp K / 4)^4 * d^2 / (ε^4 * n) := by
                simp only [y]; rw [div_pow, mul_pow, mul_pow, hn4',
                  show Real.sqrt d ^ 4 = (Real.sqrt d ^ 2)^2 by ring, Real.sq_sqrt hd.le]
              rw [e, hz, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
              have h1 : 2 * K^2 ≤ (Cp K / 4)^4 := by
                have h2 : 1 + 2 * K^2 ≤ Cp K / 4 := by unfold Cp; nlinarith [sq_nonneg K]
                have h3 : (1 + 2 * K^2) ≤ (1 + 2 * K^2)^4 := by
                  have : 1 ≤ 1 + 2 * K^2 := by nlinarith [sq_nonneg K]
                  calc (1 + 2 * K^2) = (1 + 2 * K^2)^1 := (pow_one _).symm
                    _ ≤ _ := pow_le_pow_right₀ this (by norm_num)
                have h4 : (1 + 2 * K^2)^4 ≤ (Cp K / 4)^4 := pow_le_pow_left₀ (by positivity) h2 4
                linarith
              have : 0 ≤ d^2 * (ε^4 * n) := by positivity
              nlinarith
            have hr := root_le' (by positivity) hy0 4 (by norm_num) hyy
            norm_num at hr
            calc 4 * (2 * z) ^ (1/(4:ℝ)) ≤ 4 * y := by norm_num; linarith
              _ = Cp K * Real.sqrt d / (ε * (n:ℝ)^(1/4:ℝ)) := by simp only [y]; ring
          · apply Real.exp_le_exp.mpr
            set w := β * d^2 / (ε^4 * n)
            have hw0 : 0 ≤ w := by positivity
            have e : 6 * β * z = (6 * K^2) * w := by simp only [w, hz]; ring
            rw [e, Real.mul_rpow (by positivity) hw0]
            have h1 := rpow_cube_le (6 * K^2) (by positivity)
            have h2 : 3 * (1 + 6 * K^2) ≤ Cp K := by unfold Cp; nlinarith [sq_nonneg K]
            have hw3 : 0 ≤ w ^ (1/(3:ℝ)) := by positivity
            calc 3 * ((6 * K^2) ^ (1/(3:ℝ)) * w ^ (1/(3:ℝ))) ≤ 3 * ((1 + 6 * K^2) * w ^ (1/(3:ℝ))) := by
                  gcongr
              _ ≤ Cp K * w ^ (1/(3:ℝ)) := by nlinarith
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp; positivity
  · have hsplit : Finset.Icc 1 D = insert 1 (Finset.Icc 2 D) := by
      ext j; simp; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    have h1 : ((n.choose 1 : ℕ) : ℝ)⁻¹ * (if 1 = 1 then K * L / ε^3 else
        (K * d / ε^2)^1 / (d * ε * ((2*1) ! : ℝ)))^2 * cf β 1 = K^2 * L^2 / (ε^6 * n) := by
      simp [cf]; field_simp
    rw [h1]
    have h2 : K^2 * L^2 / (ε^6 * n) ≤ Cp K * L^2 / (ε^6 * n) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h3 : 1 / (d^2 * ε^2) * (E1 + E2) ≤ Cp K / (d^2 * ε^2) * (E1 + E2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_right hCp1 (by positivity)
    linarith

end OTDProp45

namespace OTDProp45
open Matrix OptimalTraceDistance.Estimation

lemma var_zero_le {d : ℕ} (g : TraceExpression d) (ρ σ : Mat d) : polynomialVariance g 0 ρ σ ≤ 0 := by
  unfold polynomialVariance variance tr
  set G := observable g 0
  have hR : powerState (labelledState ρ σ) 0 = 1 := by
    ext x y
    have hxy : x = y := Subsingleton.elim x y
    subst hxy
    simp [powerState, tensor, OptimalSpectrum.Entangled.kronFamily]
  rw [hR, Matrix.one_mul, Matrix.one_mul]
  have hu : ∀ x : Fin 0 → Bool × Fin d, x = default := fun x => Subsingleton.elim x default
  have h1 : (G ^ 2).trace = (G default default)^2 := by
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_unique, sq, mul_apply]
  have h2 : G.trace = G default default := by
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_unique]
  rw [h1, h2]
  set g := G default default
  rw [sq, Complex.mul_re]
  nlinarith [sq_nonneg g.im]

lemma realF {d : ℕ} (ε : ℝ) : realOnHermitian (F d ε) := by
  intro X Y hX hY
  rw [show F d ε = multiscale constructionA d ε from rfl, OTDRoot.evaluate_eq]
  simp only [multiscale, traceExpr, Complex.add_im, Complex.zero_im, zero_add]
  have := OTDRoot.trace_im_herm (OTDRoot.multiscale_herm constructionA ε hX hY)
  simpa [multiscale, traceExpr] using this

end OTDProp45

open Matrix OptimalTraceDistance.Estimation OTDProp45 in
theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
  ∀ ε : ℝ, 0 < ε → ε ≤ 1/32 → ∀ ρ σ : Mat d, Density ρ → Density σ →
  ∀ Q : Mat d, projector Q → ∀ β : ℝ, 0 < β → opNorm (compress Q (plus ρ σ)) ≤ β →
  ∀ n : ℕ, 2*expressionDegree (F d ε) ≤ n →
    polynomialVariance (substituteCompression Q (F d ε)) n ρ σ ≤
      C*(Real.log d)^2/(ε^6*n) + C/((d : ℝ)^2*ε^2) *
        (Real.exp (C*Real.sqrt d/(ε*(n : ℝ)^(1/4 : ℝ))) +
          Real.exp (C*(β*(d : ℝ)^2/(ε^4*n))^(1/3 : ℝ))) := by
  obtain ⟨C26, hC26, h26⟩ := proposition_2_6
  have hCp : 0 < Cp C26 := by unfold Cp; positivity
  refine ⟨Cp C26, hCp, ?_⟩
  intro d hd ε hε hε1 ρ σ hρ hσ Q hQ β hβ hbound n hn
  have hdpos : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hL : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ d))
  rcases Nat.eq_zero_or_pos n with h0 | hn0
  · subst h0
    refine le_trans (var_zero_le _ ρ σ) ?_
    simp only [Nat.cast_zero, mul_zero, div_zero, zero_add]
    positivity
  obtain ⟨p1, -⟩ := proposition_2_1 d (by omega)
  obtain ⟨hP, -, -, hhi, -, hcomp⟩ := p1 ρ σ hρ hσ
  obtain ⟨hXpsd, hlo, hhi', htr⟩ := hcomp Q hQ
  have hSmH : (minus ρ σ).IsHermitian := by
    have := hP.1.sub hhi.1; rwa [sub_sub_cancel] at this
  have hYH : (compress Q (minus ρ σ)).IsHermitian := OTDRoot.herm_compress hQ hSmH
  obtain ⟨hdeg, -, htay⟩ := h26 d hd ε hε hε1 (compress Q (plus ρ σ)) (compress Q (minus ρ σ))
    hXpsd.1 hYH hXpsd htr hlo hhi'
  have h43 := proposition_4_3 d (by omega) ρ σ hρ hσ Q hQ β hβ hbound (F d ε) (realF ε)
    (fun j => if j = 1 then C26*Real.log d/ε^3 else
      (C26*d/ε^2)^j / ((d : ℝ)*ε*((2*j).factorial : ℝ)))
    (fun j hj => by simp at hj; exact htay j hj.1 hj.2) n hn0 (by omega)
  refine h43.trans ?_
  have := sum_bound (K := C26) (β := β) (d := d) (ε := ε) (L := Real.log d) hC26 hβ hdpos hε hL hn hn0
  exact this
