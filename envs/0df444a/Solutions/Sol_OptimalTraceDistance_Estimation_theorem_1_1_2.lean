-- Prove2me | solution 2 for OptimalTraceDistance.Estimation.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T10:14:48.269179+00:00
-- url     : https://prove2.me/submissions/33d26635-ad38-4c16-8256-e3b98107a82f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OptimalTraceDistance_Estimation_rounded_algorithm_realization
import Theorems.Thm_QAlgorithms_Papers_RoadmapL03_keyl_expectedSquaredFrobeniusError
import Theorems.Thm_OptimalTraceDistance_Estimation_proposition_3_1
import Theorems.Thm_OptimalTraceDistance_Estimation_proposition_3_2
import Theorems.Thm_OptimalTraceDistance_Estimation_proposition_2_7

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
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

namespace OTDRoot
open Matrix OptimalTraceDistance.Estimation

variable {d : ℕ}

lemma est_measurable {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    Measurable (fun o : QAlgorithms.Schur.Partition d n × Matrix.unitaryGroup (Fin d) ℂ =>
      QAlgorithms.Schur.estimate hd hn o.1 o.2) := by
  refine measurable_from_prod_countable_right (fun lam => ?_)
  apply Continuous.measurable
  unfold QAlgorithms.Schur.estimate
  fun_prop

lemma kjl_univ {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (ρ : Mat d) (hρ : Density ρ) :
    QAlgorithms.Tomography.keylJointLaw hd hn ρ hρ Set.univ = 1 := by
  obtain ⟨meas, hmeas⟩ := QAlgorithms.Papers.RoadmapL03.keyl_expectedSquaredFrobeniusError d n hd hn
  rw [← (hmeas ρ hρ).1, QAlgorithms.Measurements.bornLaw_apply _ _ _ _ MeasurableSet.univ,
    meas.total]
  simp [QAlgorithms.effectProb, (QAlgorithms.Tomography.tensorDensity ρ hρ n).2]

lemma tomo_eq {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (ρ : Mat d) (hρ : Density ρ) :
    tomographyLaw m ρ hρ = Measure.map (fun o => QAlgorithms.Schur.estimate hd hm o.1 o.2)
      (QAlgorithms.Tomography.keylJointLaw hd hm ρ hρ) := by
  simp [tomographyLaw, hd, hm]

lemma tomo_univ {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (ρ : Mat d) (hρ : Density ρ) :
    tomographyLaw m ρ hρ Set.univ = 1 := by
  rw [tomo_eq hd hm, Measure.map_apply (est_measurable hd hm) MeasurableSet.univ,
    Set.preimage_univ, kjl_univ]

lemma frob_cont {d : ℕ} (ρ : Mat d) : Continuous (fun a : Mat d => QAlgorithms.frobNorm (a - ρ)) := by
  have : (fun a : Mat d => QAlgorithms.frobNorm (a - ρ)) =
      fun a => (∑ i, ∑ j, ‖(a - ρ) i j‖ ^ (2:ℝ)) ^ (1/2:ℝ) := by
    funext a; unfold QAlgorithms.frobNorm; exact Matrix.frobenius_norm_def _
  rw [this]
  refine Continuous.rpow_const ?_ (fun _ => Or.inr (by norm_num))
  refine continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ => ?_))
  refine Continuous.rpow_const ?_ (fun _ => Or.inr (by norm_num))
  simp only [Matrix.sub_apply]
  have h1 : Continuous fun a : Mat d => a i j :=
    (continuous_apply j).comp (continuous_apply i)
  exact (h1.sub continuous_const).norm

lemma tomo_risk {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (ρ : Mat d) (hρ : Density ρ) :
    ∫⁻ a, ENNReal.ofReal (QAlgorithms.frobNorm (a - ρ) ^ 2) ∂(tomographyLaw m ρ hρ) ≤
      ENNReal.ofReal ((4 * d - 3) / m) := by
  obtain ⟨meas, hmeas⟩ := QAlgorithms.Papers.RoadmapL03.keyl_expectedSquaredFrobeniusError d m hd hm
  rw [tomo_eq hd hm, lintegral_map _ (est_measurable hd hm)]
  · exact (hmeas ρ hρ).2
  · exact ENNReal.measurable_ofReal.comp ((frob_cont ρ).pow 2).measurable

/-- Markov plus normalization: a measurable set containing every decoder output close to ρ. -/
lemma tomo_good {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (ρ : Mat d) (hρ : Density ρ)
    (G : Set (Mat d)) (hG : MeasurableSet G) {t : ℝ} (ht : 0 < t)
    (hsub : ∀ o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ,
      QAlgorithms.frobNorm (QAlgorithms.Schur.estimate hd hm o.1 o.2 - ρ) ^ 2 < t →
        QAlgorithms.Schur.estimate hd hm o.1 o.2 ∈ G) :
    1 - ENNReal.ofReal ((4 * d - 3) / m) / ENNReal.ofReal t ≤ tomographyLaw m ρ hρ G := by
  set F := {a : Mat d | t ≤ QAlgorithms.frobNorm (a - ρ) ^ 2}
  have hF : MeasurableSet F := (isClosed_le continuous_const ((frob_cont ρ).pow 2)).measurableSet
  have hmark : tomographyLaw m ρ hρ F ≤ ENNReal.ofReal ((4 * d - 3) / m) / ENNReal.ofReal t := by
    have h := meas_ge_le_lintegral_div
      (ENNReal.measurable_ofReal.comp ((frob_cont ρ).pow 2).measurable).aemeasurable
      (μ := tomographyLaw m ρ hρ) (ε := ENNReal.ofReal t) (by simpa using ht) ENNReal.ofReal_ne_top
    refine le_trans (le_trans (measure_mono ?_) h) (ENNReal.div_le_div_right (tomo_risk hd hm ρ hρ) _)
    intro a ha
    simp only [Set.mem_ofPred_eq, F] at ha ⊢
    exact ENNReal.ofReal_le_ofReal ha
  have hcompl : tomographyLaw m ρ hρ Fᶜ ≤ tomographyLaw m ρ hρ G := by
    rw [tomo_eq hd hm, Measure.map_apply (est_measurable hd hm) hF.compl,
      Measure.map_apply (est_measurable hd hm) hG]
    apply measure_mono
    intro o ho
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, F] at ho ⊢
    exact hsub o ho
  have hprob : tomographyLaw m ρ hρ Fᶜ = 1 - tomographyLaw m ρ hρ F := by
    have : IsProbabilityMeasure (tomographyLaw m ρ hρ) := ⟨tomo_univ hd hm ρ hρ⟩
    exact prob_compl_eq_one_sub hF
  calc 1 - ENNReal.ofReal ((4 * d - 3) / m) / ENNReal.ofReal t ≤ 1 - tomographyLaw m ρ hρ F :=
        tsub_le_tsub_left hmark 1
    _ = tomographyLaw m ρ hρ Fᶜ := hprob.symm
    _ ≤ _ := hcompl


/-! ### decoder outputs are density matrices -/

lemma yd_card (μ : YoungDiagram) (N : ℕ) (hN : μ.colLen 0 ≤ N) :
    μ.card = ∑ i ∈ Finset.range N, μ.rowLen i := by
  have : μ.cells = (Finset.range N).biUnion (fun i => {i} ×ˢ Finset.range (μ.rowLen i)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_product, Finset.mem_singleton]
    rw [YoungDiagram.mem_cells]
    constructor
    · intro h
      refine ⟨i, ?_, rfl, YoungDiagram.mem_iff_lt_rowLen.mp h⟩
      have := YoungDiagram.mem_iff_lt_colLen.mp h
      have := μ.colLen_anti 0 j (Nat.zero_le j)
      omega
    · rintro ⟨i', _, rfl, hj⟩
      exact YoungDiagram.mem_iff_lt_rowLen.mpr hj
  rw [YoungDiagram.card, this, Finset.card_biUnion]
  · simp
  · intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [Finset.mem_product, Finset.mem_singleton] at hc hc'
    exact hab (hc.1.symm.trans hc'.1)

lemma est_density {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (lam : QAlgorithms.Schur.Partition d n)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : Density (QAlgorithms.Schur.estimate hd hn lam U) := by
  unfold QAlgorithms.Schur.estimate QAlgorithms.Schur.normalizedDiagram
  have hU : star (U : Mat d) * (U : Mat d) = 1 := Unitary.star_mul_self_of_mem U.2
  constructor
  · have hD : (diagonal fun i => ((QAlgorithms.Schur.normalizedRows hd hn lam i : ℝ) : ℂ)).PosSemidef := by
      apply PosSemidef.diagonal
      intro i
      simp only [Pi.zero_apply]
      unfold QAlgorithms.Schur.normalizedRows
      exact_mod_cast (by positivity : (0:ℝ) ≤ (lam.val.rowLen i.val : ℝ) / n)
    have := hD.mul_mul_conjTranspose_same (U : Mat d)
    rwa [← Matrix.star_eq_conjTranspose] at this
  · rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, trace_diagonal]
    unfold QAlgorithms.Schur.normalizedRows
    have hsum : ∑ i : Fin d, (lam.val.rowLen i.val : ℝ) = n := by
      have h1 := yd_card lam.val d lam.2.2
      rw [lam.2.1] at h1
      rw [Fin.sum_univ_eq_sum_range (fun i => (lam.val.rowLen i : ℝ))]
      exact_mod_cast h1.symm
    have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [← Complex.ofReal_sum, ← Finset.sum_div, hsum, div_self hn']
    simp

lemma density_closed (d : ℕ) : IsClosed {a : Mat d | Density a} := by
  have h1 : {a : Mat d | Density a} = {a | a.IsHermitian} ∩ (⋂ x : Fin d → ℂ,
      {a | 0 ≤ star x ⬝ᵥ (a *ᵥ x)}) ∩ {a | a.trace = 1} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro h; exact ⟨⟨h.1.1, h.1.dotProduct_mulVec_nonneg⟩, h.2⟩
    · intro h; exact ⟨PosSemidef.of_dotProduct_mulVec_nonneg h.1.1 h.1.2, h.2⟩
  rw [h1]
  refine ((IsClosed.inter ?_ (isClosed_iInter (fun x => ?_))).inter ?_)
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · exact isClosed_le continuous_const (by fun_prop)
  · exact isClosed_eq (by fun_prop) continuous_const

lemma plus_density {d : ℕ} {ρ σ : Mat d} (hρ : Density ρ) (hσ : Density σ) : Density (plus ρ σ) := by
  refine ⟨(hρ.1.add hσ.1).smul ?_, ?_⟩
  · rw [show (2:ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl]
    exact_mod_cast (by norm_num : (0:ℝ) ≤ 2⁻¹)
  · unfold plus; rw [trace_smul, trace_add, hρ.2, hσ.2]; norm_num



/-! ### rounded reports -/

def cellBound (η : ℝ) : ℤ := (⌈1/η⌉₊ : ℤ) + 1

def CellSet (d : ℕ) (η : ℝ) : Finset (Fin d → Fin d → ℤ × ℤ) :=
  Fintype.piFinset (fun _ => Fintype.piFinset (fun _ =>
    Finset.Icc (-cellBound η) (cellBound η) ×ˢ Finset.Icc (-cellBound η) (cellBound η)))

lemma floor_mem {η x : ℝ} (hη : 0 < η) (hx : |x| ≤ 1) :
    ⌊x / η⌋ ∈ Finset.Icc (-cellBound η) (cellBound η) := by
  rw [Finset.mem_Icc, cellBound]
  have hc : 1/η ≤ (⌈1/η⌉₊ : ℝ) := Nat.le_ceil _
  rw [abs_le] at hx
  constructor
  · have h1 : -(1/η) ≤ x / η := by
      rw [neg_le, ← neg_div]; exact div_le_div_of_nonneg_right (by linarith) hη.le
    have h2 : (-(⌈1/η⌉₊ : ℤ) - 1 : ℝ) < ⌊x/η⌋ := by
      have := Int.sub_one_lt_floor (x/η); push_cast; linarith
    have : (-(⌈1/η⌉₊ : ℤ) - 1 : ℤ) < ⌊x/η⌋ := by exact_mod_cast h2
    omega
  · have h1 : x / η ≤ 1/η := div_le_div_of_nonneg_right hx.2 hη.le
    have h2 : (⌊x/η⌋ : ℝ) ≤ ⌈1/η⌉₊ := (Int.floor_le _).trans (h1.trans hc)
    have : ⌊x/η⌋ ≤ (⌈1/η⌉₊ : ℤ) := by exact_mod_cast h2
    omega

lemma gridCell_mem {η : ℝ} (hη : 0 < η) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    gridCell η (U : Mat d) ∈ CellSet d η := by
  simp only [CellSet, Fintype.mem_piFinset, Finset.mem_product]
  intro i j
  have hb := entry_norm_bound_of_unitary U.2 i j
  refine ⟨floor_mem hη ?_, floor_mem hη ?_⟩
  · exact (Complex.abs_re_le_norm _).trans hb
  · exact (Complex.abs_im_le_norm _).trans hb

abbrev Cells (d : ℕ) (η : ℝ) := ↥(CellSet d η)

/-- the measurable cell of an outcome -/
def Sset {m : ℕ} (η : ℝ) (t : QAlgorithms.Schur.Partition d m × Cells d η) :
    Set (QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ) :=
  {o | o.1 = t.1 ∧ gridCell η (o.2 : Mat d) = t.2.1}

set_option backward.isDefEq.respectTransparency.types false in
open scoped Matrix.Norms.Elementwise in
lemma measurable_gridCell_eq (η : ℝ) (k : Fin d → Fin d → ℤ × ℤ) :
    MeasurableSet {U : Matrix.unitaryGroup (Fin d) ℂ | gridCell η (U : Mat d) = k} := by
  have hset : {U : Matrix.unitaryGroup (Fin d) ℂ | gridCell η (U : Mat d) = k} =
      ⋂ i, ⋂ j, ({U : Matrix.unitaryGroup (Fin d) ℂ | ⌊((U : Mat d) i j).re / η⌋ = (k i j).1} ∩
        {U | ⌊((U : Mat d) i j).im / η⌋ = (k i j).2}) := by
    ext U
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, gridCell]
    constructor
    · intro h i j; rw [← h]; exact ⟨rfl, rfl⟩
    · intro h; funext i j; exact Prod.ext (h i j).1 (h i j).2
  rw [hset]
  refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => MeasurableSet.inter ?_ ?_))
  · have hc : Continuous fun U : Matrix.unitaryGroup (Fin d) ℂ => ((U : Mat d) i j).re / η :=
      (Complex.continuous_re.comp ((continuous_apply j).comp ((continuous_apply i).comp
        continuous_subtype_val))).div_const η
    exact (Int.measurable_floor.comp hc.measurable) (measurableSet_singleton _)
  · have hc : Continuous fun U : Matrix.unitaryGroup (Fin d) ℂ => ((U : Mat d) i j).im / η :=
      (Complex.continuous_im.comp ((continuous_apply j).comp ((continuous_apply i).comp
        continuous_subtype_val))).div_const η
    exact (Int.measurable_floor.comp hc.measurable) (measurableSet_singleton _)

lemma Sset_measurable {m : ℕ} (η : ℝ) (t : QAlgorithms.Schur.Partition d m × Cells d η) :
    MeasurableSet (Sset η t) := by
  have : Sset η t = (Prod.fst ⁻¹' {t.1}) ∩
      (Prod.snd ⁻¹' {U : Matrix.unitaryGroup (Fin d) ℂ | gridCell η (U : Mat d) = t.2.1}) := by
    ext o; simp [Sset]
  rw [this]
  exact (measurable_fst (measurableSet_singleton _)).inter
    (measurable_snd (measurable_gridCell_eq η t.2.1))

lemma Sset_disjoint {m : ℕ} (η : ℝ) {t t' : QAlgorithms.Schur.Partition d m × Cells d η} (h : t ≠ t') :
    Disjoint (Sset η t) (Sset η t') := by
  rw [Set.disjoint_left]
  intro o ho ho'
  apply h
  obtain ⟨h1, h2⟩ := ho
  obtain ⟨h1', h2'⟩ := ho'
  exact Prod.ext (h1.symm.trans h1') (Subtype.ext (h2.symm.trans h2'))

def cellOf {m : ℕ} {η : ℝ} (hη : 0 < η) (o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ) :
    QAlgorithms.Schur.Partition d m × Cells d η := (o.1, ⟨gridCell η (o.2 : Mat d), gridCell_mem hη o.2⟩)

lemma mem_Sset_iff {m : ℕ} {η : ℝ} (hη : 0 < η) (o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ)
    (t : QAlgorithms.Schur.Partition d m × Cells d η) : o ∈ Sset η t ↔ cellOf hη o = t := by
  constructor
  · rintro ⟨h1, h2⟩; exact Prod.ext h1 (Subtype.ext h2)
  · intro h; rw [← h]; exact ⟨rfl, rfl⟩

lemma iUnion_Sset {m : ℕ} {η : ℝ} (hη : 0 < η) :
    (⋃ t ∈ (Finset.univ : Finset (QAlgorithms.Schur.Partition d m × Cells d η)), Sset η t) = Set.univ := by
  ext o; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨cellOf hη o, Finset.mem_univ _, (mem_Sset_iff hη o _).2 rfl⟩


section rnd
variable {m : ℕ} (hd : 0 < d) (hm : 0 < m) {η : ℝ} (hη : 0 < η)
def rep (t : QAlgorithms.Schur.Partition d m × Cells d η) : Mat d :=
  QAlgorithms.Schur.estimate hd hm t.1 (cellUnitary η t.2.1)

include hη in
lemma rest_measurable :
    Measurable (fun o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ =>
      QAlgorithms.Schur.estimate hd hm o.1 (roundUnitary η o.2)) := by
  intro S _
  have hset : (fun o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ =>
      QAlgorithms.Schur.estimate hd hm o.1 (roundUnitary η o.2)) ⁻¹' S =
      ⋃ t ∈ (Finset.univ.filter (fun t => rep hd hm t ∈ S)), Sset η t := by
    ext o
    simp only [Set.mem_preimage, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨cellOf hη o, h, (mem_Sset_iff hη o _).2 rfl⟩
    · rintro ⟨t, ht, ho⟩
      rw [mem_Sset_iff hη] at ho; rw [← ho] at ht; exact ht
  rw [hset]
  exact Finset.measurableSet_biUnion _ (fun t _ => Sset_measurable η t)


end rnd

lemma rtomo_eq {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (ρ : Mat d) (hρ : Density ρ) :
    roundedTomographyLaw m ρ hρ = Measure.map
      (fun o => QAlgorithms.Schur.estimate hd hm o.1 (roundUnitary (roundingMesh d m) o.2))
      (QAlgorithms.Tomography.keylJointLaw hd hm ρ hρ) := by
  simp [roundedTomographyLaw, hd, hm]

lemma mesh_pos (d m : ℕ) : 0 < roundingMesh d m := by unfold roundingMesh; positivity

lemma frob_triangle (a b c : Mat d) :
    QAlgorithms.frobNorm (a - c) ≤ QAlgorithms.frobNorm (a - b) + QAlgorithms.frobNorm (b - c) := by
  unfold QAlgorithms.frobNorm
  letI : NormedAddCommGroup (Mat d) := Matrix.frobeniusNormedAddCommGroup
  exact norm_sub_le_norm_sub_add_norm_sub a b c

lemma frob_le_entry (A : Mat d) {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, ‖A i j‖ ≤ c) :
    QAlgorithms.frobNorm A ≤ d * c := by
  unfold QAlgorithms.frobNorm
  rw [Matrix.frobenius_norm_def]
  have hs : ∑ i, ∑ j, ‖A i j‖ ^ (2:ℝ) ≤ ((d:ℝ) * c) ^ (2:ℝ) := by
    calc ∑ i, ∑ j, ‖A i j‖ ^ (2:ℝ) ≤ ∑ _i : Fin d, ∑ _j : Fin d, c ^ (2:ℝ) := by
          gcongr with i _ j _
          exact h i j
      _ = ((d:ℝ) * c) ^ (2:ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Real.mul_rpow (by positivity) hc, show ((d:ℝ))^(2:ℝ) = (d:ℝ) * d by
            rw [Real.rpow_two]; ring]
          ring
  calc (∑ i, ∑ j, ‖A i j‖ ^ (2:ℝ)) ^ (1/2:ℝ) ≤ (((d:ℝ) * c) ^ (2:ℝ)) ^ (1/2:ℝ) :=
        Real.rpow_le_rpow (by positivity) hs (by norm_num)
    _ = d * c := by rw [← Real.rpow_mul (by positivity)]; norm_num

lemma floor_close {a b η : ℝ} (hη : 0 < η) (h : ⌊a / η⌋ = ⌊b / η⌋) : |a - b| < η := by
  have h1 := Int.floor_le (a/η)
  have h2 := Int.lt_floor_add_one (a/η)
  have h3 := Int.floor_le (b/η)
  have h4 := Int.lt_floor_add_one (b/η)
  rw [h] at h1 h2
  have : |a/η - b/η| < 1 := by rw [abs_lt]; constructor <;> linarith
  rw [← sub_div, abs_div, abs_of_pos hη, div_lt_one hη] at this
  exact this

lemma roundUnitary_cell (η : ℝ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    gridCell η ((roundUnitary η U : Matrix.unitaryGroup (Fin d) ℂ) : Mat d) = gridCell η (U : Mat d) := by
  unfold roundUnitary cellUnitary
  have hex : ∃ V : Matrix.unitaryGroup (Fin d) ℂ, gridCell η (V : Mat d) = gridCell η (U : Mat d) := ⟨U, rfl⟩
  rw [dif_pos hex]
  exact hex.choose_spec

lemma roundUnitary_entry {η : ℝ} (hη : 0 < η) (U : Matrix.unitaryGroup (Fin d) ℂ) (i j : Fin d) :
    ‖((roundUnitary η U : Matrix.unitaryGroup (Fin d) ℂ) : Mat d) i j - (U : Mat d) i j‖ ≤ 2 * η := by
  have hc := congrFun (congrFun (roundUnitary_cell η U) i) j
  simp only [gridCell, Prod.mk.injEq] at hc
  have h1 := floor_close hη hc.1
  have h2 := floor_close hη hc.2
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im]; linarith

lemma rows_le_one {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (lam : QAlgorithms.Schur.Partition d n) (k : Fin d) :
    0 ≤ QAlgorithms.Schur.normalizedRows hd hn lam k ∧ QAlgorithms.Schur.normalizedRows hd hn lam k ≤ 1 := by
  unfold QAlgorithms.Schur.normalizedRows
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hn']
  have h1 := yd_card lam.val d lam.2.2
  rw [lam.2.1] at h1
  have : lam.val.rowLen k.val ≤ n :=
    (Finset.single_le_sum (f := fun i => lam.val.rowLen i) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.2 k.2)).trans (le_of_eq h1.symm)
  exact_mod_cast this

lemma round_err {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {η : ℝ} (hη : 0 < η)
    (o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ) :
    QAlgorithms.frobNorm (QAlgorithms.Schur.estimate hd hm o.1 (roundUnitary η o.2) -
      QAlgorithms.Schur.estimate hd hm o.1 o.2) ≤ 4 * d^2 * η := by
  set U := (o.2 : Mat d)
  set V := ((roundUnitary η o.2 : Matrix.unitaryGroup (Fin d) ℂ) : Mat d)
  have hU : ∀ i j, ‖U i j‖ ≤ 1 := fun i j => entry_norm_bound_of_unitary o.2.2 i j
  have hV : ∀ i j, ‖V i j‖ ≤ 1 := fun i j => entry_norm_bound_of_unitary (roundUnitary η o.2).2 i j
  have hVU : ∀ i j, ‖V i j - U i j‖ ≤ 2 * η := fun i j => roundUnitary_entry hη o.2 i j
  have hent : ∀ a b, ‖(QAlgorithms.Schur.estimate hd hm o.1 (roundUnitary η o.2) -
      QAlgorithms.Schur.estimate hd hm o.1 o.2) a b‖ ≤ 4 * d * η := by
    intro a b
    simp only [QAlgorithms.Schur.estimate, QAlgorithms.Schur.normalizedDiagram, Matrix.sub_apply,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖V a k * ((QAlgorithms.Schur.normalizedRows hd hm o.1 k : ℝ) : ℂ) * star (V b k) -
            U a k * ((QAlgorithms.Schur.normalizedRows hd hm o.1 k : ℝ) : ℂ) * star (U b k)‖
        ≤ ∑ _k : Fin d, 4 * η := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          obtain ⟨h0, h1⟩ := rows_le_one hd hm o.1 k
          set r := QAlgorithms.Schur.normalizedRows hd hm o.1 k
          have e : V a k * (r : ℂ) * star (V b k) - U a k * (r : ℂ) * star (U b k) =
              (r : ℂ) * (V a k * (star (V b k) - star (U b k)) + (V a k - U a k) * star (U b k)) := by ring
          rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
          have hs1 : ‖star (V b k) - star (U b k)‖ ≤ 2 * η := by
            rw [← star_sub, norm_star]; exact hVU b k
          have hb1 : ‖V a k * (star (V b k) - star (U b k)) + (V a k - U a k) * star (U b k)‖ ≤ 4 * η := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_star]
            have := mul_le_mul (hV a k) hs1 (norm_nonneg _) zero_le_one
            have := mul_le_mul (hVU a k) (hU b k) (norm_nonneg _) (by linarith)
            linarith
          calc r * ‖V a k * (star (V b k) - star (U b k)) + (V a k - U a k) * star (U b k)‖ ≤ 1 * (4 * η) :=
                mul_le_mul h1 hb1 (norm_nonneg _) zero_le_one
            _ = 4 * η := one_mul _
      _ = 4 * d * η := by simp; ring
  calc _ ≤ d * (4 * d * η) := frob_le_entry _ (by positivity) hent
    _ = 4 * d^2 * η := by ring

lemma rest_meas {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    Measurable (fun o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ =>
      QAlgorithms.Schur.estimate hd hm o.1 (roundUnitary (roundingMesh d m) o.2)) :=
  rest_measurable hd hm (mesh_pos d m)

lemma rtomo_univ {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (ρ : Mat d) (hρ : Density ρ) :
    roundedTomographyLaw m ρ hρ Set.univ = 1 := by
  rw [rtomo_eq hd hm, Measure.map_apply (rest_meas hd hm) MeasurableSet.univ,
    Set.preimage_univ, kjl_univ]

/-- Markov plus normalization for the rounded law -/
lemma rtomo_good {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (ρ : Mat d) (hρ : Density ρ)
    (G : Set (Mat d)) (hG : MeasurableSet G) {t : ℝ} (ht : 0 < t)
    (hsub : ∀ o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ,
      QAlgorithms.frobNorm (QAlgorithms.Schur.estimate hd hm o.1 o.2 - ρ) ^ 2 < t →
        QAlgorithms.Schur.estimate hd hm o.1 (roundUnitary (roundingMesh d m) o.2) ∈ G) :
    1 - ENNReal.ofReal ((4 * d - 3) / m) / ENNReal.ofReal t ≤ roundedTomographyLaw m ρ hρ G := by
  set F := {a : Mat d | t ≤ QAlgorithms.frobNorm (a - ρ) ^ 2}
  have hF : MeasurableSet F := (isClosed_le continuous_const ((frob_cont ρ).pow 2)).measurableSet
  have hmark : tomographyLaw m ρ hρ F ≤ ENNReal.ofReal ((4 * d - 3) / m) / ENNReal.ofReal t := by
    have h := meas_ge_le_lintegral_div
      (ENNReal.measurable_ofReal.comp ((frob_cont ρ).pow 2).measurable).aemeasurable
      (μ := tomographyLaw m ρ hρ) (ε := ENNReal.ofReal t) (by simpa using ht) ENNReal.ofReal_ne_top
    refine le_trans (le_trans (measure_mono ?_) h) (ENNReal.div_le_div_right (tomo_risk hd hm ρ hρ) _)
    intro a ha
    simp only [Set.mem_ofPred_eq, F] at ha ⊢
    exact ENNReal.ofReal_le_ofReal ha
  have hcompl : tomographyLaw m ρ hρ Fᶜ ≤ roundedTomographyLaw m ρ hρ G := by
    rw [tomo_eq hd hm, Measure.map_apply (est_measurable hd hm) hF.compl,
      rtomo_eq hd hm, Measure.map_apply (rest_meas hd hm) hG]
    apply measure_mono
    intro o ho
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, F] at ho ⊢
    exact hsub o ho
  have hprob : tomographyLaw m ρ hρ Fᶜ = 1 - tomographyLaw m ρ hρ F := by
    have : IsProbabilityMeasure (tomographyLaw m ρ hρ) := ⟨tomo_univ hd hm ρ hρ⟩
    exact prob_compl_eq_one_sub hF
  calc 1 - ENNReal.ofReal ((4 * d - 3) / m) / ENNReal.ofReal t ≤ 1 - tomographyLaw m ρ hρ F :=
        tsub_le_tsub_left hmark 1
    _ = tomographyLaw m ρ hρ Fᶜ := hprob.symm
    _ ≤ _ := hcompl

/-- a rounded report is close to the report -/
lemma rround_close {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (X : Mat d) {t : ℝ} (ht : 0 < t)
    (hmt : 1 / (2^8 * (m:ℝ)) ≤ Real.sqrt t / 2)
    (o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ)
    (ho : QAlgorithms.frobNorm (QAlgorithms.Schur.estimate hd hm o.1 o.2 - X) ^ 2 < t / 4) :
    QAlgorithms.frobNorm (QAlgorithms.Schur.estimate hd hm o.1 (roundUnitary (roundingMesh d m) o.2) - X) ^ 2 ≤ t := by
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have h1 := round_err hd hm (mesh_pos d m) o
  have h2 : 4 * (d:ℝ)^2 * roundingMesh d m ≤ 1 / (2^8 * (m:ℝ)) := by
    unfold roundingMesh
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hd1 : (d:ℝ)^2 ≤ ((d:ℝ) + 1)^2 := by have := (Nat.cast_nonneg d : (0:ℝ) ≤ d); nlinarith
    have hA : (d:ℝ)^2 * m ≤ ((d:ℝ)+1)^2 * ((m:ℝ)+1) :=
      mul_le_mul hd1 (by linarith) (by positivity) (by positivity)
    nlinarith [hA]
  have hst : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have h3 : QAlgorithms.frobNorm (QAlgorithms.Schur.estimate hd hm o.1 o.2 - X) < Real.sqrt t / 2 := by
    have hsq : Real.sqrt (t/4) = Real.sqrt t / 2 := by
      rw [Real.sqrt_div' t (by norm_num : (0:ℝ) ≤ 4), show (4:ℝ) = 2^2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [← hsq]
    exact Real.lt_sqrt_of_sq_lt ho
  have h4 := frob_triangle (QAlgorithms.Schur.estimate hd hm o.1 (roundUnitary (roundingMesh d m) o.2))
    (QAlgorithms.Schur.estimate hd hm o.1 o.2) X
  have h5 : QAlgorithms.frobNorm (QAlgorithms.Schur.estimate hd hm o.1 (roundUnitary (roundingMesh d m) o.2) - X)
      ≤ Real.sqrt t := by linarith
  have h0 : 0 ≤ QAlgorithms.frobNorm (QAlgorithms.Schur.estimate hd hm o.1 (roundUnitary (roundingMesh d m) o.2) - X) :=
    frob_nonneg _
  calc _ ≤ (Real.sqrt t)^2 := pow_le_pow_left₀ h0 h5 2
    _ = t := Real.sq_sqrt ht.le

/-! ### rate arithmetic -/

lemma logd_pos {d : ℕ} (hd : 2 ≤ d) : 0 < Real.log d :=
  Real.log_pos (by exact_mod_cast (by omega : 1 < d))

lemma rate_pos {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) : 0 < rate d ε := by
  have := logd_pos hd
  unfold rate; positivity

lemma rate_anti {d : ℕ} (hd : 2 ≤ d) {ε₁ ε₂ : ℝ} (h1 : 0 < ε₁) (h12 : ε₁ ≤ ε₂) :
    rate d ε₂ ≤ rate d ε₁ := by
  have hL := logd_pos hd
  unfold rate
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hsq : ε₁^2 * Real.log d ^ 2 ≤ ε₂^2 * Real.log d ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (by positivity); nlinarith
  exact mul_le_mul hsq (max_le_max le_rfl hsq) (by positivity) (by positivity)

lemma rate_32 {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    rate d (1/32) ≤ 2^20 * rate d ε := by
  have hL := logd_pos hd
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (rate_anti hd hε hε1) (by norm_num))
  unfold rate
  set L := Real.log d
  have hm : max 1 (L^2) / 1024 ≤ max 1 ((1/32)^2 * L^2) := by
    rcases le_total 1 (L^2) with h | h
    · rw [max_eq_right h]; refine le_trans ?_ (le_max_right _ _); nlinarith
    · rw [max_eq_left h]; refine le_trans ?_ (le_max_left _ _); norm_num
  rw [show (2:ℝ)^20 * ((d:ℝ)^2 / (1^2 * L^2 * max 1 (1^2 * L^2))) =
    (d:ℝ)^2 / (L^2 * max 1 (L^2) / 2^20) by field_simp]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have : L^2 * max 1 (L^2) / 2^20 = (1/32)^2 * L^2 * (max 1 (L^2) / 1024) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left hm (by positivity)

lemma log_six {d : ℕ} (hd : 2 ≤ d) : Real.log d ^ 6 ≤ 6^6 * d := by
  have h := Real.log_le_rpow_div (x := d) (by positivity) (by norm_num : (0:ℝ) < 1/6)
  have hL := logd_pos hd
  have h2 : Real.log d ≤ 6 * (d:ℝ) ^ ((1:ℝ)/6) := by
    rw [div_eq_mul_inv, show ((1:ℝ)/6)⁻¹ = 6 by norm_num] at h; linarith
  have h3 := pow_le_pow_left₀ hL.le h2 6
  rw [mul_pow, ← Real.rpow_natCast ((d:ℝ) ^ ((1:ℝ)/6)), ← Real.rpow_mul (by positivity)] at h3
  norm_num at h3; linarith

lemma pow_le_one_add {L : ℝ} (hL : 0 ≤ L) {k : ℕ} (hk : k ≤ 6) : L^k ≤ 1 + L^6 := by
  rcases le_total L 1 with h | h
  · have := pow_le_one₀ hL h (n := k); have : 0 ≤ L^6 := by positivity
    linarith
  · have := pow_le_pow_right₀ h hk; linarith

lemma rate_lower {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/32) :
    1024 * (d:ℝ)^2 / (Real.log d ^ 2 + Real.log d ^ 4) ≤ rate d ε := by
  have hL := logd_pos hd
  set L := Real.log d
  unfold rate
  rw [show 1024 * (d:ℝ)^2 / (L^2 + L^4) = (d:ℝ)^2 / ((L^2 + L^4) / 1024) by field_simp]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have he2 : ε^2 ≤ 1/1024 := by nlinarith
  have hm : max 1 (ε^2 * L^2) ≤ 1 + ε^2 * L^2 := by
    apply max_le <;> nlinarith [sq_nonneg (ε * L)]
  calc ε^2 * L^2 * max 1 (ε^2 * L^2) ≤ ε^2 * L^2 * (1 + ε^2 * L^2) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ = ε^2 * L^2 + (ε^2)^2 * L^4 := by ring
    _ ≤ (1/1024) * L^2 + (1/1024)^2 * L^4 := by
        gcongr
    _ ≤ (L^2 + L^4) / 1024 := by nlinarith [sq_nonneg (L^2)]


def Kt : ℝ := 2^40 * 6^6
def Ko : ℝ := 6^6

lemma L_facts {d : ℕ} (hd : 2 ≤ d) :
    Real.log d ^ 2 ≤ 1 + 6^6 * d ∧ Real.log d ^ 4 ≤ 1 + 6^6 * d ∧ Real.log d ^ 6 ≤ 6^6 * d := by
  have hL := (logd_pos hd).le
  have h6 := log_six hd
  exact ⟨(pow_le_one_add hL (by norm_num)).trans (by linarith),
    (pow_le_one_add hL (by norm_num)).trans (by linarith), h6⟩

lemma one_le_rate {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/32) :
    1 ≤ Ko * rate d ε := by
  have hr := rate_lower hd hε hε1
  obtain ⟨h2, h4, -⟩ := L_facts hd
  have hL := logd_pos hd
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hden : Real.log d ^ 2 + Real.log d ^ 4 ≤ (2 + 2 * 6^6) * (d:ℝ)^2 := by nlinarith
  have : 1024 / (2 + 2 * 6^6) ≤ 1024 * (d:ℝ)^2 / (Real.log d ^ 2 + Real.log d ^ 4) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  unfold Ko; nlinarith

lemma tomo_le {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/32) :
    (tomographyCount d : ℝ) ≤ Kt * rate d ε := by
  have hr := rate_lower hd hε hε1
  obtain ⟨h2, h4, h6⟩ := L_facts hd
  have hL := logd_pos hd
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hc : (tomographyCount d : ℝ) ≤ 2^40 * d * Real.log d ^ 2 + 1 := by
    unfold tomographyCount constructionC₀
    exact (Nat.ceil_lt_add_one (by positivity)).le
  refine hc.trans ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hr (by unfold Kt; positivity))
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  set L := Real.log d
  have hL2 : 0 ≤ L^2 := by positivity
  have e : (2^40 * d * L^2 + 1) * (L^2 + L^4) = 2^40 * d * L^4 + 2^40 * d * L^6 + L^2 + L^4 := by ring
  rw [e]; unfold Kt
  have hd2 : (d:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 2^40 * d),
    mul_le_mul_of_nonneg_left h6 (by positivity : (0:ℝ) ≤ 2^40 * d)]

def Kc (C₁ : ℝ) (d₀ : ℕ) : ℝ :=
  2^40 * Real.log d₀ ^ 2 * max 1 (Real.log d₀ ^ 2) + Kt + C₁ + 3 * Ko

lemma cost_le (C₁ : ℝ) (hC : 0 < C₁) (d₀ : ℕ) (hd₀ : 2 ≤ d₀) {d : ℕ} (hd : 2 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1/32) :
    (algorithmCost C₁ d₀ d ε : ℝ) ≤ Kc C₁ d₀ * rate d ε := by
  have hr := rate_pos hd hε
  have h1 := one_le_rate hd hε hε1
  have hKo : 0 ≤ Ko := by unfold Ko; positivity
  have hKt : 0 ≤ Kt := by unfold Kt; positivity
  have hL0 := logd_pos hd₀
  have hA : 0 ≤ 2^40 * Real.log d₀ ^ 2 * max 1 (Real.log d₀ ^ 2) := by positivity
  unfold algorithmCost Kc
  split_ifs with hlt
  · -- bounded branch
    have hc : (boundedCount d ε : ℝ) ≤ 2^40 * (d:ℝ)^2 / ε^2 + 1 := by
      unfold boundedCount constructionC₀
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have hL : Real.log d ≤ Real.log d₀ :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < d)) (by exact_mod_cast hlt.le)
    have hLd := logd_pos hd
    have hrate : (d:ℝ)^2 / (ε^2 * Real.log d₀ ^ 2 * max 1 (Real.log d₀ ^ 2)) ≤ rate d ε := by
      unfold rate
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have hsq : ε^2 * Real.log d ^ 2 ≤ ε^2 * Real.log d₀ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
      apply mul_le_mul hsq (max_le_max le_rfl (le_trans ?_ (by nlinarith : Real.log d ^ 2 ≤ Real.log d₀ ^ 2)))
        (by positivity) (by positivity)
      have : ε^2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (Real.log d)]
    have hmain : 2^40 * (d:ℝ)^2 / ε^2 ≤ 2^40 * Real.log d₀ ^ 2 * max 1 (Real.log d₀ ^ 2) * rate d ε := by
      refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hrate hA)
      field_simp
    have : (Kt + C₁ + 3 * Ko) * rate d ε ≥ 1 := by nlinarith
    nlinarith
  · push_cast
    have ht := tomo_le hd hε hε1
    have hf : (freshCount C₁ d ε : ℝ) ≤ C₁ * rate d ε + 1 := by
      unfold freshCount; exact (Nat.ceil_lt_add_one (by positivity)).le
    nlinarith


/-! ### spectral laws -/

section spec
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma tr_pure (R : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    (R * QAlgorithms.pureDensity v).trace = ∑ a, ∑ b, (starRingEnd ℂ) (v a) * R a b * v b := by
  simp only [Matrix.trace, Matrix.diag, mul_apply, QAlgorithms.pureDensity, Matrix.of_apply]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))

/-- weight of eigenvector i -/
def wt {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (R : Matrix ι ι ℂ) (i : ι) : ℝ :=
  (R * QAlgorithms.pureDensity (hG.eigenvectorBasis i)).trace.re

lemma wt_eq {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (R : Matrix ι ι ℂ) (i : ι) :
    ((R * QAlgorithms.pureDensity (hG.eigenvectorBasis i)).trace) =
      (star (hG.eigenvectorUnitary : Matrix ι ι ℂ) * R * (hG.eigenvectorUnitary : Matrix ι ι ℂ)) i i := by
  rw [tr_pure]
  simp only [mul_apply, Matrix.star_eq_conjTranspose, conjTranspose_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rfl

lemma tr_R_pow {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (R : Matrix ι ι ℂ) (k : ℕ) :
    (R * G ^ k).trace = ∑ i, (R * QAlgorithms.pureDensity (hG.eigenvectorBasis i)).trace *
      ((hG.eigenvalues i : ℂ) ^ k) := by
  set U := (hG.eigenvectorUnitary : Matrix ι ι ℂ)
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem (hG.eigenvectorUnitary).2
  have hspec : G = U * diagonal (fun i => ((hG.eigenvalues i : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [hG.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]; rfl
  have hpow : G ^ k = U * diagonal (fun i => ((hG.eigenvalues i : ℝ) : ℂ) ^ k) * star U := by
    induction k with
    | zero => simp; exact (Unitary.mul_star_self_of_mem (hG.eigenvectorUnitary).2).symm
    | succ k ih =>
      rw [pow_succ, ih]
      refine (congrArg (fun X => (U * diagonal (fun i => ((hG.eigenvalues i : ℝ) : ℂ) ^ k) * star U) * X)
        hspec).trans ?_
      calc U * diagonal (fun i => ((hG.eigenvalues i : ℝ) : ℂ) ^ k) * star U *
            (U * diagonal (fun i => ((hG.eigenvalues i : ℝ) : ℂ)) * star U)
          = U * diagonal (fun i => ((hG.eigenvalues i : ℝ) : ℂ) ^ k) * (star U * U) *
            diagonal (fun i => ((hG.eigenvalues i : ℝ) : ℂ)) * star U := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [hUU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]
          simp only [pow_succ]
  simp_rw [wt_eq hG R]
  rw [hpow, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, mul_diagonal]
  rfl

lemma sum_wt {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (R : Matrix ι ι ℂ) :
    ∑ i, wt hG R i = R.trace.re := by
  have := tr_R_pow hG R 0
  simp only [pow_zero, Matrix.mul_one, mul_one] at this
  rw [this, Complex.re_sum]; rfl

lemma spectralLaw_eq {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (R : Matrix ι ι ℂ) :
    spectralLaw G R = ∑ i, ENNReal.ofReal (wt hG R i) • Measure.dirac (hG.eigenvalues i) := by
  unfold spectralLaw; rw [dif_pos hG]; rfl

end spec


section cheb
variable {κ : Type*} [Fintype κ]

lemma atomic_apply (w lam : κ → ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    (∑ i, ENNReal.ofReal (w i) • Measure.dirac (lam i)) S =
      ∑ i, ENNReal.ofReal (w i) * S.indicator 1 (lam i) := by
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Measure.smul_apply, Measure.dirac_apply' _ hS, smul_eq_mul]

lemma atomic_bound (w lam : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (S : Set ℝ) (hS : MeasurableSet S)
    (e t : ℝ) (ht : 0 < t) (hsub : ∀ x, |x - e| ≤ t → x ∈ S) :
    ENNReal.ofReal (∑ i, w i - (∑ i, w i * (lam i - e)^2) / t^2) ≤
      (∑ i, ENNReal.ofReal (w i) • Measure.dirac (lam i)) S := by
  rw [atomic_apply w lam S hS]
  have hpt : ∀ i, w i * (1 - (lam i - e)^2 / t^2) ≤ w i * S.indicator 1 (lam i) := by
    intro i
    by_cases hg : |lam i - e| ≤ t
    · rw [Set.indicator_of_mem (hsub _ hg)]
      apply mul_le_mul_of_nonneg_left _ (hw i)
      have : 0 ≤ (lam i - e)^2 / t^2 := by positivity
      simp; linarith
    · push Not at hg
      have h1 : t^2 < (lam i - e)^2 := by
        rw [← sq_abs (lam i - e)]; exact pow_lt_pow_left₀ hg ht.le (by norm_num)
      have h2 : 1 < (lam i - e)^2 / t^2 := by rw [lt_div_iff₀ (by positivity)]; linarith
      have h3 : 0 ≤ w i * S.indicator 1 (lam i) := by
        apply mul_nonneg (hw i); unfold Set.indicator; split_ifs <;> norm_num
      nlinarith [hw i]
  calc ENNReal.ofReal (∑ i, w i - (∑ i, w i * (lam i - e)^2) / t^2)
      = ENNReal.ofReal (∑ i, w i * (1 - (lam i - e)^2 / t^2)) := by
        congr 1; rw [Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => by ring)
    _ ≤ ENNReal.ofReal (∑ i, w i * S.indicator 1 (lam i)) :=
        ENNReal.ofReal_le_ofReal (Finset.sum_le_sum (fun i _ => hpt i))
    _ = ∑ i, ENNReal.ofReal (w i) * S.indicator 1 (lam i) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i) (by
          unfold Set.indicator; split_ifs <;> norm_num))]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [ENNReal.ofReal_mul (hw i)]
        congr 1
        unfold Set.indicator; split_ifs <;> simp

lemma weights_nonneg (w : κ → ℝ) (h1 : ∑ i, ENNReal.ofReal (w i) = 1) (h2 : ∑ i, w i = 1) :
    ∀ i, 0 ≤ w i := by
  have h3 : ∑ i, max (w i) 0 = 1 := by
    have := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top)] at this
    simpa [ENNReal.toReal_ofReal'] using this
  have h4 : ∑ i, (max (w i) 0 - w i) = 0 := by rw [Finset.sum_sub_distrib, h3, h2, sub_self]
  have h5 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by
    have := le_max_left (w i) 0; linarith)).mp h4
  intro i
  have := h5 i (Finset.mem_univ i)
  have := le_max_right (w i) 0
  linarith

lemma atomic_integral (w lam : κ → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∫ x, x ∂(∑ i, ENNReal.ofReal (w i) • Measure.dirac (lam i)) = ∑ i, w i * lam i := by
  rw [integral_finset_sum_measure (fun i _ => (integrable_dirac (by simp)).smul_measure
    ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i), smul_eq_mul]

end cheb


section inner
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma tr_re_pow {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (R : Matrix ι ι ℂ) (k : ℕ) :
    (R * G ^ k).trace.re = ∑ i, wt hG R i * hG.eigenvalues i ^ k := by
  rw [tr_R_pow hG R k, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rfl

lemma inner_bound {G R : Matrix ι ι ℂ} (hG : G.IsHermitian) (hR : R.trace.re = 1)
    (huniv : spectralLaw G R Set.univ = 1) {e : ℝ} (he : ∫ x, x ∂(spectralLaw G R) = e)
    {v : ℝ} (hv : (R * G ^ 2).trace.re - ((R * G).trace.re) ^ 2 ≤ v)
    {t : ℝ} (ht : 0 < t) (S : Set ℝ) (hS : MeasurableSet S) (hsub : ∀ x, |x - e| ≤ t → x ∈ S) :
    ENNReal.ofReal (1 - v / t^2) ≤ spectralLaw G R S := by
  set w := wt hG R
  set lam := hG.eigenvalues
  have hμ := spectralLaw_eq hG R
  have hsum : ∑ i, w i = 1 := by rw [sum_wt, hR]
  have huniv' : ∑ i, ENNReal.ofReal (w i) = 1 := by
    rw [hμ, atomic_apply _ _ _ MeasurableSet.univ] at huniv
    simpa using huniv
  have hw := weights_nonneg w huniv' hsum
  have he' : ∑ i, w i * lam i = e := by rw [← he, hμ, atomic_integral w lam hw]
  have h1 : (R * G).trace.re = ∑ i, w i * lam i := by
    have := tr_re_pow hG R 1; simpa using this
  have h2 : (R * G ^ 2).trace.re = ∑ i, w i * lam i ^ 2 := tr_re_pow hG R 2
  have hV : ∑ i, w i * (lam i - e)^2 = (R * G ^ 2).trace.re - ((R * G).trace.re) ^ 2 := by
    rw [h1, h2, he']
    have : ∑ i, w i * (lam i - e)^2 = ∑ i, w i * lam i ^ 2 - 2 * e * ∑ i, w i * lam i + e^2 * ∑ i, w i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [this, he', hsum]; ring
  rw [hμ]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (atomic_bound w lam hw S hS e t ht hsub)
  rw [hsum, hV]
  have : ((R * G ^ 2).trace.re - ((R * G).trace.re) ^ 2) / t^2 ≤ v / t^2 :=
    div_le_div_of_nonneg_right hv (by positivity)
  linarith

end inner


lemma trace_powerState {ι : Type*} [Fintype ι] (τ : Matrix ι ι ℂ) (n : ℕ) :
    (powerState τ n).trace = τ.trace ^ n := by
  simp only [powerState, tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.trace, Matrix.diag,
    Matrix.of_apply]
  have h := Fintype.prod_sum (fun (_ : Fin n) (i : ι) => τ i i)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [h]

lemma trace_labelled {d : ℕ} {ρ σ : Mat d} (hρ : Density ρ) (hσ : Density σ) :
    (labelledState ρ σ).trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, labelledState, if_true, Fintype.sum_prod_type,
    Fintype.sum_bool, if_false, Bool.false_eq_true]
  have h1 := hρ.2; have h2 := hσ.2
  simp only [Matrix.trace, Matrix.diag] at h1 h2
  rw [← Finset.mul_sum, ← Finset.mul_sum, h1, h2]; norm_num


/-! ### assembly: small accuracy -/

lemma clip_close {x D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1) : |clip x - D| ≤ |x - D| := by
  unfold clip
  rcases le_total x 0 with h | h
  · rw [max_eq_left h, min_eq_right zero_le_one, abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]; linarith
  · rw [max_eq_right h]
    rcases le_total x 1 with h' | h'
    · rw [min_eq_right h']
    · rw [min_eq_left h', abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

lemma frob_sub_comm (a b : Mat d) : QAlgorithms.frobNorm (a - b) = QAlgorithms.frobNorm (b - a) := by
  unfold QAlgorithms.frobNorm
  rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def]
  congr 1; refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Matrix.sub_apply, Matrix.sub_apply, norm_sub_rev]

lemma herm_closed : IsClosed {a : Mat d | a.IsHermitian} := isClosed_eq (by fun_prop) (by fun_prop)

lemma outcome_univ {N : ℕ} (M : TwoStateMeasurement d N) (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ) :
    outcomeLaw M ρ σ hρ hσ Set.univ = 1 := by
  rw [outcomeLaw, QAlgorithms.Measurements.bornLaw_apply _ _ _ _ MeasurableSet.univ, M.total]
  simp [QAlgorithms.effectProb, (jointInput_density N ρ σ hρ hσ).2]

lemma ennreal_prod_bound {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : 2/3 ≤ x * y) {A B : ℝ≥0∞}
    (hA : ENNReal.ofReal x ≤ A) (hB : ENNReal.ofReal y ≤ B) : ENNReal.ofReal (2/3) ≤ A * B := by
  calc ENNReal.ofReal (2/3) ≤ ENNReal.ofReal (x * y) := ENNReal.ofReal_le_ofReal hxy
    _ = ENNReal.ofReal x * ENNReal.ofReal y := ENNReal.ofReal_mul hx
    _ ≤ A * B := mul_le_mul' hA hB

lemma one_sub_ofReal {x : ℝ} (hx : 0 ≤ x) : 1 - ENNReal.ofReal x = ENNReal.ofReal (1 - x) := by
  rw [ENNReal.ofReal_sub 1 hx, ENNReal.ofReal_one]

lemma bounded_branch {d₀ d : ℕ} (hd : 2 ≤ d) (hlt : d < d₀) (C₁ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1/32) (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ) :
    ENNReal.ofReal (2/3) ≤ roundedAlgorithmWeight C₁ d₀ ε ρ σ hρ hσ {x | |x - distance ρ σ| ≤ ε} := by
  rw [roundedAlgorithmWeight, if_pos hlt]
  set m := boundedCount d ε with hmdef
  have hdpos : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hmge : 2^40 * (d:ℝ)^2 / ε^2 ≤ m := Nat.le_ceil _
  have hmpos' : (0:ℝ) < m := lt_of_lt_of_le (by positivity) hmge
  have hm : 0 < m := by exact_mod_cast hmpos'
  have hd0 : 0 < d := by omega
  set t := ε^2 / d with htdef
  have ht : 0 < t := by positivity
  let G : Mat d → Set (Mat d) := fun X => {a | a.IsHermitian ∧ QAlgorithms.frobNorm (a - X) ^ 2 ≤ t}
  have hGm : ∀ X, MeasurableSet (G X) := fun X =>
    (herm_closed.inter (isClosed_le ((frob_cont X).pow 2) continuous_const)).measurableSet
  have ht4 : 0 < t / 4 := by positivity
  have hrat : ENNReal.ofReal ((4 * d - 3) / m) / ENNReal.ofReal (t / 4) ≤ ENNReal.ofReal (16 / 2^40) := by
    rw [← ENNReal.ofReal_div_of_pos ht4]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ ht4, div_le_iff₀ hmpos']
    have : 2^40 * (d:ℝ)^2 ≤ m * ε^2 := by rwa [div_le_iff₀ (by positivity)] at hmge
    rw [htdef]
    have : (4 * d - 3) ≤ 4 * (d:ℝ) := by linarith
    have hfin : 16 / 2^40 * (ε^2 / d / 4) * m = 4 * (m * ε^2) / (2^40 * d) := by field_simp; ring
    rw [hfin, le_div_iff₀ (by positivity)]; nlinarith
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one hdpos]
    have : ε^2 ≤ 1 := by nlinarith
    have : (1:ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    linarith
  have hmt : 1 / (2^8 * (m:ℝ)) ≤ Real.sqrt t / 2 := by
    have hts : t ≤ Real.sqrt t := by
      have := Real.sqrt_le_one.mpr ht1
      nlinarith [Real.mul_self_sqrt ht.le, Real.sqrt_nonneg t]
    have : 1 / (2^8 * (m:ℝ)) ≤ t / 2 := by
      have h2 : 2^40 * (d:ℝ)^2 ≤ m * ε^2 := by rwa [div_le_iff₀ (by positivity)] at hmge
      rw [htdef, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
      nlinarith
    linarith
  have hGX : ∀ X (hX : Density X), ENNReal.ofReal (1 - 16 / 2^40) ≤ roundedTomographyLaw m X hX (G X) := by
    intro X hX
    rw [← one_sub_ofReal (by positivity)]
    refine le_trans (tsub_le_tsub_left hrat 1) (rtomo_good hd0 hm X hX (G X) (hGm X) ht4 ?_)
    intro o ho
    exact ⟨(est_density hd0 hm o.1 _).1.1, rround_close hd0 hm X ht hmt o ho⟩
  have hdist : ∀ a ∈ G ρ, ∀ b ∈ G σ, |distance a b - distance ρ σ| ≤ ε := by
    intro a ha b hb
    have hρa := traceNorm_le_frob (ha.1.sub hρ.1.1)
    have hσb := traceNorm_le_frob (hb.1.sub hσ.1.1)
    have hfa : QAlgorithms.frobNorm (a - ρ) ≤ ε / Real.sqrt d := by
      rw [← Real.sqrt_sq (frob_nonneg _), div_eq_mul_inv, ← Real.sqrt_inv,
        ← Real.sqrt_sq hε.le, ← Real.sqrt_mul (sq_nonneg _)]
      exact Real.sqrt_le_sqrt (by rw [← div_eq_mul_inv]; exact ha.2)
    have hfb : QAlgorithms.frobNorm (b - σ) ≤ ε / Real.sqrt d := by
      rw [← Real.sqrt_sq (frob_nonneg _), div_eq_mul_inv, ← Real.sqrt_inv,
        ← Real.sqrt_sq hε.le, ← Real.sqrt_mul (sq_nonneg _)]
      exact Real.sqrt_le_sqrt (by rw [← div_eq_mul_inv]; exact hb.2)
    have hsq : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
    have h1 : QAlgorithms.traceNorm (a - ρ) ≤ ε := by
      calc _ ≤ Real.sqrt d * QAlgorithms.frobNorm (a - ρ) := hρa
        _ ≤ Real.sqrt d * (ε / Real.sqrt d) := mul_le_mul_of_nonneg_left hfa hsq.le
        _ = ε := by field_simp
    have h2 : QAlgorithms.traceNorm (b - σ) ≤ ε := by
      calc _ ≤ Real.sqrt d * QAlgorithms.frobNorm (b - σ) := hσb
        _ ≤ Real.sqrt d * (ε / Real.sqrt d) := mul_le_mul_of_nonneg_left hfb hsq.le
        _ = ε := by field_simp
    have hab := ha.1.sub hb.1
    have hrs := hρ.1.1.sub hσ.1.1
    have e1 : a - b = (ρ - σ) + ((a - ρ) + -(b - σ)) := by abel
    have e2 : ρ - σ = (a - b) + (-(a - ρ) + (b - σ)) := by abel
    have t1 := traceNorm_add_le hrs ((ha.1.sub hρ.1.1).add (hb.1.sub hσ.1.1).neg)
    have t2 := traceNorm_add_le (ha.1.sub hρ.1.1) (hb.1.sub hσ.1.1).neg
    have t3 := traceNorm_add_le hab ((ha.1.sub hρ.1.1).neg.add (hb.1.sub hσ.1.1))
    have t4 := traceNorm_add_le (ha.1.sub hρ.1.1).neg (hb.1.sub hσ.1.1)
    rw [← e1] at t1; rw [← e2] at t3
    rw [traceNorm_neg] at t2 t4
    unfold distance
    rw [abs_le]; constructor <;> linarith
  -- lower bound of the double integral
  have hinner : ∀ a, (G ρ).indicator (fun _ => roundedTomographyLaw m σ hσ (G σ)) a ≤
      ∫⁻ b, (if distance a b ∈ {x | |x - distance ρ σ| ≤ ε} then 1 else 0) ∂roundedTomographyLaw m σ hσ := by
    intro a
    by_cases ha : a ∈ G ρ
    · rw [Set.indicator_of_mem ha, ← lintegral_indicator_one (hGm σ)]
      refine lintegral_mono (fun b => ?_)
      by_cases hb : b ∈ G σ
      · have h1 : distance a b ∈ {x | |x - distance ρ σ| ≤ ε} := hdist a ha b hb
        rw [Set.indicator_of_mem hb, if_pos h1]; rfl
      · rw [Set.indicator_of_notMem hb]; exact zero_le'
    · rw [Set.indicator_of_notMem ha]; exact zero_le'
  calc ENNReal.ofReal (2/3) ≤ roundedTomographyLaw m σ hσ (G σ) * roundedTomographyLaw m ρ hρ (G ρ) :=
        ennreal_prod_bound (by norm_num) (by norm_num) (by norm_num) (hGX σ hσ) (hGX ρ hρ)
    _ = ∫⁻ a, (G ρ).indicator (fun _ => roundedTomographyLaw m σ hσ (G σ)) a ∂roundedTomographyLaw m ρ hρ := by
        rw [lintegral_indicator_const (hGm ρ)]
    _ ≤ _ := lintegral_mono hinner

lemma main_branch {d₀ d : ℕ} (hd : 2 ≤ d) (hge : d₀ ≤ d) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (h32 : ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/32 →
      ∀ ρ σ : Mat d, Density ρ → Density σ → ∀ Q : Mat d, projector Q →
      ∀ n : ℕ, C₁*rate d ε ≤ (n : ℝ) →
        expressionDegree (f d ε Q) ≤ n ∧
        (opNorm (compress Q (plus ρ σ)) ≤ 1/Real.log d →
          polynomialVariance (f d ε Q) n ρ σ ≤ ε^2/64))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/32) (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ) :
    ENNReal.ofReal (2/3) ≤ roundedAlgorithmWeight C₁ d₀ ε ρ σ hρ hσ {x | |x - distance ρ σ| ≤ ε} := by
  have hP := plus_density hρ hσ
  rw [roundedAlgorithmWeight, if_neg (not_lt.mpr hge)]
  simp only
  rw [dif_pos hP]
  set D := distance ρ σ
  set B := {x : ℝ | |x - D| ≤ ε}
  set n := freshCount C₁ d ε
  set m₀ := tomographyCount d
  have hd0 : 0 < d := by omega
  have hL := logd_pos hd
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd0
  have hm₀ge : 2^40 * (d:ℝ) * Real.log d ^ 2 ≤ m₀ := Nat.le_ceil _
  have hm₀pos' : (0:ℝ) < m₀ := lt_of_lt_of_le (by positivity) hm₀ge
  have hm₀ : 0 < m₀ := by exact_mod_cast hm₀pos'
  set t := (1 / (2 * Real.log d))^2 with htdef
  have ht : 0 < t := by positivity
  let G : Set (Mat d) := {a | Density a ∧ QAlgorithms.frobNorm (a - plus ρ σ) ^ 2 ≤ t}
  have hGm : MeasurableSet G :=
    ((density_closed d).inter (isClosed_le ((frob_cont _).pow 2) continuous_const)).measurableSet
  have ht4 : 0 < t / 4 := by positivity
  have hrat : ENNReal.ofReal ((4 * d - 3) / m₀) / ENNReal.ofReal (t / 4) ≤ ENNReal.ofReal (64 / 2^40) := by
    rw [← ENNReal.ofReal_div_of_pos ht4]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ ht4, div_le_iff₀ hm₀pos', htdef]
    have hfin : 64 / 2^40 * ((1 / (2 * Real.log d))^2 / 4) * m₀ = 4 * m₀ / (2^40 * Real.log d ^ 2) := by
      field_simp; ring
    rw [hfin, le_div_iff₀ (by positivity)]; nlinarith
  have hlog2 : (1/2 : ℝ) < Real.log d := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) (by exact_mod_cast hd)
    linarith
  have ht1 : t ≤ 1 := by
    rw [htdef, div_pow, one_pow, div_le_one (by positivity)]; nlinarith
  have hmt : 1 / (2^8 * (m₀:ℝ)) ≤ Real.sqrt t / 2 := by
    have hts : t ≤ Real.sqrt t := by
      have := Real.sqrt_le_one.mpr ht1
      nlinarith [Real.mul_self_sqrt ht.le, Real.sqrt_nonneg t]
    have : 1 / (2^8 * (m₀:ℝ)) ≤ t / 2 := by
      have he : t / 2 = 1 / (8 * Real.log d ^ 2) := by rw [htdef]; field_simp; ring
      rw [he]
      refine one_div_le_one_div_of_le (by positivity) ?_
      have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
      nlinarith [sq_nonneg (Real.log d)]
    linarith
  have hGT : ENNReal.ofReal (1 - 64 / 2^40) ≤ roundedTomographyLaw m₀ (plus ρ σ) hP G := by
    rw [← one_sub_ofReal (by positivity)]
    refine le_trans (tsub_le_tsub_left hrat 1) (rtomo_good hd0 hm₀ _ hP G hGm ht4 ?_)
    intro o ho
    exact ⟨est_density hd0 hm₀ o.1 _, rround_close hd0 hm₀ _ ht hmt o ho⟩
  -- the inner probability on good reports
  have hinner : ∀ a ∈ G, ENNReal.ofReal (35/36) ≤
      spectralLaw (observable (f d ε (reportProjector d a)) n)
        (powerState (labelledState ρ σ) n) (clip ⁻¹' B) := by
    intro a ha
    have hQ := rp_projector (d := d) ha.1.1.1
    set Q := reportProjector d a
    have hrank := rank_one_sub_rp ha.1 hd
    have hfr : QAlgorithms.frobNorm (plus ρ σ - a) ≤ 1 / (2 * Real.log d) := by
      rw [frob_sub_comm, ← Real.sqrt_sq (frob_nonneg _), ← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1 / (2 * Real.log d))]
      exact Real.sqrt_le_sqrt ha.2
    have hclose : opNorm (plus ρ σ - a) ≤ 1 / (2 * Real.log d) :=
      (opNorm_le_frob (hP.1.1.sub ha.1.1.1)).trans hfr
    have hnorm := opNorm_compress_rp ha.1 hP.1.1 hd hclose
    have hn : C₁ * rate d ε ≤ (n : ℝ) := Nat.le_ceil _
    obtain ⟨hdeg, hvar⟩ := h32 d hge ε hε hε1 ρ σ hρ hσ Q hQ n hn
    have hvar' := hvar hnorm
    have hn0 : 0 < n := by
      have : (0:ℝ) < n := lt_of_lt_of_le (mul_pos hC₁ (rate_pos hd hε)) hn
      exact_mod_cast this
    obtain ⟨hHerm, -, M', hM'⟩ := proposition_2_7 d n hd0 hn0 (f d ε Q) (realOnHermitian_f d ε hQ) hdeg
    obtain ⟨hlaw, -, hmean⟩ := hM' ρ σ hρ hσ
    have huniv : spectralLaw (observable (f d ε Q) n) (powerState (labelledState ρ σ) n) Set.univ = 1 := by
      rw [← hlaw]; exact outcome_univ M' ρ σ hρ hσ
    have hbias := proposition_3_1 d hd ε hε hε1 ρ σ hρ hσ Q hQ hrank
    have hR : (powerState (labelledState ρ σ) n).trace.re = 1 := by
      rw [trace_powerState, trace_labelled hρ hσ, one_pow, Complex.one_re]
    have hv : (powerState (labelledState ρ σ) n * (observable (f d ε Q) n) ^ 2).trace.re -
        ((powerState (labelledState ρ σ) n * observable (f d ε Q) n).trace.re) ^ 2 ≤ ε^2/64 := hvar'
    have hS : MeasurableSet (clip ⁻¹' B) := by
      have hc : Continuous clip := by unfold clip; fun_prop
      exact hc.measurable (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const))
        continuous_const).measurableSet
    have hD0 := distance_nonneg ρ σ hρ hσ
    have hD1 := distance_le_one ρ σ hρ hσ
    have hsub : ∀ x, |x - (evaluate (f d ε Q) (plus ρ σ) (minus ρ σ)).re| ≤ 3 * ε / 4 → x ∈ clip ⁻¹' B := by
      intro x hx
      show |clip x - D| ≤ ε
      refine (clip_close hD0 hD1).trans ?_
      have := abs_sub_le x (evaluate (f d ε Q) (plus ρ σ) (minus ρ σ)).re D
      linarith
    have hb := inner_bound hHerm hR huniv hmean hv (by positivity : (0:ℝ) < 3 * ε / 4) _ hS hsub
    have : (1 : ℝ) - ε^2/64 / (3 * ε / 4)^2 = 35/36 := by field_simp; ring
    rwa [this] at hb
  calc ENNReal.ofReal (2/3) ≤ ENNReal.ofReal (35/36) * roundedTomographyLaw m₀ (plus ρ σ) hP G :=
        ennreal_prod_bound (by norm_num) (by norm_num) (by norm_num) le_rfl hGT
    _ = ∫⁻ a, G.indicator (fun _ => ENNReal.ofReal (35/36)) a ∂roundedTomographyLaw m₀ (plus ρ σ) hP := by
        rw [lintegral_indicator_const hGm]
    _ ≤ _ := by
        refine lintegral_mono (fun a => ?_)
        by_cases ha : a ∈ G
        · rw [Set.indicator_of_mem ha]; exact hinner a ha
        · rw [Set.indicator_of_notMem ha]; exact zero_le'

lemma Kc_pos (C₁ : ℝ) (hC : 0 < C₁) (d₀ : ℕ) : 0 < Kc C₁ d₀ := by
  unfold Kc Kt Ko; positivity

end OTDRoot

open OptimalTraceDistance.Estimation OTDRoot in
theorem solution : ∃ C : ℝ, 0 < C ∧
  (∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, N ≤ ⌈C*rate d ε⌉₊ ∧ ∃ M : TwoStateMeasurement d N,
      ∀ (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ),
        ENNReal.ofReal (2/3 : ℝ) ≤
          outcomeLaw M ρ σ hρ hσ {x | |x-distance ρ σ| ≤ ε}) ∧
  (∃ M : TwoStateMeasurement 1 0, ∀ (ρ σ : Mat 1) (hρ : Density ρ) (hσ : Density σ),
    distance ρ σ = 0 ∧ outcomeLaw M ρ σ hρ hσ = Measure.dirac 0) := by
  obtain ⟨d₀, hd₀, C₂, hC₂, h32⟩ := proposition_3_2
  have hK := Kc_pos C₂ hC₂ d₀
  refine ⟨2^20 * Kc C₂ d₀, by positivity, ?_, ?_⟩
  · -- small accuracy
    have small : ∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/32 →
        ∃ M : TwoStateMeasurement d (algorithmCost C₂ d₀ d ε), ∀ (ρ σ : Mat d) (hρ : Density ρ)
          (hσ : Density σ), ENNReal.ofReal (2/3 : ℝ) ≤
            outcomeLaw M ρ σ hρ hσ {x | |x-distance ρ σ| ≤ ε} := by
      intro d hd ε hε hε1
      obtain ⟨M, hM⟩ := rounded_algorithm_realization C₂ hC₂ d₀ hd₀ d hd ε hε hε1
      refine ⟨M, fun ρ σ hρ hσ => ?_⟩
      have hB : MeasurableSet {x : ℝ | |x - distance ρ σ| ≤ ε} :=
        (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const))
          continuous_const).measurableSet
      rw [hM ρ σ hρ hσ _ hB]
      by_cases hlt : d < d₀
      · exact bounded_branch hd hlt C₂ hε hε1 ρ σ hρ hσ
      · exact main_branch hd (not_lt.mp hlt) hC₂ h32 hε hε1 ρ σ hρ hσ
    intro d hd ε hε
    by_cases h1 : 1 ≤ ε
    · refine ⟨0, Nat.zero_le _, zeroPOVM d, fun ρ σ hρ hσ => ?_⟩
      rw [law_zero]
      have hB : MeasurableSet {x : ℝ | |x - distance ρ σ| ≤ ε} :=
        (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const))
          continuous_const).measurableSet
      rw [Measure.dirac_apply' _ hB, Set.indicator_of_mem]
      · simp; norm_num
      · show |0 - distance ρ σ| ≤ ε
        rw [zero_sub, abs_neg, abs_of_nonneg (distance_nonneg ρ σ hρ hσ)]
        linarith [distance_le_one ρ σ hρ hσ]
    · push Not at h1
      set ε' := min ε (1/32) with hε'
      have hε'0 : 0 < ε' := lt_min hε (by norm_num)
      have hε'1 : ε' ≤ 1/32 := min_le_right _ _
      obtain ⟨M, hM⟩ := small d hd ε' hε'0 hε'1
      refine ⟨algorithmCost C₂ d₀ d ε', ?_, M, fun ρ σ hρ hσ => ?_⟩
      · have hc := cost_le C₂ hC₂ d₀ hd₀ hd hε'0 hε'1
        have hr : Kc C₂ d₀ * rate d ε' ≤ 2^20 * Kc C₂ d₀ * rate d ε := by
          by_cases hs : ε ≤ 1/32
          · rw [hε', min_eq_left hs]
            have := rate_pos hd hε
            nlinarith
          · push Not at hs
            rw [hε', min_eq_right hs.le]
            have := rate_32 hd hε h1.le
            nlinarith
        have : (algorithmCost C₂ d₀ d ε' : ℝ) ≤ ⌈2^20 * Kc C₂ d₀ * rate d ε⌉₊ :=
          (hc.trans hr).trans (Nat.le_ceil _)
        exact_mod_cast this
      · refine le_trans (hM ρ σ hρ hσ) (measure_mono ?_)
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        exact hx.trans (min_le_left _ _)
  · refine ⟨zeroPOVM 1, fun ρ σ hρ hσ => ⟨?_, law_zero ρ σ hρ hσ⟩⟩
    rw [distance, density_one hρ, density_one hσ, sub_self, traceNorm_zero, zero_div]
