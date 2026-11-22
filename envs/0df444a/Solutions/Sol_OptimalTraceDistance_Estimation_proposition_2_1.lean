-- Prove2me | solution 1 for OptimalTraceDistance.Estimation.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:12:57.971828+00:00
-- url     : https://prove2.me/submissions/fcfe27f0-8d8f-4620-9666-42378457788c

import Definitions.Def_OptimalTraceDistance_Estimation_Core

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OTDProp21
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


lemma density_quad {ρ : Mat d} (hρ : Density ρ) (x : Fin d → ℂ) :
    0 ≤ (star x ⬝ᵥ (ρ *ᵥ x)).re ∧ (star x ⬝ᵥ (ρ *ᵥ x)).re ≤ (star x ⬝ᵥ x).re := by
  have hH := hρ.1.1
  have hnn := hρ.1.eigenvalues_nonneg
  have hsum : ∑ i, hH.eigenvalues i = 1 := by
    have := congrArg Complex.re (hH.trace_eq_sum_eigenvalues)
    rw [hρ.2, Complex.re_sum] at this; simpa using this.symm
  have hle : ∀ i, hH.eigenvalues i ≤ 1 := fun i => by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  rw [quad_re_self hH, ← sum_normsq_U hH]
  constructor
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hnn i) (sq_nonneg _))
  · exact Finset.sum_le_sum (fun i _ => by
      have := sq_nonneg ‖(star (hH.eigenvectorUnitary : Mat d) *ᵥ x) i‖
      nlinarith [hle i, hnn i])

lemma quad_smul (c : ℂ) (A : Mat d) (x : Fin d → ℂ) :
    star x ⬝ᵥ ((c • A) *ᵥ x) = c * (star x ⬝ᵥ (A *ᵥ x)) := by
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma quad_sub (A B : Mat d) (x : Fin d → ℂ) :
    star x ⬝ᵥ ((A - B) *ᵥ x) = star x ⬝ᵥ (A *ᵥ x) - star x ⬝ᵥ (B *ᵥ x) := by
  rw [sub_mulVec, dotProduct_sub]

lemma quad_add (A B : Mat d) (x : Fin d → ℂ) :
    star x ⬝ᵥ ((A + B) *ᵥ x) = star x ⬝ᵥ (A *ᵥ x) + star x ⬝ᵥ (B *ᵥ x) := by
  rw [add_mulVec, dotProduct_add]

lemma two_inv_nonneg : (0 : ℂ) ≤ (2 : ℂ)⁻¹ := by
  rw [show (2:ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl]
  exact_mod_cast (by norm_num : (0:ℝ) ≤ 2⁻¹)

lemma minus_add_plus (ρ σ : Mat d) : minus ρ σ - -plus ρ σ = ρ := by
  unfold minus plus; rw [sub_neg_eq_add, ← smul_add]
  rw [show ρ - σ + (ρ + σ) = (2:ℂ) • ρ by rw [two_smul]; abel, smul_smul]; norm_num

lemma plus_sub_minus (ρ σ : Mat d) : plus ρ σ - minus ρ σ = σ := by
  unfold minus plus; rw [← smul_sub]
  rw [show ρ + σ - (ρ - σ) = (2:ℂ) • σ by rw [two_smul]; abel, smul_smul]; norm_num

lemma proj_conj_psd {Q X : Mat d} (hQ : projector Q) (hX : X.PosSemidef) :
    (compress Q X).PosSemidef := by
  unfold compress
  have := hX.mul_mul_conjTranspose_same Q
  rwa [hQ.1.eq] at this

lemma part1 (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ) :
    (plus ρ σ).PosSemidef ∧ (plus ρ σ).trace = 1 ∧
    lePSD (-(plus ρ σ)) (minus ρ σ) ∧ lePSD (minus ρ σ) (plus ρ σ) ∧
    opNorm (minus ρ σ) ≤ 1/2 ∧
    ∀ Q, projector Q → (compress Q (plus ρ σ)).PosSemidef ∧
      lePSD (-(compress Q (plus ρ σ))) (compress Q (minus ρ σ)) ∧
      lePSD (compress Q (minus ρ σ)) (compress Q (plus ρ σ)) ∧
      tr (compress Q (plus ρ σ)) ≤ 1 := by
  have hP : (plus ρ σ).PosSemidef := (hρ.1.add hσ.1).smul two_inv_nonneg
  have htr : (plus ρ σ).trace = 1 := by
    unfold plus; rw [trace_smul, trace_add, hρ.2, hσ.2]; norm_num
  refine ⟨hP, htr, ?_, ?_, ?_, ?_⟩
  · unfold lePSD; rw [minus_add_plus]; exact hρ.1
  · unfold lePSD; rw [plus_sub_minus]; exact hσ.1
  · have hMH : (minus ρ σ).IsHermitian := by
      unfold minus
      have h := hρ.1.1.sub hσ.1.1
      unfold IsHermitian at h ⊢
      rw [conjTranspose_smul, h]; congr 1; simp
    refine opNorm_le_of_quad hMH (by norm_num) (fun x => ?_)
    unfold minus
    rw [quad_smul, quad_sub]
    obtain ⟨a0, a1⟩ := density_quad hρ x
    obtain ⟨b0, b1⟩ := density_quad hσ x
    have : ((2:ℂ)⁻¹ * (star x ⬝ᵥ (ρ *ᵥ x) - star x ⬝ᵥ (σ *ᵥ x))).re =
        2⁻¹ * ((star x ⬝ᵥ (ρ *ᵥ x)).re - (star x ⬝ᵥ (σ *ᵥ x)).re) := by
      rw [show (2:ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul, Complex.sub_re]
    rw [this, abs_le]; constructor <;> nlinarith
  · intro Q hQ
    refine ⟨proj_conj_psd hQ hP, ?_, ?_, ?_⟩
    · unfold lePSD compress
      rw [show Q * minus ρ σ * Q - -(Q * plus ρ σ * Q) = Q * (minus ρ σ - -plus ρ σ) * Q by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul], minus_add_plus]
      exact proj_conj_psd hQ hρ.1
    · unfold lePSD compress
      rw [show Q * plus ρ σ * Q - Q * minus ρ σ * Q = Q * (plus ρ σ - minus ρ σ) * Q by
        simp only [Matrix.mul_sub, Matrix.sub_mul], plus_sub_minus]
      exact proj_conj_psd hQ hσ.1
    · -- tr(QPQ) = tr P - tr((1-Q)P(1-Q))
      have hQ' : projector (1 - Q) := by
        refine ⟨(isHermitian_one).sub hQ.1, ?_⟩
        rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hQ.2]; simp
      have h1 := (proj_conj_psd hQ' hP).trace_nonneg
      have key : (compress Q (plus ρ σ)).trace + (compress (1-Q) (plus ρ σ)).trace =
          (plus ρ σ).trace := by
        unfold compress
        rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle (1 - Q), hQ.2, hQ'.2, ← trace_add,
          ← Matrix.add_mul]; simp
      unfold tr
      rw [htr] at key
      have h2 := congrArg Complex.re key
      rw [Complex.add_re, Complex.one_re] at h2
      have h3 : 0 ≤ (compress (1-Q) (plus ρ σ)).trace.re := by
        exact (Complex.nonneg_iff.mp h1).1
      linarith


lemma quad_conj_herm {G : Mat d} (hG : G.IsHermitian) (B : Mat d) (x : Fin d → ℂ) :
    star x ⬝ᵥ ((G * B * G) *ᵥ x) = star (G *ᵥ x) ⬝ᵥ (B *ᵥ (G *ᵥ x)) := by
  have h := quad_conj G B x
  have hs : star G = G := by rw [Matrix.star_eq_conjTranspose, hG.eq]
  rwa [hs] at h

lemma re_nonneg_of_psd {A : Mat d} (hA : A.PosSemidef) (x : Fin d → ℂ) :
    0 ≤ (star x ⬝ᵥ (A *ᵥ x)).re := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg x)).1

/-- sandwich: |quad Y| ≤ quad X -/
lemma sandwich {X Y : Mat d} (h1 : lePSD (-X) Y) (h2 : lePSD Y X) (x : Fin d → ℂ) :
    |(star x ⬝ᵥ (Y *ᵥ x)).re| ≤ (star x ⬝ᵥ (X *ᵥ x)).re := by
  have a := re_nonneg_of_psd h1 x
  have b := re_nonneg_of_psd h2 x
  rw [sub_neg_eq_add, quad_add, Complex.add_re] at a
  rw [quad_sub, Complex.sub_re] at b
  rw [abs_le]; constructor <;> linarith

def gInv (t : ℝ) : ℝ := if 0 < t then (Real.sqrt t)⁻¹ else 0
def pf (t : ℝ) : ℝ := if 0 < t then 1 else 0

lemma part2_J (X Y : Mat d) (hXH : X.IsHermitian) (hYH : Y.IsHermitian) (hX : X.PosSemidef)
    (h1 : lePSD (-X) Y) (h2 : lePSD Y X) :
    ∃ J : Mat d, J.IsHermitian ∧ Y = sqrtMat X * J * sqrtMat X ∧ opNorm J ≤ 1 := by
  set G := cfc gInv X with hGdef
  set P := cfc pf X with hPdef
  have hG : G.IsHermitian := cfc_herm hXH gInv
  have hPH : P.IsHermitian := cfc_herm hXH pf
  have hSG : sqrtMat X * G = P := by
    unfold sqrtMat; rw [cfc_mul' hXH]; congr 1; funext t; unfold gInv pf
    split_ifs with h
    · exact mul_inv_cancel₀ (Real.sqrt_pos.mpr h).ne'
    · simp
  have hGS : G * sqrtMat X = P := by
    unfold sqrtMat; rw [cfc_mul' hXH]; congr 1; funext t; unfold gInv pf
    split_ifs with h
    · exact inv_mul_cancel₀ (Real.sqrt_pos.mpr h).ne'
    · simp
  have hGXG : G * X * G = P := by
    conv_lhs => rw [← cfc_id'' hXH]
    rw [cfc_mul' hXH, cfc_mul' hXH]; congr 1; funext t; unfold gInv pf
    split_ifs with h
    · have hs := Real.sqrt_pos.mpr h
      have : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt h.le
      calc (Real.sqrt t)⁻¹ * t * (Real.sqrt t)⁻¹ = t / (Real.sqrt t * Real.sqrt t) := by
            field_simp
        _ = 1 := by rw [this, div_self h.ne']
    · simp
  have hXP : X * P = X := by
    conv_lhs => rw [← cfc_id'' hXH]
    conv_rhs => rw [← cfc_id'' hXH]
    rw [cfc_mul' hXH]
    apply cfc_congr' hXH
    intro i; unfold pf
    have := hX.eigenvalues_nonneg i
    split_ifs with h
    · ring
    · have : hXH.eigenvalues i = 0 := by
        have h' : hXH.eigenvalues i ≤ 0 := not_lt.mp h
        exact le_antisymm h' (by convert hX.eigenvalues_nonneg i)
      rw [this]; ring
  have hXQ : X * (1 - P) = 0 := by rw [Matrix.mul_sub, hXP, Matrix.mul_one, sub_self]
  have hYQ : Y * (1 - P) = 0 := by
    rw [ext_iff_mulVec]; intro v
    rw [zero_mulVec, ← mulVec_mulVec]
    set u := (1 - P) *ᵥ v
    have hXu : X *ᵥ u = 0 := by rw [mulVec_mulVec, hXQ, zero_mulVec]
    have a := h1.dotProduct_mulVec_nonneg u
    have b := h2.dotProduct_mulVec_nonneg u
    rw [sub_neg_eq_add, quad_add, hXu, dotProduct_zero, add_zero] at a
    rw [quad_sub, hXu, dotProduct_zero, zero_sub] at b
    have hq : star u ⬝ᵥ (Y *ᵥ u) = 0 := le_antisymm (by simpa using b) a
    have hz : star u ⬝ᵥ ((Y - -X) *ᵥ u) = 0 := by
      rw [sub_neg_eq_add, quad_add, hXu, dotProduct_zero, add_zero, hq]
    have := (h1.dotProduct_mulVec_zero_iff u).mp hz
    rw [sub_neg_eq_add, add_mulVec, hXu, add_zero] at this
    exact this
  have hYP : Y * P = Y := by
    have : Y * (1 - P) = Y - Y * P := by rw [Matrix.mul_sub, Matrix.mul_one]
    rw [hYQ] at this; exact (sub_eq_zero.mp this.symm).symm
  have hPY : P * Y = Y := by
    have := congrArg conjTranspose hYP
    rwa [conjTranspose_mul, hPH.eq, hYH.eq] at this
  refine ⟨G * Y * G, ?_, ?_, ?_⟩
  · have := isHermitian_mul_mul_conjTranspose G hYH
    rwa [hG.eq] at this
  · calc Y = P * Y * P := by rw [hPY, hYP]
      _ = (sqrtMat X * G) * Y * (G * sqrtMat X) := by rw [hSG, hGS]
      _ = sqrtMat X * (G * Y * G) * sqrtMat X := by simp only [Matrix.mul_assoc]
  · have hJ : (G * Y * G).IsHermitian := by
      have := isHermitian_mul_mul_conjTranspose G hYH
      rwa [hG.eq] at this
    refine opNorm_le_of_quad hJ zero_le_one (fun x => ?_)
    rw [quad_conj_herm hG, one_mul]
    refine (sandwich h1 h2 _).trans ?_
    rw [← quad_conj_herm hG, hGXG, hPdef, quad_re hXH, ← sum_normsq_U hXH]
    refine Finset.sum_le_sum (fun i _ => ?_)
    unfold pf; split_ifs <;> nlinarith [sq_nonneg ‖(star (hXH.eigenvectorUnitary : Mat d) *ᵥ x) i‖]


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

lemma row_normsq (M : Mat d) (hM : M * star M = 1) (j : Fin d) :
    ∑ k, ‖M j k‖^2 = 1 := by
  have h := congrArg (fun A : Mat d => (A j j).re) hM
  simp only [mul_apply, Matrix.star_eq_conjTranspose, conjTranspose_apply, one_apply_eq,
    Complex.one_re, Complex.re_sum] at h
  rw [← h]; refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show star (M j k) = (starRingEnd ℂ) (M j k) from rfl, Complex.mul_conj',
    ← Complex.ofReal_pow, Complex.ofReal_re]

lemma core_ineq {X Y : Mat d} (hXH : X.IsHermitian) (hYH : Y.IsHermitian) (hX : X.PosSemidef)
    (h1 : lePSD (-X) Y) (h2 : lePSD Y X) {q : ℝ} (hq : 1 ≤ q) :
    ∑ k, |hYH.eigenvalues k| ^ q ≤ ∑ j, hXH.eigenvalues j ^ q := by
  set V := (hYH.eigenvectorUnitary : Mat d)
  set W := (hXH.eigenvectorUnitary : Mat d)
  set μ := hYH.eigenvalues
  set lam := hXH.eigenvalues
  have hVV : star V * V = 1 := Unitary.star_mul_self_of_mem (U_mem hYH)
  have hVV' : V * star V = 1 := Unitary.mul_star_self_of_mem (U_mem hYH)
  have hWW : star W * W = 1 := Unitary.star_mul_self_of_mem (U_mem hXH)
  have hWW' : W * star W = 1 := Unitary.mul_star_self_of_mem (U_mem hXH)
  set Mx := star W * V
  have hMx : Mx * star Mx = 1 := by
    simp only [Mx, star_mul, star_star]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc V, hVV', Matrix.one_mul, hWW]
  set c : Fin d → Fin d → ℝ := fun j k => ‖Mx j k‖^2
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => by convert hX.eigenvalues_nonneg j
  -- for each k
  have hk : ∀ k, |μ k| ≤ ∑ j, c j k * lam j ∧ ∑ j, c j k = 1 := by
    intro k
    set v : Fin d → ℂ := fun i => V i k
    have hmu : (star v ⬝ᵥ (Y *ᵥ v)).re = μ k := by
      rw [quad_re_self hYH]
      simp only [v, mulVec_col]
      rw [show star (hYH.eigenvectorUnitary : Mat d) * V = 1 from hVV]
      rw [Finset.sum_eq_single k]
      · simp [μ]
      · intro i _ hi; simp [one_apply_ne hi]
      · simp
    have ha : (star v ⬝ᵥ (X *ᵥ v)).re = ∑ j, c j k * lam j := by
      rw [quad_re_self hXH]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [v, mulVec_col, c, Mx]; ring
    have hn : ∑ j, c j k = 1 := by
      have := sum_normsq_U hXH v
      simp only [v, mulVec_col] at this
      rw [col_normsq, hVV] at this
      simpa [c, Mx] using this
    refine ⟨?_, hn⟩
    rw [← hmu, ← ha]; exact sandwich h1 h2 v
  have hcol : ∀ j, ∑ k, c j k = 1 := fun j => row_normsq Mx hMx j
  have hconv := convexOn_rpow hq
  calc ∑ k, |μ k| ^ q ≤ ∑ k, (∑ j, c j k * lam j) ^ q := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        exact Real.rpow_le_rpow (abs_nonneg _) (hk k).1 (by linarith)
    _ ≤ ∑ k, ∑ j, c j k * lam j ^ q := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        have := hconv.map_sum_le (t := Finset.univ) (w := fun j => c j k) (p := lam)
          (fun j _ => sq_nonneg _) (hk k).2 (fun j _ => Set.mem_Ici.mpr (hlam0 j))
        simpa [smul_eq_mul] using this
    _ = ∑ j, lam j ^ q * ∑ k, c j k := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
    _ = ∑ j, lam j ^ q := by simp [hcol]


lemma sq_rpow_half (x q : ℝ) : (x^2)^(q/2) = |x|^q := by
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]
  congr 1; push_cast; ring

lemma schatten_herm {A : Mat d} (hA : A.IsHermitian) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    WHMultiplicativity.schattenNorm p A = (∑ i, |hA.eigenvalues i| ^ p.toReal) ^ (1 / p.toReal) := by
  unfold WHMultiplicativity.schattenNorm
  rw [if_neg hp, trace_cfc_sq hA]
  simp only [sq_rpow_half]

lemma schatten_mono {X Y : Mat d} (hXH : X.IsHermitian) (hYH : Y.IsHermitian) (hX : X.PosSemidef)
    (h1 : lePSD (-X) Y) (h2 : lePSD Y X) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    WHMultiplicativity.schattenNorm p Y ≤ WHMultiplicativity.schattenNorm p X := by
  by_cases htop : p = ⊤
  · unfold WHMultiplicativity.schattenNorm
    rw [if_pos htop, if_pos htop]
    change opNorm Y ≤ opNorm X
    refine opNorm_le_of_quad hYH (norm_nonneg _) (fun x => ?_)
    refine (sandwich h1 h2 x).trans ?_
    exact (le_abs_self _).trans (quad_le_opNorm X x)
  · have hq : 1 ≤ p.toReal := by
      have := ENNReal.toReal_mono htop hp
      simpa using this
    rw [schatten_herm hYH htop, schatten_herm hXH htop]
    apply Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => by positivity)) _ (by positivity)
    have := core_ineq hXH hYH hX h1 h2 hq
    refine this.trans (le_of_eq (Finset.sum_congr rfl (fun j _ => ?_)))
    rw [abs_of_nonneg (by convert hX.eigenvalues_nonneg j)]

end OTDProp21

open OptimalTraceDistance.Estimation OTDProp21

theorem solution (d : ℕ) (hd : 0 < d) :
  (∀ ρ σ : Mat d, Density ρ → Density σ →
    (plus ρ σ).PosSemidef ∧ (plus ρ σ).trace = 1 ∧
    lePSD (-(plus ρ σ)) (minus ρ σ) ∧ lePSD (minus ρ σ) (plus ρ σ) ∧
    opNorm (minus ρ σ) ≤ 1/2 ∧
    ∀ Q, projector Q → (compress Q (plus ρ σ)).PosSemidef ∧
      lePSD (-(compress Q (plus ρ σ))) (compress Q (minus ρ σ)) ∧
      lePSD (compress Q (minus ρ σ)) (compress Q (plus ρ σ)) ∧
      tr (compress Q (plus ρ σ)) ≤ 1) ∧
  (∀ X Y : Mat d, X.IsHermitian → Y.IsHermitian → X.PosSemidef →
    lePSD (-X) Y → lePSD Y X →
    (∃ J : Mat d, J.IsHermitian ∧ Y = sqrtMat X * J * sqrtMat X ∧ opNorm J ≤ 1) ∧
    ∀ p : ℝ≥0∞, 1 ≤ p → WHMultiplicativity.schattenNorm p Y ≤
      WHMultiplicativity.schattenNorm p X) := by
  refine ⟨fun ρ σ hρ hσ => part1 ρ σ hρ hσ, fun X Y hXH hYH hX h1 h2 => ?_⟩
  exact ⟨part2_J X Y hXH hYH hX h1 h2, fun p hp => schatten_mono hXH hYH hX h1 h2 p hp⟩
