-- Prove2me | solution 1 for Viterbo.gromovWidth_pow_le_factorial_mul_volume
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:23:37.605748+00:00
-- url     : https://prove2.me/submissions/997ca061-02d7-4358-b69b-46c27f2bef62

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

open MeasureTheory
open scoped ENNReal

namespace Viterbo.Part

open OAI.SymmetricPolar

/-- The phase-space ball of capacity `c` is the `ofLp`-preimage of a Euclidean ball. -/
theorem ofLp_preimage_capacityBall (n : ℕ) (c : ℝ) :
    (WithLp.ofLp : WithLp 2 (Position n × Position n) → Phase n) ⁻¹' capacityBall n c =
      Metric.ball (0 : WithLp 2 (Position n × Position n)) (Real.sqrt (c / Real.pi)) := by
  ext x
  simp only [Set.mem_preimage, capacityBall, Set.mem_ofPred_eq, mem_ball_zero_iff]
  have hx := WithLp.prod_norm_sq_eq_of_L2 x
  rw [← Real.sqrt_sq (norm_nonneg x)]
  rw [Real.sqrt_lt_sqrt_iff (sq_nonneg _), hx, lt_div_iff₀ Real.pi_pos, mul_comm]
  rfl

theorem volume_capacityBall (n : ℕ) {c : ℝ} (hc : 0 < c) :
    volume (capacityBall n c) = ENNReal.ofReal (c ^ n / n.factorial) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have huniv : capacityBall 0 c = Set.univ := by
      ext z
      simp only [capacityBall, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      have h1 : z.1 = 0 := Subsingleton.elim _ _
      have h2 : z.2 = 0 := Subsingleton.elim _ _
      simp [h1, h2, hc]
    rw [huniv, Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod]
    simp [volume_euclideanSpace_eq_dirac]
  · have hopen : IsOpen (capacityBall n c) := by
      apply isOpen_lt (by fun_prop) continuous_const
    rw [← (WithLp.volume_preserving_ofLp (Position n) (Position n)).measure_preimage
      hopen.measurableSet.nullMeasurableSet, ofLp_preimage_capacityBall n c]
    have hfr : Module.finrank ℝ (WithLp 2 (Position n × Position n)) = 2 * n := by
      rw [(WithLp.linearEquiv 2 ℝ (Position n × Position n)).finrank_eq, Module.finrank_prod,
        finrank_euclideanSpace, Fintype.card_fin]
      ring
    have : Nontrivial (WithLp 2 (Position n × Position n)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfr]; omega)
    rw [InnerProductSpace.volume_ball, hfr]
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h1 : Real.sqrt (c / Real.pi) ^ (2 * n) = (c / Real.pi) ^ n := by
      rw [pow_mul, Real.sq_sqrt (by positivity)]
    have h2 : Real.sqrt Real.pi ^ (2 * n) = Real.pi ^ n := by
      rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
    have h3 : ((2 * n : ℕ) : ℝ) / 2 + 1 = (n : ℝ) + 1 := by push_cast; ring
    rw [h1, h2, h3, Real.Gamma_nat_eq_factorial, div_pow]
    have hpi : Real.pi ^ n ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp

end Viterbo.Part

namespace Viterbo.GromovVol

open OAI.SymmetricPolar Set

/-- The standard symplectic form `omega0` as a bilinear form. -/
noncomputable def omegaForm (n : ℕ) : LinearMap.BilinForm ℝ (Phase n) :=
  LinearMap.mk₂ ℝ omega0
    (fun a b c => by simp only [omega0, Prod.fst_add, Prod.snd_add, inner_add_left,
      inner_add_right]; ring)
    (fun r a b => by simp only [omega0, Prod.smul_fst, Prod.smul_snd, inner_smul_left,
      inner_smul_right, smul_eq_mul, RCLike.conj_to_real]; ring)
    (fun a b c => by simp only [omega0, Prod.fst_add, Prod.snd_add, inner_add_left,
      inner_add_right]; ring)
    (fun r a b => by simp only [omega0, Prod.smul_fst, Prod.smul_snd, inner_smul_left,
      inner_smul_right, smul_eq_mul, RCLike.conj_to_real]; ring)

theorem omegaForm_apply {n : ℕ} (v w : Phase n) : omegaForm n v w = omega0 v w := rfl

theorem omegaForm_nondegenerate (n : ℕ) : (omegaForm n).Nondegenerate := by
  constructor
  · intro m hm
    have h := hm (-m.2, m.1)
    simp only [omegaForm_apply, omega0, inner_neg_left] at h
    have h1 := real_inner_self_nonneg (x := m.1)
    have h2 := real_inner_self_nonneg (x := m.2)
    have e1 : inner ℝ m.1 m.1 = 0 := by linarith
    have e2 : inner ℝ m.2 m.2 = 0 := by linarith
    rw [inner_self_eq_zero (𝕜 := ℝ)] at e1 e2
    exact Prod.ext e1 e2
  · intro m hm
    have h := hm (m.2, -m.1)
    simp only [omegaForm_apply, omega0, inner_neg_right] at h
    have h1 := real_inner_self_nonneg (x := m.1)
    have h2 := real_inner_self_nonneg (x := m.2)
    have e1 : inner ℝ m.1 m.1 = 0 := by linarith
    have e2 : inner ℝ m.2 m.2 = 0 := by linarith
    rw [inner_self_eq_zero (𝕜 := ℝ)] at e1 e2
    exact Prod.ext e1 e2

/-- A linear map preserving `omega0` has determinant `±1`. -/
theorem abs_det_eq_one {n : ℕ} (A : Phase n →L[ℝ] Phase n)
    (hA : ∀ v w, omega0 (A v) (A w) = omega0 v w) : |A.det| = 1 := by
  have hB : (omegaForm n).comp A.toLinearMap A.toLinearMap = omegaForm n := by
    refine LinearMap.ext₂ fun v w => ?_
    simp [LinearMap.BilinForm.comp_apply, omegaForm_apply, hA]
  let b := Module.finBasis ℝ (Phase n)
  have hM := LinearMap.BilinForm.toMatrix_comp b b (omegaForm n) A.toLinearMap A.toLinearMap
  rw [hB] at hM
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at hdet
  have hne : (LinearMap.BilinForm.toMatrix b (omegaForm n)).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp (omegaForm_nondegenerate n)
  have hsq : LinearMap.det A.toLinearMap * LinearMap.det A.toLinearMap = 1 := by
    have : (LinearMap.BilinForm.toMatrix b (omegaForm n)).det *
        (LinearMap.det A.toLinearMap * LinearMap.det A.toLinearMap - 1) = 0 := by
      linear_combination -hdet
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · linarith
  have habs : |A.det| * |A.det| = 1 := by
    rw [← abs_mul]
    change |LinearMap.det A.toLinearMap * LinearMap.det A.toLinearMap| = 1
    rw [hsq, abs_one]
  nlinarith [abs_nonneg A.det]

theorem isOpen_capacityBall (n : ℕ) (c : ℝ) : IsOpen (capacityBall n c) :=
  isOpen_lt (by fun_prop) continuous_const

/-- Symplectic embeddings of a ball preserve its volume, so the ball's volume is at most `vol K`. -/
theorem volume_le_of_embedding {n : ℕ} {c : ℝ} {K : Set (Phase n)}
    (h : HasSymplecticEmbedding (capacityBall n c) K) :
    volume (capacityBall n c) ≤ volume K := by
  obtain ⟨e, hcd, hemb, hmaps, hsymp⟩ := h
  have : (volume : Measure (Phase n)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hopen := isOpen_capacityBall n c
  have hdiff : ∀ z ∈ capacityBall n c, HasFDerivAt e (fderiv ℝ e z) z := fun z hz =>
    ((hcd.differentiableOn (by simp)) z hz).differentiableAt (hopen.mem_nhds hz) |>.hasFDerivAt
  have hinj : InjOn e (capacityBall n c) := by
    intro x hx y hy hxy
    have := hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy
    simpa using congrArg Subtype.val this
  have hcov := lintegral_abs_det_fderiv_eq_addHaar_image volume hopen.measurableSet
    (fun z hz => (hdiff z hz).hasFDerivWithinAt) hinj
  rw [setLIntegral_congr_fun hopen.measurableSet
    (g := fun _ => (1 : ℝ≥0∞)) (fun z hz => by simp [abs_det_eq_one _ (hsymp z hz)])] at hcov
  rw [setLIntegral_const, one_mul] at hcov
  rw [hcov]
  exact measure_mono hmaps.image_subset

theorem ofReal_pow_le_of_embedding {n : ℕ} {c : ℝ} (hc : 0 < c) {K : Set (Phase n)}
    (h : HasSymplecticEmbedding (capacityBall n c) K) :
    ENNReal.ofReal c ^ n ≤ (n.factorial : ℝ≥0∞) * volume K := by
  calc ENNReal.ofReal c ^ n = (n.factorial : ℝ≥0∞) * volume (capacityBall n c) := by
        rw [Viterbo.Part.volume_capacityBall n hc, ← ENNReal.ofReal_pow hc.le,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hf : (n.factorial : ℝ) ≠ 0 := by positivity
        field_simp
    _ ≤ (n.factorial : ℝ≥0∞) * volume K := mul_le_mul_right (volume_le_of_embedding h) _

theorem main (n : ℕ) (K : Set (OAI.SymmetricPolar.Phase n))
    (hK : IsConvexDomain K) :
    OAI.SymmetricPolar.gromovWidth K ^ n ≤ (n.factorial : ℝ≥0∞) * volume K := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨z, hz⟩ := hK.2.2
    have hKu : K = univ :=
      eq_univ_of_forall fun w => (Subsingleton.elim z w) ▸ interior_subset hz
    have h1 : volume (capacityBall 0 1) = 1 := by
      rw [Viterbo.Part.volume_capacityBall 0 one_pos]; simp
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, hKu]
    calc (1 : ℝ≥0∞) = volume (capacityBall 0 1) := h1.symm
      _ ≤ volume (univ : Set (Phase 0)) := measure_mono (subset_univ _)
  · unfold gromovWidth
    rw [sSup_image, ENNReal.iSup_pow_of_ne_zero hn.ne']
    refine iSup_le fun c => ?_
    rw [ENNReal.iSup_pow_of_ne_zero hn.ne']
    exact iSup_le fun hc => ofReal_pow_le_of_embedding hc.1 hc.2

end Viterbo.GromovVol

open MeasureTheory
open scoped ENNReal

theorem solution (n : ℕ) (K : Set (OAI.SymmetricPolar.Phase n))
    (hK : Viterbo.IsConvexDomain K) :
    OAI.SymmetricPolar.gromovWidth K ^ n ≤ (n.factorial : ℝ≥0∞) * volume K :=
  Viterbo.GromovVol.main n K hK
