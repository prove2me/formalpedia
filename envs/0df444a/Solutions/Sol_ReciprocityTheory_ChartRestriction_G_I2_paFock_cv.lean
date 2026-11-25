-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paFock_cv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:11:58.323305+00:00
-- url     : https://prove2.me/submissions/8cbed802-555b-475e-a240-c61920d84e4a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paTR_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {q : ℕ} (hq : 1 ≤ q) (H K : EuclideanSpace ℂ ι → ℂ) :
    fockIP (fun z => H ((Real.sqrt (q * Real.pi))⁻¹ • paT z))
      (fun z => K ((Real.sqrt (q * Real.pi))⁻¹ • paT z)) = (q : ℂ) ^ Fintype.card ι * paIP q H K := by
  set s : ℝ := Real.sqrt (q * Real.pi) with hs
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = q * Real.pi := Real.sq_sqrt (by positivity)
  let g : EuclideanSpace ℂ ι → ℂ := fun w =>
    H (s⁻¹ • w) * (starRingEnd ℂ) (K (s⁻¹ • w)) * (Real.exp (-‖w‖ ^ 2) : ℂ)

  have h1 : (∫ z : EuclideanSpace ℂ (Fin (Fintype.card ι)), H (s⁻¹ • paT z) *
      (starRingEnd ℂ) (K (s⁻¹ • paT z)) * (Real.exp (-‖z‖ ^ 2) : ℂ)) = ∫ w, g w := by
    rw [← (paTR (ι := ι)).measurePreserving.integral_comp
      (paTR (ι := ι)).toHomeomorph.measurableEmbedding g]
    congr 1
    ext z
    simp only [g, paTR_apply, LinearIsometryEquiv.norm_map]

  have hd : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace]
  have h2 : ∫ w, g w = (s ^ (2 * Fintype.card ι) : ℝ) • paIP q H K := by
    have h3 := MeasureTheory.Measure.integral_comp_smul
      (volume : Measure (EuclideanSpace ℂ ι)) g s
    rw [hd] at h3
    have hg : (fun x => g (s • x)) = fun v => H v * (starRingEnd ℂ) (K v) * (paW q v : ℂ) := by
      ext v
      simp only [g, paW]
      rw [smul_smul, inv_mul_cancel₀ hs0.ne', one_smul, norm_smul, Real.norm_eq_abs,
        abs_of_pos hs0, mul_pow, hs2]
      simp only [neg_mul]
    rw [hg, abs_of_pos (by positivity)] at h3
    unfold paIP
    rw [h3, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  unfold fockIP
  rw [h1, h2, pow_mul, hs2, Complex.real_smul]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  rw [mul_pow]
  field_simp
end ReciprocityTheory.ChartRestriction.G.I2
