-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.modulus_characters_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:03:11.230459+00:00
-- url     : https://prove2.me/submissions/38dc5f32-6648-48ba-a564-9e5a9800875d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_lower_right_parabolic_ne_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_par_rel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (p q : ℤ) {P : M2 n} (hP : InP P) :
    c1 p q P * c2 p q P = ((‖(P.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) := by
  have hd := det_lower_right_parabolic_ne_zero hP
  have hrel : star P.toBlocks₁₁.det * P.toBlocks₂₂.det = 1 := by
    have := congrArg Matrix.det (par_rel hP.1 hP.2)
    rwa [det_mul, det_conjTranspose, det_one] at this
  have ha : P.toBlocks₁₁.det = (star P.toBlocks₂₂.det)⁻¹ := by
    have h2 : star (star P.toBlocks₁₁.det * P.toBlocks₂₂.det) = 1 := by rw [hrel, star_one]
    rw [star_mul, star_star] at h2
    exact eq_inv_of_mul_eq_one_right h2
  have hn : ((‖P.toBlocks₂₂.det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) =
      (P.toBlocks₂₂.det * star P.toBlocks₂₂.det) ^ (-(n : ℤ)) := by
    rw [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_zpow, Complex.normSq_eq_norm_sq]
    congr 1
    rw [← zpow_natCast, ← _root_.zpow_mul]
    congr 1
    push_cast; ring
  rw [hn, c1, c2, ha, mul_zpow]
  set d := P.toBlocks₂₂.det
  have e : d ^ (-p) * d ^ (-q) * (d ^ (p - n) * d ^ q * (star d)⁻¹ ^ (n : ℤ)) =
      (d ^ (-p) * d ^ (-q) * d ^ (p - n) * d ^ q) * (star d)⁻¹ ^ (n : ℤ) := by ring
  rw [e, ← zpow_add₀ hd, ← zpow_add₀ hd, ← zpow_add₀ hd,
    show -p + -q + (p - (n : ℤ)) + q = -(n : ℤ) by ring, _root_.inv_zpow']
end PositivityTheory.Rg.Sw.LVs
