-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.I.norm_sq_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:44.855747+00:00
-- url     : https://prove2.me/submissions/36eb0cca-127d-4ab1-9323-6d97854f2d09

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Integr

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.I
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.I
theorem _root_.solution (y : E n) : ‖y‖ ^ 2 ≤ ∑ a, ∑ b, y a b ^ 2 := by
  have h0 : 0 ≤ ∑ a, ∑ b, y a b ^ 2 := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hle : ‖y‖ ≤ Real.sqrt (∑ a, ∑ b, y a b ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun b => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    calc y a b ^ 2 ≤ ∑ b', y a b' ^ 2 := Finset.single_le_sum (fun b' _ => sq_nonneg (y a b')) (Finset.mem_univ b)
      _ ≤ ∑ a', ∑ b', y a' b' ^ 2 :=
        Finset.single_le_sum (f := fun a' => ∑ b', y a' b' ^ 2) (fun a' _ => Finset.sum_nonneg fun b' _ => sq_nonneg _)
          (Finset.mem_univ a)
  calc ‖y‖ ^ 2 ≤ Real.sqrt (∑ a, ∑ b, y a b ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = _ := Real.sq_sqrt h0
end PositivityTheory.Rg.Sw.WR.I
