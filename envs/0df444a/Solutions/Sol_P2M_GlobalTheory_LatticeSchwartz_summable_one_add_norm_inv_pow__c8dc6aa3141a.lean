-- Prove2me | solution 1 for P2M_GlobalTheory_LatticeSchwartz_summable_one_add_norm_inv_pow__c8dc6aa3141a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:31:53.865379+00:00
-- url     : https://prove2.me/submissions/4e44c6ec-1986-43f6-9fed-9b77ccc0e05f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeShiftedCutoffSummable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeSchwartz
namespace GlobalTheory.LatticeSchwartz
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {k : ℕ}
    (hk : Module.finrank ℤ L < k) :
    Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := by
  classical
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv L k hk).add (hasSum_ite_eq (0 : L) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp only [if_pos rfl, norm_zero, add_zero, inv_one, one_pow]
    exact le_add_of_nonneg_left (by positivity)
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith
end GlobalTheory.LatticeSchwartz
