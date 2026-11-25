-- Prove2me | solution 1 for P2M_GlobalTheory_SchwartzTranslateSum_summable_one_add_norm_inv_pow__68b39a97649f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:25.410214+00:00
-- url     : https://prove2.me/submissions/f8bccbe3-b77f-451d-a6cf-d87a01c12ac9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeTranslatesCutoffSummable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SchwartzMap
noncomputable section
open GlobalTheory GlobalTheory.SchwartzTranslateSum
namespace GlobalTheory.SchwartzTranslateSum
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] {N : ℕ}
    (hN : Module.finrank ℤ Λ < N) : Summable fun z : Λ => ((1 + ‖z‖)⁻¹) ^ N := by
  classical
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv Λ N hN).add (hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith
end GlobalTheory.SchwartzTranslateSum
