-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.ml_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:22.75745+00:00
-- url     : https://prove2.me/submissions/47acd671-d5dd-4320-b56c-64326ceb5c3b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ}
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin k => V) ℂ) (Y : Fin k → Fin 3 → V) (z : ℂ) :
    A (fun i => Y i 0 + z • Y i 1 + z ^ 2 • Y i 2) =
      ∑ f : Fin k → Fin 3, z ^ (∑ i, (f i : ℕ)) * A (fun i => Y i (f i)) := by
  have h : (fun i => Y i 0 + z • Y i 1 + z ^ 2 • Y i 2) = fun i => ∑ w : Fin 3, z ^ (w : ℕ) • Y i w := by
    funext i; simp [Fin.sum_univ_three]
  rw [h, ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr (by simp) fun f _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum, smul_eq_mul]
end PositivityTheory.Rg.Sw.LVs.TC
