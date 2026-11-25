-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.wIbp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:16:15.112124+00:00
-- url     : https://prove2.me/submissions/983c6c13-ecfe-4210-9d42-403651edaa24

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_WIbpLeft
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_wIbp_left
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.E
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] : WIbpStatement n M := by
  intro z hz ph k a b hph ha hb hc
  refine ⟨wIbp_left n z hz ph k a b hph ha hb hc, ?_⟩

  have h := wIbp_left n z hz ph k b a hph hb ha hc.symm
  have h' := congrArg (starRingEnd ℂ) h
  rw [← integral_conj, map_neg, ← integral_conj] at h'
  have e1 : (fun x => dTw n z ph k a x * conj (b x) * (Real.exp (-ph x) : ℂ)) =
      fun x => conj (b x * conj (dTw n z ph k a x) * (Real.exp (-ph x) : ℂ)) := by
    funext x
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  have e2 : (fun x => a x * conj (db n z k b x) * (Real.exp (-ph x) : ℂ)) =
      fun x => conj (db n z k b x * conj (a x) * (Real.exp (-ph x) : ℂ)) := by
    funext x
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  rw [e1, e2, h', neg_neg]
end ReciprocityTheory.L2DbarEstimates.E
