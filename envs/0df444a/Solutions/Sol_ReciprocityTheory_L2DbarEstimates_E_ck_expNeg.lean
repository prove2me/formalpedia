-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.ck_expNeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:09.268813+00:00
-- url     : https://prove2.me/submissions/894c92d6-80cd-4742-a6a5-688e229a0588

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


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
open scoped ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.E
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (ph : M → ℝ) (hph : CkR n z k ph) :
    Ck n z k (fun x => (Real.exp (-ph x) : ℂ)) := by
  intro e he
  have hg : ContDiff ℝ k (fun c : ℂ => ((Real.exp (-c.re) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.reCLM.contDiff.neg)
  refine (hg.comp_contDiffOn (hph e he)).congr fun w _ => ?_
  simp
end ReciprocityTheory.L2DbarEstimates.E
