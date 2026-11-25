-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_logLogCut_mem_Icc_93e196c3aba0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:14.153474+00:00
-- url     : https://prove2.me/submissions/4723fba5-3904-4e89-a948-f527360e554e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCutHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) (y : Fin m → ℂ) :
    logLogCut Q k y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold logLogCut cutStep
  split_ifs
  · simp
  · simp
  · exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
end GroundTheory.Heights₂.Heights
