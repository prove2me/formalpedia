-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_MaDensLogPow_cons_const_apply_5310b6bbe09d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:45.775342+00:00
-- url     : https://prove2.me/submissions/b5ea90a1-7244-4aac-a901-97c7bd9e6819

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLogPow

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
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLogPow
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.MaDensLogPow
theorem _root_.solution {n : ℕ} (A₀ H : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) (k : Fin (n + 1 + 1)) :
    (Fin.cons A₀ (fun _ : Fin (n + 1) => H) : Fin (n + 1 + 1) → _) k = if k = 0 then A₀ else H := by
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · simp [Fin.succ_ne_zero]
end GroundTheory.Heights₂.Heights.MaDensLogPow
