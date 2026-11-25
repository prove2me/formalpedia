-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.st_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:58:40.052982+00:00
-- url     : https://prove2.me/submissions/33767be8-44e1-488d-84c7-6026d2e4c35f

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow
import Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_alg_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action PositivityTheory.KReal
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.CayleyTransformDarboux
variable {ι I M : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.ThKG.CayleyTransformDarboux
theorem _root_.solution {act : (ι → Matrix I I ℂ) →ₗ[ℂ] Module.End ℂ M} {r : I → I → Prop} {N : Submodule ℂ M}
    (h : ∀ w a b, r a b → ∀ x ∈ N, act (un w a b) x ∈ N) : St act (alg ι r) N :=
  fun _ hZ => (alg_le (S := stab act N) h) hZ
end PositivityTheory.ThKG.CayleyTransformDarboux
