-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.continuous_blkEmbed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:57.072369+00:00
-- url     : https://prove2.me/submissions/7b5d17d4-d144-495c-85f4-a2b08882c56d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_continuous_blkDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (s : Bool) : Continuous (blkEmbed ε s) := by
  have hmk : Continuous (fun h : KG (fun _ : Fin (blkP ε s) => true) => toMK h) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hemb : Continuous fun h : KG (fun _ : Fin (blkP ε s) => true) => embM ε s (toMK h) :=
    (continuous_blkDiag ε).comp ((continuous_mulSingle s).comp hmk)
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact Units.continuous_iff.mpr ⟨hemb, hemb.matrix_conjTranspose⟩
end ReciprocityTheory.ChartRestriction.DS.HW
