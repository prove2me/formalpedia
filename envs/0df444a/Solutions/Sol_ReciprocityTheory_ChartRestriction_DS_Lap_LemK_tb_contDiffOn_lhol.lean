-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.tb_contDiffOn_lhol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:38.722715+00:00
-- url     : https://prove2.me/submissions/d61d64d9-a1c4-4909-bfaa-252dbc9801fb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution {F : Matrix (Fin n) (Fin n) ℂ → E} {s : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hs : IsOpen s) (hF : ContDiffOn ℂ ω F s) (Z : Matrix (Fin n) (Fin n) ℂ) :
    ContDiffOn ℂ ω (Lhol Z F) s := by
  have hl : ContDiff ℂ ω (fun z : Matrix (Fin n) (Fin n) ℂ => Z * z) :=
    (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ Z)).contDiff
  exact (hF.fderiv_of_isOpen hs le_top).clm_apply hl.contDiffOn
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
