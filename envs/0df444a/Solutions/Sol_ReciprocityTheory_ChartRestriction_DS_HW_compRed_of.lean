-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.compRed_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:43.977673+00:00
-- url     : https://prove2.me/submissions/aeb16f60-0575-4c58-8762-db2e966a3693

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Decomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_finrank_eq_sum_of_orth
import Theorems.Thm_Formalism_REAL_isCompactInvariant_compactSpan
import Theorems.Thm_Formalism_REAL_kDecomp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (hR : KRepRelStatement) (hS : KRepStableStatement) (hP : KRepPieceStatement) :
    CompRedStatement := by
  intro n ε R
  obtain ⟨hrel, hunit⟩ := hR n ε R
  obtain ⟨m, x, μ, hx, horth, htop⟩ :=
    Formalism.REAL.kDecomp R.V n ε R.units ⊤ inferInstance hrel hunit (fun a b _ v _ => Submodule.mem_top)
  refine ⟨m, x, μ, fun i => ⟨(hx i).2.1, (hx i).2.2⟩, horth, htop, ?_, ?_, ?_⟩
  · exact finrank_eq_sum_of_orth _ horth htop
  · intro i k v hv
    exact (hS n ε R _).mpr (Formalism.REAL.isCompactInvariant_compactSpan (x i)) k v hv
  · intro i
    obtain ⟨T, φ, h1, h2, h3⟩ := hP n ε R (μ i) (x i) (hx i).2.1 (hx i).2.2
    exact ⟨T, φ, φ.toLinearEquiv.finrank_eq, h1, h2, h3⟩
end ReciprocityTheory.ChartRestriction.DS.HW
