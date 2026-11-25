-- Prove2me | solution 1 for PositivityTheory.CW.EigenvectorBasisSetup.cas_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:41.840907+00:00
-- url     : https://prove2.me/submissions/eae4141b-a333-44a5-b7ad-52ce1df5cfd6

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_OrthonormalEigenbasisOfBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.EigenvectorBasisSetup
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.CW.EigenvectorBasisSetup
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (v : V) :
    casimir E v = ∑ a, ∑ b, E a b (E b a v) := by
  unfold casimir
  simp [LinearMap.sum_apply]
end PositivityTheory.CW.EigenvectorBasisSetup
