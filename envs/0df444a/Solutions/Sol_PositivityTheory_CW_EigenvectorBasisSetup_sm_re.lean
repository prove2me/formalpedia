-- Prove2me | solution 1 for PositivityTheory.CW.EigenvectorBasisSetup.sm_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:24:59.586837+00:00
-- url     : https://prove2.me/submissions/694dc145-5f5e-40bf-94b0-405de729654b

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_OrthonormalEigenbasisOfBasic
import Theorems.Thm_PositivityTheory_CW_EigenvectorBasisSetup_sq_re

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
theorem _root_.solution (r : ℝ) (u : V) : (inner ℂ u ((r : ℂ) • u)).re = r * ‖u‖ ^ 2 := by
  rw [inner_smul_right, Complex.re_ofReal_mul, ← sq_re]
end PositivityTheory.CW.EigenvectorBasisSetup
