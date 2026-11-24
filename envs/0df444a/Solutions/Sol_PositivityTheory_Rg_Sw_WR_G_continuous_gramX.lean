-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.continuous_gramX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:50.194947+00:00
-- url     : https://prove2.me/submissions/11250118-1d68-43d9-b9a5-74e3bbf52ec3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_NormMono
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousGramX
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_continuous_evX


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution {m n : ℕ} (ε : Fin m → Bool) : Continuous fun x : Fin m → Fin n → ℂ => gramX ε x :=
  continuous_pi fun i => continuous_pi fun j => GI.continuous_evX _
end PositivityTheory.Rg.Sw.WR.G
