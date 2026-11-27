-- Prove2me | solution 1 for P2M_GlobalTheory_coh_equiv__toH_77444994ce05
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:52:56.676528+00:00
-- url     : https://prove2.me/submissions/83142e17-fc37-45c6-930d-3996cb7dbbfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Theorems.Thm_P2M_GlobalTheory_SiteCoh_equiv__terminalEquiv_79b4d00cc8cf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
open GlobalTheory.coh
namespace GlobalTheory.coh
theorem _root_.solution (F : X.Modules) (x : coh F 0) :
    Sheaf.H.equiv₀ ((toAbSheaf X).obj F) isTerminalTop (toH F 0 x) = zeroEquiv F x :=
  SiteCoh.equiv₀_terminalEquiv ((toAbSheaf X).obj F) isTerminalTop (cohOn.toH' F ⊤ 0 x)
end GlobalTheory.coh
