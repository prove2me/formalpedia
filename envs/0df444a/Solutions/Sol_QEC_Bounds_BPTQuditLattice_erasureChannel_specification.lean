-- Prove2me | solution 1 for QEC.Bounds.BPTQuditLattice.erasureChannel_specification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:53:42.951337+00:00
-- url     : https://prove2.me/submissions/abaee58a-b76d-47bf-9d2b-3beb91bf84a5

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators
universe u v
open QEC.Bounds.BPTQuditLattice
namespace QEC.Bounds.BPTQuditLattice
theorem _root_.solution (L : BPTQuditLattice) (region : Finset L.Site) :
    L.erasureChannel region = (L.subsystem region).erasureChannelFromRegister :=
  rfl
end QEC.Bounds.BPTQuditLattice
