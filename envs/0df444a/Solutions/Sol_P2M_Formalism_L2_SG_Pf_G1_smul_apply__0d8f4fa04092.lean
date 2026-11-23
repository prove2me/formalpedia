-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_G1_smul_apply__0d8f4fa04092
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:24.164961+00:00
-- url     : https://prove2.me/submissions/6d7b15b3-f440-49dd-99ab-fd5b41c3db1b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K}
namespace Formalism.L2.SG.Pf.G1
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (x y : V) : (c • h) x y = c * h x y := by
  simp only [LinearMap.smul_apply, smul_eq_mul]
end Formalism.L2.SG.Pf.G1
