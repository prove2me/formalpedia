-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_G4_IsSD_exists_norm__3019c7167a34
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:29:37.597988+00:00
-- url     : https://prove2.me/submissions/dd459d74-db2c-4872-a906-b566d9850a81

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AdelicThetaPoissonSummation
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_G4_exists_primitive_norm__3b43edf65924
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_exists_not_dv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_norm_of_not_dv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G4
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
namespace Formalism.L2.SG.Pf.G4
namespace IsSD
theorem _root_.solution (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hM : IsSD S h W M) {ξ : V} (hξ : ξ ∈ W) {u : K}
    (hu : IsUnitIn S u) (hξu : h ξ ξ = u) : ∃ X ∈ M, h X X = u := by
  obtain ⟨y, hy, -, -, hprim, a, ha, hyy⟩ := exists_primitive_norm' hS hM.toIsLatIn hξ hu hξu
  obtain ⟨w, hw, hn⟩ := hM.exists_not_dv hπ hy hprim
  have huf : star u = u := by
    have e : starRingEnd K (h ξ ξ) = h ξ ξ := by
      first
        | exact hs ξ ξ
        | exact hs.eq ξ ξ
    rw [hξu, starRingEnd_apply] at e
    exact e
  exact exists_norm_of_not_dv hS hπ hs hM.smul_mem hM.int hy hw ha hu huf hyy hn
end IsSD
end Formalism.L2.SG.Pf.G4
