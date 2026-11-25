-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_G4_IsSD_exists_unit_norm__db471541043b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:45:32.46753+00:00
-- url     : https://prove2.me/submissions/789d6d0a-45b4-4ea7-bf24-4ec2d3bcd6a2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AdelicThetaPoissonSummation
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_G4_exists_primitive__0bf0807a5daa
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_exists_unit_norm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_exists_not_dv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_exists_unit_norm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_unit_norm


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
    (hnd : NondegOn h W) (hM : IsSD S h W M) {ξ : V} (hξ : ξ ∈ W) (hξ0 : ξ ≠ 0) :
    ∃ x ∈ M, IsUnitIn S (h x x) := by
  obtain ⟨w, hw, hn⟩ := hnd ξ hξ hξ0
  obtain ⟨l, hl0, hlM, hprim⟩ := exists_primitive' hS hM.toIsLatIn hξ hw hn
  have hprim' : ∀ c : K, c • (l • ξ) ∈ M → c ∈ S := by
    intro c hc
    have e := hprim (c * l) (by rwa [mul_smul])
    rwa [mul_assoc, mul_inv_cancel₀ hl0, mul_one] at e
  obtain ⟨w', hw', hn'⟩ := hM.exists_not_dv hπ hlM hprim'
  exact exists_unit_norm hS hπ hs hM.smul_mem hM.int hlM hw' hn'
end IsSD
end Formalism.L2.SG.Pf.G4
