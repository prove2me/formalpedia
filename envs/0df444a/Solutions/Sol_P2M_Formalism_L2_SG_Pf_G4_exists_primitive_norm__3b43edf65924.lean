-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_G4_exists_primitive_norm__3b43edf65924
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:51:15.732833+00:00
-- url     : https://prove2.me/submissions/6bfd1c6a-ef9e-44f5-bfc7-8d32db510d84

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AdelicThetaPoissonSummation
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_G4_exists_primitive__0bf0807a5daa
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_exists_norm_one_mul_mem


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
theorem _root_.solution (hS : IsHermSemilocal S) (hM : IsLatIn S h W M) {ξ : V} (hξ : ξ ∈ W)
    {u : K} (hu : IsUnitIn S u) (hξu : h ξ ξ = u) :
    ∃ y ∈ M, y ≠ 0 ∧ (∃ l : K, y = l • ξ) ∧ (∀ c : K, c • y ∈ M → c ∈ S) ∧
      ∃ a ∈ S, h y y = star a * a * u := by
  have hu0 : u ≠ 0 := hu.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    apply hu0
    rw [← hξu]
    simp
  obtain ⟨l, hl0, hlM, hprim⟩ := exists_primitive' hS hM hξ hξ (by rw [hξu]; exact hu0)
  have hyy : h (l • ξ) (l • ξ) = star l * l * u := by
    rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply, hξu]
    ring
  have hN : star l * l ∈ S := by
    have hi := hM.int _ hlM _ hlM
    rw [hyy] at hi
    have e := S.mul_mem hi hu.2.2
    rwa [mul_assoc, mul_inv_cancel₀ hu0, mul_one] at e
  obtain ⟨b, hb1, hbS⟩ := Formalism.HermitianLattices.Ext.L3.WA.exists_norm_one_mul_mem hS hN
  refine ⟨l • ξ, hlM, smul_ne_zero hl0 hξ0, ⟨l, rfl⟩, fun c hc => ?_, l * b, hbS, ?_⟩
  · have e := hprim (c * l) (by rwa [mul_smul])
    rwa [mul_assoc, mul_inv_cancel₀ hl0, mul_one] at e
  · rw [hyy, star_mul]
    linear_combination (-(star l * l * u)) * hb1
end Formalism.L2.SG.Pf.G4
