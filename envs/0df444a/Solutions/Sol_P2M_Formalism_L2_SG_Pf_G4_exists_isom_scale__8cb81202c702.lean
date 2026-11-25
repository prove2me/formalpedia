-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_G4_exists_isom_scale__8cb81202c702
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:45:34.744798+00:00
-- url     : https://prove2.me/submissions/7689c492-df6d-4da5-a2fb-e9ce4837af21

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AdelicThetaPoissonSummation
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsIsomScale
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_isom_scale


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
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.L2.SG.Pf.G4
theorem _root_.solution (hs : h.IsSymm) {z : V} (hz : h z z ≠ 0) {b : K} (hb : star b * b = 1) :
    ∃ ψ ∈ Formalism.HermitianLatticesTheory.isom h, ψ z = b • z ∧ (∀ v, h z v = 0 → ψ v = v) ∧
      ∀ W : Submodule K V, z ∈ W → ∀ v, v ∈ W ↔ ψ v ∈ W := by
  obtain ⟨ψ, hψ, hψz, hψv⟩ := exists_isom_scale hs hz hb
  refine ⟨ψ, hψ, hψz, hψv, ?_⟩
  intro W hzW v
  have hdec : h z (v - (h z v * (h z z)⁻¹) • z) = 0 := by
    rw [map_sub, map_smul, smul_eq_mul, inv_mul_cancel_right₀ hz, sub_self]
  have hψv' : ψ v = (h z v * (h z z)⁻¹) • (b • z) + (v - (h z v * (h z z)⁻¹) • z) := by
    have e : v = (h z v * (h z z)⁻¹) • z + (v - (h z v * (h z z)⁻¹) • z) := by abel
    conv_lhs => rw [e]
    rw [map_add, map_smul, hψz, hψv _ hdec]
  constructor
  · intro hv
    rw [hψv']
    exact W.add_mem (W.smul_mem _ (W.smul_mem _ hzW)) (W.sub_mem hv (W.smul_mem _ hzW))
  · intro hv
    rw [hψv'] at hv
    have h1 := W.sub_mem hv (W.smul_mem (h z v * (h z z)⁻¹) (W.smul_mem b hzW))
    rw [add_sub_cancel_left] at h1
    have h2 := W.add_mem h1 (W.smul_mem (h z v * (h z z)⁻¹) hzW)
    rwa [sub_add_cancel] at h2
end Formalism.L2.SG.Pf.G4
