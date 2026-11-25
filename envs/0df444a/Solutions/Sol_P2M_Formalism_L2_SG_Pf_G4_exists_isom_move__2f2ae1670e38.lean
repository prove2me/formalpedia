-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_G4_exists_isom_move__2f2ae1670e38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:45:33.574402+00:00
-- url     : https://prove2.me/submissions/b2e5a74b-3bbe-403d-8b98-e0ae9c71e6a3

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AdelicThetaPoissonSummation
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsIsomScale
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq


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
theorem _root_.solution (hs : h.IsSymm) {x y : V} (hxy : h x x = h y y)
    (hb : h x x - h y x ≠ 0) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ (∀ v, h x v = 0 → h y v = 0 → τ v = v) ∧
      ∀ W : Submodule K V, x ∈ W → y ∈ W → ∀ v, v ∈ W ↔ τ v ∈ W := by
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => by
    rw [← starRingEnd_apply]
    exact hs.eq u v
  obtain ⟨z, hz⟩ : ∃ z, z = x - y := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b, b = h x x - h y x := ⟨_, rfl⟩
  have hb0 : b ≠ 0 := hbd ▸ hb
  have hsb0 : star b ≠ 0 := star_ne_zero.2 hb0
  have hzx : h z x = b := by
    rw [hz, hbd, map_sub, LinearMap.sub_apply]
  have hzv : ∀ v, h z v = h x v - h y v := fun v => by
    rw [hz, map_sub, LinearMap.sub_apply]
  have hzz : h z z = b + star b := by
    have h1 : star b = h x x - h x y := by
      rw [hbd, star_sub, hsym, hsym]
    rw [h1, hbd, hzv, hz, map_sub, map_sub, hxy]
    ring
  let τl : V →ₗ[K] V := LinearMap.id - (b⁻¹ • h z).smulRight z
  let σl : V →ₗ[K] V := LinearMap.id - ((star b)⁻¹ • h z).smulRight z
  have hτ : ∀ v, τl v = v - (b⁻¹ * h z v) • z := fun v => rfl
  have hσ : ∀ v, σl v = v - ((star b)⁻¹ * h z v) • z := fun v => rfl
  have key : ∀ c d : K, c + d = c * d * h z z → ∀ v : V,
      (v - (c * h z v) • z) - (d * h z (v - (c * h z v) • z)) • z = v := by
    intro c d hcd v
    rw [map_sub, map_smul, smul_eq_mul, sub_sub, ← add_smul]
    have h0 : c * h z v + d * (h z v - c * h z v * h z z) = 0 := by
      linear_combination (h z v) * hcd
    rw [h0, zero_smul, sub_zero]
  have hcd : (star b)⁻¹ + b⁻¹ = (star b)⁻¹ * b⁻¹ * h z z := by
    rw [hzz]
    field_simp
    try ring
  have h₁ : τl.comp σl = LinearMap.id := by
    apply LinearMap.ext
    intro v
    show τl (σl v) = v
    rw [hτ, hσ]
    exact key _ _ hcd v
  have h₂ : σl.comp τl = LinearMap.id := by
    apply LinearMap.ext
    intro v
    show σl (τl v) = v
    rw [hσ, hτ]
    exact key _ _ (by rw [add_comm, mul_comm b⁻¹]; exact hcd) v
  refine ⟨LinearEquiv.ofLinear τl σl h₁ h₂, ?_, ?_, ?_, ?_⟩
  · show ∀ u v, h (τl u) (τl v) = h u v
    intro u v
    rw [hτ, hτ]
    have hu : h u z = star (h z u) := (hsym z u).symm
    simp only [map_sub, map_smulₛₗ, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply, star_mul, star_inv₀, RingHom.id_apply, hu, hzz]
    field_simp
    try ring
  · show τl x = y
    rw [hτ, hzx, inv_mul_cancel₀ hb0, one_smul, hz, sub_sub_cancel]
  · intro v hxv hyv
    show τl v = v
    rw [hτ, hzv, hxv, hyv, sub_zero, mul_zero, zero_smul, sub_zero]
  · intro W hxW hyW v
    have hzW : z ∈ W := hz ▸ W.sub_mem hxW hyW
    show v ∈ W ↔ τl v ∈ W
    rw [hτ]
    constructor
    · intro hv
      exact W.sub_mem hv (W.smul_mem _ hzW)
    · intro hv
      have := W.add_mem hv (W.smul_mem (b⁻¹ * h z v) hzW)
      rwa [sub_add_cancel] at this
end Formalism.L2.SG.Pf.G4
