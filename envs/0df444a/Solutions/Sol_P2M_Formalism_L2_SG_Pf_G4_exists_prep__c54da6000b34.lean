-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_G4_exists_prep__c54da6000b34
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:31:10.891867+00:00
-- url     : https://prove2.me/submissions/b47454d5-b240-4f2c-a8e9-60e335704d40

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AdelicThetaPoissonSummation
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsIsomScale
import Theorems.Thm_Formalism_L2_SG_Pf_G4_exists_isom_map_of_eq_norm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_cutW


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
theorem _root_.solution (hs : h.IsSymm) (h2 : (2 : K) ≠ 0) {W₁ W₂ : Submodule K V}
    {φ : V ≃ₗ[K] V} (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom h) (hW : ∀ v, v ∈ W₁ ↔ φ v ∈ W₂) {x X : V}
    (hx : x ∈ W₁) (hX : X ∈ W₂) (hxX : h x x = h X X) (hx0 : h x x ≠ 0) :
    ∃ φ' ∈ Formalism.HermitianLatticesTheory.isom h, φ' x = X ∧ (∀ v, v ∈ cutW h W₁ x ↔ φ' v ∈ cutW h W₂ X) ∧
      ∀ v, (∀ w ∈ W₁, h w v = 0) → φ' v = φ v := by
  have hφ' : ∀ a c, h (φ a) (φ c) = h a c := hφ
  have hφx : φ x ∈ W₂ := (hW x).1 hx
  have hn : h (φ x) (φ x) = h X X := by rw [hφ' x x]; exact hxX
  have hn0 : h (φ x) (φ x) ≠ 0 := by rw [hφ' x x]; exact hx0
  obtain ⟨τ, hτ, hτx, hτv, hτW⟩ := exists_isom_map_of_eq_norm hs h2 hn hn0
  have hτ' : ∀ a c, h (τ a) (τ c) = h a c := hτ
  refine ⟨τ * φ, mul_mem hτ hφ, hτx, ?_, ?_⟩
  · intro v
    show v ∈ cutW h W₁ x ↔ τ (φ v) ∈ cutW h W₂ X
    rw [mem_cutW, mem_cutW, ← hτW W₂ hφx hX (φ v), ← hW v, ← hτx, hτ' (φ x) (φ v), hφ' x v]
  · intro v hv
    show τ (φ v) = φ v
    apply hτv
    · rw [hφ' x v]
      exact hv x hx
    · obtain ⟨x', rfl⟩ := φ.surjective X
      rw [hφ' x' v]
      exact hv x' ((hW x').2 hX)
end Formalism.L2.SG.Pf.G4
