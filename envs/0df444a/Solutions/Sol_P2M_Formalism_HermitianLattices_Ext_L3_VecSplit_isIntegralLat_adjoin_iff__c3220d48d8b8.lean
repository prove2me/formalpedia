-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isIntegralLat_adjoin_iff__c3220d48d8b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:35.67541+00:00
-- url     : https://prove2.me/submissions/e4ee4fe0-3055-46b1-8037-91be1158aae7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_mem_adjoin_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_h_comb
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_star_alg_mem_one
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
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open Formalism.HermitianLattices.Ext.L3.VecSplit
variable (S : VecSplit h h')
namespace Formalism.HermitianLattices.Ext.L3.VecSplit
theorem _root_.solution (hs : h.IsSymm) (h1 : h S.x₀ S.x₀ = 1) (L' : Submodule (𝓞 K) V') :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin L') ↔ Formalism.HermitianLatticesTheory.IsIntegralLat h' L' := by
  unfold Formalism.HermitianLatticesTheory.IsIntegralLat
  constructor
  · intro H b hb a ha
    have hb' : S.ι b ∈ S.adjoin L' := (S.mem_adjoin_iff L' _).mpr ⟨0, b, hb, by simp⟩
    have ha' : S.ι a ∈ S.adjoin L' := (S.mem_adjoin_iff L' _).mpr ⟨0, a, ha, by simp⟩
    rw [← S.isom]
    exact H _ hb' _ ha'
  · intro H x hx y hy
    obtain ⟨r, b, hb, rfl⟩ := (S.mem_adjoin_iff L' x).mp hx
    obtain ⟨r', a, ha, rfl⟩ := (S.mem_adjoin_iff L' y).mp hy
    rw [S.h_comb hs h1]
    refine Submodule.add_mem _ ?_ (H b hb a ha)
    obtain ⟨u, hu⟩ := Submodule.mem_one.mp (star_alg_mem_one r)
    exact Submodule.mem_one.mpr ⟨u * r', by rw [map_mul, hu]⟩
end Formalism.HermitianLattices.Ext.L3.VecSplit
