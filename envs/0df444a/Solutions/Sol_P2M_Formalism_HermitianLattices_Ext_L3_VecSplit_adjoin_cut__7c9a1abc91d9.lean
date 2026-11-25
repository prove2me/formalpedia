-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_adjoin_cut__7c9a1abc91d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:33.141055+00:00
-- url     : https://prove2.me/submissions/d19836c5-270b-48f3-8263-499ca8dfb534

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_h_x__comb_726bcd8e9864
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_mem_adjoin_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_mem_cut_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L) : S.adjoin (S.cut L) = L := by
  apply le_antisymm
  · unfold VecSplit.adjoin VecSplit.cut
    exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx) (Submodule.map_comap_le _ _)
  · intro v hv
    obtain ⟨c, a, rfl⟩ := S.cover v
    have hc : c ∈ (1 : Submodule (𝓞 K) K) := by
      have := hL S.x₀ hx _ hv
      rwa [S.h_x₀_comb, h1, mul_one] at this
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hc
    rw [S.mem_adjoin_iff]
    refine ⟨r, a, ?_, by rw [hr]⟩
    rw [S.mem_cut_iff]
    have e : S.ι a = (c • S.x₀ + S.ι a) - (algebraMap (𝓞 K) K r) • S.x₀ := by
      rw [hr]
      abel
    rw [e]
    refine L.sub_mem hv ?_
    rw [algebraMap_smul]
    exact L.smul_mem r hx
end Formalism.HermitianLattices.Ext.L3.VecSplit
