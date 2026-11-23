-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isLattice_adjoin_iff__9a69000cf349
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:21.655148+00:00
-- url     : https://prove2.me/submissions/bc438e4c-48c8-4fdf-9330-a79d13adb75f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_comb_eq_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_mem_adjoin_iff
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_x__mem_adjoin__3068ade258cb
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
theorem _root_.solution (L' : Submodule (𝓞 K) V') :
    Submodule.IsLattice K (S.adjoin L') ↔ Submodule.IsLattice K L' := by
  constructor
  · intro hL
    have hFG : (L'.map (S.ι.restrictScalars (𝓞 K))).FG :=
      hL.fg.of_le (by unfold VecSplit.adjoin; exact le_sup_right)
    refine ⟨Submodule.fg_of_fg_map_injective (S.ι.restrictScalars (𝓞 K)) S.inj hFG, ?_⟩
    rw [eq_top_iff]
    intro a _
    have key : ∀ v ∈ Submodule.span K (S.adjoin L' : Set V), ∃ (c : K) (b : V'),
        b ∈ Submodule.span K (L' : Set V') ∧ v = c • S.x₀ + S.ι b := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨r, b, hb, rfl⟩ := (S.mem_adjoin_iff L' x).1 hx
        exact ⟨_, b, Submodule.subset_span hb, rfl⟩
      | zero => exact ⟨0, 0, zero_mem _, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨c, b, hb, rfl⟩ := hx
        obtain ⟨c', b', hb', rfl⟩ := hy
        exact ⟨c + c', b + b', add_mem hb hb', by rw [map_add, add_smul]; abel⟩
      | smul k x _ hx =>
        obtain ⟨c, b, hb, rfl⟩ := hx
        exact ⟨k * c, k • b, Submodule.smul_mem _ k hb, by rw [smul_add, map_smul, smul_smul]⟩
    have hmem : S.ι a ∈ Submodule.span K (S.adjoin L' : Set V) := by
      rw [hL.span_eq_top]
      exact Submodule.mem_top
    obtain ⟨c, b, hb, he⟩ := key _ hmem
    have hc : (0 : K) • S.x₀ + S.ι a = c • S.x₀ + S.ι b := by
      rw [zero_smul, zero_add]
      exact he
    rw [(S.comb_eq_iff.1 hc).2]
    exact hb
  · intro hL
    refine ⟨?_, ?_⟩
    · unfold VecSplit.adjoin
      exact (Submodule.fg_span_singleton _).sup (hL.fg.map _)
    · rw [eq_top_iff]
      intro v _
      obtain ⟨c, a, rfl⟩ := S.cover v
      refine add_mem (Submodule.smul_mem _ c (Submodule.subset_span (S.x₀_mem_adjoin' L'))) ?_
      have ha : a ∈ Submodule.span K (L' : Set V') := by
        rw [hL.span_eq_top]
        exact Submodule.mem_top
      have hle : Submodule.map S.ι (Submodule.span K (L' : Set V')) ≤
          Submodule.span K (S.adjoin L' : Set V) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨b, hb, rfl⟩
        unfold VecSplit.adjoin
        exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hb)
      exact hle (Submodule.mem_map_of_mem ha)
end Formalism.HermitianLattices.Ext.L3.VecSplit
