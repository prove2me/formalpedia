-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isOrthoLattice_adjoin__de5b3f982f95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:36.850221+00:00
-- url     : https://prove2.me/submissions/c10f2c62-c4e9-4876-9f4e-0e286366f1fd

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_x__not_mem_range_04f72e8df2db
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_orth__ee462835f427
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
theorem _root_.solution (hs : h.IsSymm) (h1 : h S.x₀ S.x₀ = 1)
    {I' : Submodule (𝓞 K) V'} {n : ℕ} (hI' : Formalism.HermitianLatticesTheory.IsOrthoLattice h' I' n) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice h (S.adjoin I') (n + 1) := by
  obtain ⟨e', hli, hspan, hI'eq, horth⟩ := hI'
  refine ⟨Fin.cons S.x₀ (fun j => S.ι (e' j)), ?_, ?_, ?_, ?_⟩
  · rw [linearIndependent_fin_cons]
    refine ⟨hli.map' S.ι (LinearMap.ker_eq_bot.mpr S.inj), fun hmem => ?_⟩
    have hle : Submodule.span K (Set.range (fun j => S.ι (e' j))) ≤ LinearMap.range S.ι := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨e' j, rfl⟩
    obtain ⟨a, ha⟩ := hle hmem
    exact S.x₀_not_mem_range a ha
  · rw [eq_top_iff]
    intro v _
    obtain ⟨c, a, rfl⟩ := S.cover v
    rw [Fin.range_cons]
    have ha : a ∈ Submodule.span K (Set.range e') := by
      rw [hspan]
      exact Submodule.mem_top
    refine Submodule.add_mem _ (Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_insert _ _))) ?_
    have hm : S.ι a ∈ (Submodule.span K (Set.range e')).map S.ι := Submodule.mem_map_of_mem ha
    rw [Submodule.map_span] at hm
    refine Submodule.span_mono ?_ hm
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact Set.mem_insert_of_mem _ ⟨j, rfl⟩
  · rw [Fin.range_cons, Submodule.span_insert, hI'eq]
    unfold VecSplit.adjoin
    congr 1
    rw [Submodule.map_span]
    congr 1
    ext v
    simp
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [h1]
    · simp [S.orth, (Fin.succ_ne_zero _).symm]
    · simp [S.orth' hs, Fin.succ_ne_zero]
    · simp [S.isom, horth]
end Formalism.HermitianLattices.Ext.L3.VecSplit
