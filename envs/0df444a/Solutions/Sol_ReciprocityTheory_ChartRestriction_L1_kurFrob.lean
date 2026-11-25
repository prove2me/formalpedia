-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kurFrob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:36:46.618148+00:00
-- url     : https://prove2.me/submissions/fc58203b-a199-4714-9acf-e0d3d3db1bb1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KmuInclDenseRange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kmuIncl_norm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kmuIncl_isometry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kmuIncl_denseRange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kmu_sigma
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kur_complete
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kur_discrete
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_l_Cl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution : ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, FrobField (MaximalUnramifiedExtension l) l σ := by
  obtain ⟨s, hs1, hs2⟩ := kmu_sigma l
  have : CompleteSpace (MaximalUnramifiedExtension l) := kur_complete l
  have hiso : Isometry ((kmuIncl l).comp s) :=
    AddMonoidHomClass.isometry_of_norm _ (fun x => by
      rw [RingHom.comp_apply, kmuIncl_norm, hs1])
  let σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l :=
    IsDenseInducing.extendRingHom (i := kmuIncl l) (f := (kmuIncl l).comp s)
      (kmuIncl_isometry l).isUniformInducing (kmuIncl_denseRange l) hiso.uniformContinuous
  have hdi : IsDenseInducing (kmuIncl l) :=
    (kmuIncl_isometry l).isUniformInducing.isDenseInducing (kmuIncl_denseRange l)
  have hσc : Continuous σ :=
    (uniformContinuous_uniformly_extend (kmuIncl_isometry l).isUniformInducing
      (kmuIncl_denseRange l) hiso.uniformContinuous).continuous
  have hσi : ∀ x : Kmu l, σ (kmuIncl l x) = kmuIncl l (s x) := fun x =>
    hdi.extend_eq hiso.continuous x
  have hl : ‖(l : MaximalUnramifiedExtension l)‖ = ‖(l : ℂ_[l])‖ := rfl
  refine ⟨σ, Fact.out, ?_, ?_, ?_, ?_⟩
  · rw [hl, norm_l_Cl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  · intro x
    refine (kmuIncl_denseRange l).induction_on (p := fun x => ‖σ x‖ = ‖x‖) x
      (isClosed_eq hσc.norm continuous_norm) (fun y => ?_)
    rw [hσi, kmuIncl_norm, kmuIncl_norm, hs1]
  · intro x hx
    have hopen : IsOpen (Metric.closedBall (0 : MaximalUnramifiedExtension l) 1) :=
      IsUltrametricDist.isOpen_closedBall _ one_ne_zero
    have hmem : x ∈ closure (Metric.closedBall (0 : MaximalUnramifiedExtension l) 1 ∩ Set.range (kmuIncl l)) :=
      (kmuIncl_denseRange l).open_subset_closure_inter hopen (by simpa using hx)
    have hcl : IsClosed {x : MaximalUnramifiedExtension l | ‖σ x - x ^ l‖ ≤ ‖(l : MaximalUnramifiedExtension l)‖} :=
      isClosed_le (hσc.sub (continuous_pow l)).norm continuous_const
    refine closure_minimal ?_ hcl hmem
    rintro _ ⟨hy1, y, rfl⟩
    have hy : ‖y‖ ≤ 1 := by
      rw [mem_closedBall_zero_iff, kmuIncl_norm] at hy1
      exact hy1
    have := hs2 y hy
    show ‖σ (kmuIncl l y) - (kmuIncl l y) ^ l‖ ≤ ‖(l : MaximalUnramifiedExtension l)‖
    rw [hσi, ← map_pow, ← map_sub, kmuIncl_norm]
    exact this
  · intro x hx
    exact kur_discrete l x.2 hx
end ReciprocityTheory.ChartRestriction.L1
