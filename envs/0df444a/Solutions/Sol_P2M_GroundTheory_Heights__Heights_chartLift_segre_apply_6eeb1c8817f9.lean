-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chartLift_segre_apply_6eeb1c8817f9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:20.024712+00:00
-- url     : https://prove2.me/submissions/fc87c6f6-a493-4085-9dbd-f752a6a36cad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StokesObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (MRing mcPts segre PBlk)
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (z : (Σ k, ι k) → ℂ) (hz : segre z i = 1) (k : K) (j : ι k) :
    chartLift σ i (fun a => segre z (σ a)) ⟨k, j⟩ = z ⟨k, j⟩ * (z ⟨k, i k⟩)⁻¹ := by
  have hne : z ⟨k, i k⟩ ≠ 0 := fun h0 => by
    have : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [hz] at this
    exact one_ne_zero this
  have hupd : (fun k' => z ⟨k', Function.update i k j k'⟩) =
      Function.update (fun k' => z ⟨k', i k'⟩) k (z ⟨k, j⟩) := by
    funext k'
    by_cases h : k' = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  have hprod : segre z (Function.update i k j) = z ⟨k, j⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i k'⟩ := by
    simp only [segre]
    rw [hupd, Finset.prod_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hall : z ⟨k, i k⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i k'⟩ = 1 := by
    rw [Finset.mul_prod_erase _ (fun k' => z ⟨k', i k'⟩) (Finset.mem_univ k)]
    exact hz
  simp only [chartLift, Equiv.apply_symm_apply]
  rw [hprod]
  field_simp
  linear_combination z ⟨k, j⟩ * hall
end GroundTheory.Heights₂.Heights
