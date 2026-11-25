-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_levi_phi_pos_86b952d26614
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:10:30.300317+00:00
-- url     : https://prove2.me/submissions/cf903319-f13e-426f-8cf9-630bf83459d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_leviForm_phi_29693f206fdb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_sum_line_820fc4227819
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_lagrange_9c3712389ff7

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
theorem _root_.solution {z w : (Σ _ : Unit, Fin 2) → ℂ} (hz : ∃ i, z ⟨(), i⟩ ≠ 0)
    (hw : ∀ c : ℂ, w ≠ fun p => c * z p) : 0 < leviForm phi z w := by
  have hS : sqSum z ≠ 0 := by
    obtain ⟨i, hi⟩ := hz
    refine ne_of_gt (lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) ?_)
    exact Finset.single_le_sum (f := fun p => ‖z p‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ (⟨(), i⟩ : Σ _ : Unit, Fin 2))
  rw [leviForm_phi hS, lagrange]
  refine div_pos (Complex.normSq_pos.mpr fun h0 => ?_) (by positivity)
  rw [sub_eq_zero] at h0
  have hcases : ∀ p : Σ _ : Unit, Fin 2, p = ⟨(), 0⟩ ∨ p = ⟨(), 1⟩ := by
    rintro ⟨⟨⟩, j⟩
    fin_cases j <;> simp
  by_cases hz0 : z ⟨(), 0⟩ = 0
  · have hz1 : z ⟨(), 1⟩ ≠ 0 := fun h1 => hS (by simp [sqSum, sum_line, hz0, h1])
    apply hw (w ⟨(), 1⟩ / z ⟨(), 1⟩)
    funext p
    rcases hcases p with rfl | rfl
    · rw [hz0, zero_mul] at h0
      have hw0 : w ⟨(), 0⟩ = 0 := by
        rcases mul_eq_zero.mp h0.symm with h | h
        · exact absurd h hz1
        · exact h
      rw [hw0, hz0, mul_zero]
    · rw [div_mul_cancel₀ _ hz1]
  · apply hw (w ⟨(), 0⟩ / z ⟨(), 0⟩)
    funext p
    rcases hcases p with rfl | rfl
    · rw [div_mul_cancel₀ _ hz0]
    · rw [div_mul_eq_mul_div, eq_div_iff hz0]
      linear_combination h0
end GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
