-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TelescopingSum_comp_swap_1fad1a80f92e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:22:25.439085+00:00
-- url     : https://prove2.me/submissions/e9f7e8f6-c66d-4b42-9d21-6804cf881c51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDerived
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PTelescope

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.TelescopingSum
namespace GroundTheory.Heights₂.Heights.TelescopingSum
theorem _root_.solution {α : Type*} (D k : ℕ) (hk : k < D + 1) (X Y : α) (m : ℕ) (hm : m = k ∨ m = k + 1) :
    (fun j : Fin (D + 1) => if (j : ℕ) < m then X else Y) ∘ Equiv.swap ⟨k, hk⟩ (Fin.last D) =
      Fin.snoc (fun j : Fin D => if (j : ℕ) < k then X else Y) (if k < m then X else Y) := by
  funext j
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp [Equiv.swap_apply_right]
  · simp only [Function.comp_apply, Fin.snoc_castSucc]
    by_cases h : (j' : ℕ) = k
    · have hj : Fin.castSucc j' = ⟨k, hk⟩ := Fin.ext (by simp [h])
      rw [hj, Equiv.swap_apply_left]
      have := j'.isLt
      simp only [Fin.val_last]
      rw [if_neg (by omega), if_neg (by omega)]
    · have h1 : Fin.castSucc j' ≠ ⟨k, hk⟩ := fun e => h (by simpa using congrArg Fin.val e)
      have h2 : Fin.castSucc j' ≠ Fin.last D := Fin.castSucc_ne_last j'
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      simp only [Fin.val_castSucc]
      rcases hm with rfl | rfl
      · rfl
      · by_cases h3 : (j' : ℕ) < k
        · rw [if_pos h3, if_pos (by omega)]
        · rw [if_neg h3, if_neg (by omega)]
end GroundTheory.Heights₂.Heights.TelescopingSum
