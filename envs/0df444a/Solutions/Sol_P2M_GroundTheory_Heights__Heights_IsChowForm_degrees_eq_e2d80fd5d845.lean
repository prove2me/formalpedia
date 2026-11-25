-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsChowForm_degrees_eq_e2d80fd5d845
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:52:19.575971+00:00
-- url     : https://prove2.me/submissions/e7dc5851-cf19-4af1-811f-b5a2dd515d30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_rename_843ff05dc414
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowFormSwap_457535a64ce2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {k n : ℕ}
variable {R : Type*} [CommRing R]
variable {F : Type} [Field F]
namespace GroundTheory.Heights₂.Heights
namespace IsChowForm
theorem _root_.solution {I : Ideal (MvPolynomial (Fin n) F)} {g : MvPolynomial (Fin k × Fin n) F}
    (hg : IsChowForm I k g) {a : Fin k → ℕ} (ha : ∀ i, IsWeightedHomogeneous (inGroup i) g (a i))
    (i j : Fin k) : a i = a j := by
  obtain ⟨c, hc2, hc⟩ := chowFormSwap F n k I g hg (Equiv.swap i j)
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc2
  have h1 : IsWeightedHomogeneous (inGroup j) (rename (Prod.map (Equiv.swap i j) id) g) (a i) := by
    refine isWeightedHomogeneous_rename ((Equiv.swap i j).injective.prodMap Function.injective_id)
      (fun x => ?_) (ha i)
    simp only [inGroup, Prod.map_fst]
    by_cases h : x.1 = i
    · rw [if_pos h, if_pos (by rw [h, Equiv.swap_apply_left])]
    · rw [if_neg h, if_neg]
      intro h'
      apply h
      have := congrArg (Equiv.swap i j) h'
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
  rw [hc] at h1
  have h2 : IsWeightedHomogeneous (inGroup j) (C c * g) (a j) := (ha j).C_mul c
  exact h1.inj_right (mul_ne_zero (C_ne_zero.mpr hc0) hg.1) h2
end IsChowForm
end GroundTheory.Heights₂.Heights
