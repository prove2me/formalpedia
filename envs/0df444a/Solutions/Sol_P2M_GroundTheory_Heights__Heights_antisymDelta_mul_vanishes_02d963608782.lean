-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_antisymDelta_mul_vanishes_02d963608782
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:41:32.553437+00:00
-- url     : https://prove2.me/submissions/b5a38bbb-16a5-42b5-b014-e7faafed7c5c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_antisymDelta_eq_zero_2ab9ab7fe6fa

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (T : Type*) [Fintype T] [DecidableEq T] (N j : ℕ)
    (l : MvPolynomial (T × Fin N) ℝ) (τ : T) (a b : Fin N) (ha : a.val < j) (hb : j ≤ b.val) :
    ∃ O : Set (T × Fin N → ℝ), IsOpen O ∧ (O ∩ diagHyperplane T N τ a b).Nonempty ∧
      ∀ x ∈ O ∩ diagHyperplane T N τ a b, eval x (antisymDelta T N * l) = 0 := by
  refine ⟨Set.univ, isOpen_univ, ⟨0, Set.mem_univ _, rfl⟩, fun x hx => ?_⟩
  have hab : a < b := Fin.lt_def.2 (lt_of_lt_of_le ha hb)
  rw [map_mul, eval_antisymDelta_eq_zero T N hab hx.2, zero_mul]
end GroundTheory.Heights₂.Heights
