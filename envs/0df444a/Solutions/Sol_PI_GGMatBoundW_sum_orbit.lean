-- Prove2me | solution 1 for PI.GGMatBoundW.sum_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:06.018035+00:00
-- url     : https://prove2.me/submissions/759bc374-a35b-4bd4-82c8-5b4f49b15281

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_GammaMatrixInverse
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_MatrixCoefficientEquation
import Theorems.Thm_PI_GGMatBoundW_eq_of_smul_eq_of_free

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {G : Type} [Group G] {X : Type} [MulAction Gᵐᵒᵖ X]
namespace PI.GGMatBoundW
theorem _root_.solution [Fintype G] (hfree : ∀ (x : Gᵐᵒᵖ) (j : X), x • j = j → x = 1) (d : X → X → G)
    (hd : ∀ i j, (∃ x : Gᵐᵒᵖ, x • j = i) → MulOpposite.op (d i j) • j = i) (f : G → ℂ) (i j : X) :
    (∑ x : G, if MulOpposite.op x • j = i then f x else 0) =
      if ∃ x : Gᵐᵒᵖ, x • j = i then f (d i j) else 0 := by
  by_cases h : ∃ x : Gᵐᵒᵖ, x • j = i
  · rw [if_pos h]
    have hdij := hd i j h
    rw [Finset.sum_eq_single (d i j)]
    · rw [if_pos hdij]
    · intro b _ hb
      rw [if_neg]
      intro hbj
      exact hb (MulOpposite.op_injective (eq_of_smul_eq_of_free hfree (hbj.trans hdij.symm)))
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg]
    intro hx
    exact h ⟨_, hx⟩
end PI.GGMatBoundW
