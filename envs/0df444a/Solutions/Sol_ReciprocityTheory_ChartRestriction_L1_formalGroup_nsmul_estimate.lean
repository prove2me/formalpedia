-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.formalGroup_nsmul_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:53:20.945426+00:00
-- url     : https://prove2.me/submissions/6d7517d7-570c-4630-a5b5-0ad77bfe77e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorChord
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorContr
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_ELL_formal_group_points_subgroup
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_formalGroup_add_estimate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_formalGroup_param_norm_lt_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)
variable {C : Type} [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (W : WeierstrassCurve C) (hW : IntegralModel W) (hΔ : ‖W.Δ‖ = 1)
    (D : W.toAffine.Point) (hD : InFormalGroupPoints D) (n : ℕ) :
    InFormalGroupPoints (n • D) ∧ ‖uOf (n • D) - (n : C) * uOf D‖ ≤ ‖uOf D‖ ^ 2 := by
  have hu : ‖uOf D‖ < 1 := formalGroup_param_norm_lt_one W hW D hD
  have hsq : ‖uOf D‖ ^ 2 ≤ ‖uOf D‖ := by
    have h0 := norm_nonneg (uOf D)
    nlinarith
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [zero_smul]; exact (trivial : InFormalGroupPoints (Affine.Point.zero : W.toAffine.Point))
    · rw [zero_smul]
      have : uOf (0 : W.toAffine.Point) = 0 := rfl
      rw [this]; simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hin : InFormalGroupPoints (n • D + D) := (formal_group_points_subgroup C W hW hΔ (n • D) D h1 hD).1
    have hn : ‖(n : C)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one C n
    have hnu : ‖(n : C) * uOf D‖ ≤ ‖uOf D‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hn
    have hb : ‖uOf (n • D)‖ ≤ ‖uOf D‖ := by
      have e : uOf (n • D) = (uOf (n • D) - (n : C) * uOf D) + (n : C) * uOf D := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h2.trans hsq) hnu)
    have hadd := formalGroup_add_estimate W hW (n • D) D h1 hD
    rw [max_eq_right hb] at hadd
    rw [succ_nsmul]
    refine ⟨hin, ?_⟩
    have e : uOf (n • D + D) - ((n + 1 : ℕ) : C) * uOf D
        = (uOf (n • D + D) - uOf (n • D) - uOf D) + (uOf (n • D) - (n : C) * uOf D) := by
      push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hadd h2)
end ReciprocityTheory.ChartRestriction.L1
