-- Prove2me | solution 1 for SmartPTO.Fisher.prop3_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:21:31.510573+00:00
-- url     : https://prove2.me/submissions/ff912a32-9d3a-4943-9ea6-b7010dc7648a

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SmartPTO_Fisher_Setting
set_option autoImplicit false
open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory
open SmartPTO.Fisher

theorem gg_xi_le {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hScpt : IsCompact S)
    (u w : EuclideanSpace ℝ (Fin d)) (hw : w ∈ S) : ⟪u, w⟫_ℝ ≤ xi S u := by
  have hb : BddAbove ((fun w => ⟪u, w⟫_ℝ) '' S) :=
    (hScpt.image (continuous_const.inner continuous_id)).bddAbove
  exact le_csSup hb ⟨w, hw, rfl⟩

theorem gg_xi_le_of {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSne : S.Nonempty)
    (u : EuclideanSpace ℝ (Fin d)) (b : ℝ) (h : ∀ w ∈ S, ⟪u, w⟫_ℝ ≤ b) : xi S u ≤ b := by
  apply csSup_le (hSne.image _)
  rintro _ ⟨w, hw, rfl⟩
  exact h w hw

theorem solution {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hw : SPOBounds.Natarajan.IsOracle S wstar)
    (c chat : EuclideanSpace ℝ (Fin d)) :
    spoLoss S chat c ≤ spoPlusLoss S wstar chat c := by
  unfold spoLoss spoPlusLoss
  have hne : (Wstar S chat).Nonempty := by
    obtain ⟨w, hwS, hwm⟩ := hScpt.exists_isMinOn hSne
      (continuous_const.inner continuous_id : Continuous fun w : EuclideanSpace ℝ (Fin d) => ⟪chat, w⟫_ℝ).continuousOn
    exact ⟨w, hwS, fun v hv => isMinOn_iff.mp hwm v hv⟩
  have key : sSup ((fun w => ⟪c, w⟫_ℝ) '' Wstar S chat) ≤
      xi S (c - (2 : ℝ) • chat) + 2 * ⟪chat, wstar c⟫_ℝ := by
    apply csSup_le (hne.image _)
    rintro _ ⟨w, ⟨hwS, hwmin⟩, rfl⟩
    have h1 : ⟪c - (2 : ℝ) • chat, w⟫_ℝ ≤ xi S (c - (2 : ℝ) • chat) :=
      gg_xi_le S hScpt _ w hwS
    have h2 : ⟪chat, w⟫_ℝ ≤ ⟪chat, wstar c⟫_ℝ := hwmin _ (hw c).1
    have h3 : ⟪c, w⟫_ℝ = ⟪c - (2 : ℝ) • chat, w⟫_ℝ + 2 * ⟪chat, w⟫_ℝ := by
      rw [inner_sub_left, real_inner_smul_left]; ring
    linarith
  linarith
