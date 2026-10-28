-- Prove2me | solution 1 for ResidualsDRO.Wass.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:27:43.781437+00:00
-- url     : https://prove2.me/submissions/9d38502a-098a-4b03-9be8-1311ee68cf54

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Setting

open MeasureTheory

open ResidualsDRO.Wass in
theorem solution {dx dy n : ℕ} (𝒴 : Set (EuclideanSpace ℝ (Fin dy)))
    (h𝒴c : IsClosed 𝒴) (h𝒴v : Convex ℝ 𝒴) (h𝒴n : 𝒴.Nonempty)
    (proj : EuclideanSpace ℝ (Fin dy) → EuclideanSpace ℝ (Fin dy))
    (hproj : IsNearestPointProj 𝒴 proj)
    (fstar fhat : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (xs : Fin n → EuclideanSpace ℝ (Fin dx)) (eps : Fin n → EuclideanSpace ℝ (Fin dy))
    (x : EuclideanSpace ℝ (Fin dx)) (hY : ∀ i, fstar x + eps i ∈ 𝒴) (i : Fin n) :
    ‖proj (fhat x + residual fstar fhat xs eps i) - (fstar x + eps i)‖ ≤
        ‖epsTilde fstar fhat xs eps x i‖ ∧
      epsTilde fstar fhat xs eps x i = (fhat x - fstar x) + (fstar (xs i) - fhat (xs i)) := by
  constructor
  · have hE : epsTilde fstar fhat xs eps x i =
        (fhat x + residual fstar fhat xs eps i) - (fstar x + eps i) := by
      simp only [epsTilde]
    rw [hE]
    generalize fhat x + residual fstar fhat xs eps i = v
    have hyY := hY i
    generalize fstar x + eps i = y at hyY ⊢
    obtain ⟨hPv, hmin⟩ := hproj v
    haveI : Nonempty 𝒴 := ⟨⟨proj v, hPv⟩⟩
    have hinf : ‖v - proj v‖ = ⨅ w : 𝒴, ‖v - w‖ := by
      apply le_antisymm
      · exact le_ciInf (fun w => hmin w.1 w.2)
      · have hbdd : BddBelow (Set.range fun w : 𝒴 => ‖v - (w : EuclideanSpace ℝ (Fin dy))‖) := by
          refine ⟨0, ?_⟩
          rintro _ ⟨w, rfl⟩
          exact norm_nonneg _
        have h1 := ciInf_le hbdd (⟨proj v, hPv⟩ : 𝒴)
        exact h1
    have hvi := (norm_eq_iInf_iff_real_inner_le_zero h𝒴v hPv).mp hinf y hyY
    have hexp : ‖v - y‖ ^ 2 = ‖v - proj v‖ ^ 2 - 2 * inner ℝ (v - proj v) (y - proj v) +
        ‖proj v - y‖ ^ 2 := by
      have e : v - y = (v - proj v) + (proj v - y) := by abel
      rw [e, norm_add_sq_real]
      have : proj v - y = -(y - proj v) := by abel
      rw [this, inner_neg_right, norm_neg]
      ring
    have hsq : ‖proj v - y‖ ^ 2 ≤ ‖v - y‖ ^ 2 := by
      rw [hexp]; nlinarith [sq_nonneg ‖v - proj v‖]
    nlinarith [norm_nonneg (proj v - y), norm_nonneg (v - y)]
  · simp only [epsTilde, ResidualsDRO.Wass.residual]
    abel
