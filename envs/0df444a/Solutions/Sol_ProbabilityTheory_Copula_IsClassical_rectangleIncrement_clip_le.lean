-- Prove2me | solution 1 for ProbabilityTheory.Copula.IsClassical.rectangleIncrement_clip_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:55:16.660423+00:00
-- url     : https://prove2.me/submissions/1a1bde66-6c97-402e-bf48-1e5371570b0a

module
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_Classical_Approximation
public import Theorems.Thm_ProbabilityTheory_Copula_IsClassical_rectangleIncrement_mono_upper
public import Theorems.Thm_ProbabilityTheory_Copula_rectangleIncrement_eq_zero_of_eq


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval ENNReal BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}
namespace ProbabilityTheory.Copula
namespace IsClassical
theorem _root_.solution (hF : IsClassical F)
    (a b u : Fin d → I) (hab : a ≤ b) :
    rectangleIncrement F (a ⊓ u) (b ⊓ u) ≤ rectangleIncrement F a b := by
  by_cases ha : a ≤ u
  · rw [inf_eq_left.mpr ha]
    exact hF.rectangleIncrement_mono_upper a (b ⊓ u) b (le_inf hab ha) inf_le_left
  · obtain ⟨i, hi⟩ := not_forall.mp ha
    have hua : u i ≤ a i := (not_le.mp hi).le
    rw [rectangleIncrement_eq_zero_of_eq (a ⊓ u) (b ⊓ u) i (by
      change min (a i) (u i) = min (b i) (u i)
      rw [min_eq_right hua, min_eq_right (hua.trans (hab i))])]
    exact hF.increasing a b hab
end IsClassical
end ProbabilityTheory.Copula
