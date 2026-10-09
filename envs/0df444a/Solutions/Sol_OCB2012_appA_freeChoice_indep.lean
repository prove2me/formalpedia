-- Prove2me | solution 1 for OCB2012.appA_freeChoice_indep
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T10:08:57.613242+00:00
-- url     : https://prove2.me/submissions/b4e2f554-0fcb-448f-bcb3-b5b4996387f2

import Mathlib
import Definitions.Def_OCB2012_appA

namespace OCB2012Sol
open OCB2012

/-- A sum over the three causal relations. -/
lemma sum_causalRel (f : CausalRel → ℝ) :
    ∑ R, f R = f CausalRel.AB + f CausalRel.BA + f CausalRel.incomparable := by
  show ∑ R ∈ ({CausalRel.AB, CausalRel.BA, CausalRel.incomparable} : Finset CausalRel), f R = _
  simp [Finset.sum_insert, add_assoc]

/-- `p(E)` is the sum of the contributions of the three values of `R`. -/
lemma pr_three (P : EventDist) (E : Bool → Bool → Bool → Bool → Bool → CausalRel → Bool) :
    P.pr E =
      (∑ a, ∑ b, ∑ b', ∑ x, ∑ y,
          if E a b b' x y CausalRel.AB then P a b b' x y CausalRel.AB else 0) +
      (∑ a, ∑ b, ∑ b', ∑ x, ∑ y,
          if E a b b' x y CausalRel.BA then P a b b' x y CausalRel.BA else 0) +
      (∑ a, ∑ b, ∑ b', ∑ x, ∑ y, if E a b b' x y CausalRel.incomparable then
          P a b b' x y CausalRel.incomparable else 0) := by
  simp only [EventDist.pr, sum_causalRel, Finset.sum_add_distrib]

/-- Independence of a variable from `R = r₁` and from `R ∈ {r₁, r₃}` gives independence from
`R = r₂` and `R = r₃`, when the three values of `R` exhaust the probability mass. -/
lemma indep_of_two {f₁ f₂ f₃ q₁ q₂ q₃ : ℝ} (hq : q₁ + q₂ + q₃ = 1)
    (h₁ : f₁ = (f₁ + f₂ + f₃) * q₁) (h₁₃ : f₁ + f₃ = (f₁ + f₂ + f₃) * (q₁ + q₃)) :
    f₂ = (f₁ + f₂ + f₃) * q₂ ∧ f₃ = (f₁ + f₂ + f₃) * q₃ :=
  ⟨by linear_combination -h₁₃ - (f₁ + f₂ + f₃) * hq, by linear_combination h₁₃ - h₁⟩

/-- `indep_of_two` with the roles of the first two values of `R` exchanged in the sums. -/
lemma indep_of_two' {f₁ f₂ f₃ q₁ q₂ q₃ : ℝ} (hq : q₂ + q₁ + q₃ = 1)
    (h₁ : f₁ = (f₂ + f₁ + f₃) * q₁) (h₁₃ : f₁ + f₃ = (f₂ + f₁ + f₃) * (q₁ + q₃)) :
    f₂ = (f₂ + f₁ + f₃) * q₂ ∧ f₃ = (f₂ + f₁ + f₃) * q₃ :=
  ⟨by linear_combination -h₁₃ - (f₂ + f₁ + f₃) * hq, by linear_combination h₁₃ - h₁⟩

end OCB2012Sol

open OCB2012 OCB2012Sol EventDist in
theorem solution (P : EventDist) (hP : P.IsProb)
    (hb' : ∀ v,
      P.pr (fun _ _ b' _ _ R => decide (b' = v ∧ R = CausalRel.AB)) =
          P.pr (fun _ _ b' _ _ _ => decide (b' = v)) *
            P.pr (fun _ _ _ _ _ R => decide (R = CausalRel.AB)) ∧
      P.pr (fun _ _ b' _ _ R => decide (b' = v ∧ R ≠ CausalRel.BA)) =
          P.pr (fun _ _ b' _ _ _ => decide (b' = v)) *
            P.pr (fun _ _ _ _ _ R => decide (R ≠ CausalRel.BA)))
    (hb : ∀ v,
      P.pr (fun _ b _ _ _ R => decide (b = v ∧ R = CausalRel.AB)) =
          P.pr (fun _ b _ _ _ _ => decide (b = v)) *
            P.pr (fun _ _ _ _ _ R => decide (R = CausalRel.AB)) ∧
      P.pr (fun _ b _ _ _ R => decide (b = v ∧ R ≠ CausalRel.BA)) =
          P.pr (fun _ b _ _ _ _ => decide (b = v)) *
            P.pr (fun _ _ _ _ _ R => decide (R ≠ CausalRel.BA)))
    (ha : ∀ v,
      P.pr (fun a _ _ _ _ R => decide (a = v ∧ R = CausalRel.BA)) =
          P.pr (fun a _ _ _ _ _ => decide (a = v)) *
            P.pr (fun _ _ _ _ _ R => decide (R = CausalRel.BA)) ∧
      P.pr (fun a _ _ _ _ R => decide (a = v ∧ R ≠ CausalRel.AB)) =
          P.pr (fun a _ _ _ _ _ => decide (a = v)) *
            P.pr (fun _ _ _ _ _ R => decide (R ≠ CausalRel.AB))) :
    ∀ v R₀,
      P.pr (fun _ _ b' _ _ R => decide (b' = v ∧ R = R₀)) =
          P.pr (fun _ _ b' _ _ _ => decide (b' = v)) * P.pr (fun _ _ _ _ _ R => decide (R = R₀)) ∧
      P.pr (fun _ b _ _ _ R => decide (b = v ∧ R = R₀)) =
          P.pr (fun _ b _ _ _ _ => decide (b = v)) * P.pr (fun _ _ _ _ _ R => decide (R = R₀)) ∧
      P.pr (fun a _ _ _ _ R => decide (a = v ∧ R = R₀)) =
          P.pr (fun a _ _ _ _ _ => decide (a = v)) * P.pr (fun _ _ _ _ _ R => decide (R = R₀)) := by
  intro v R₀
  have hsum := hP.2
  obtain ⟨hb'1, hb'2⟩ := hb' v
  obtain ⟨hb1, hb2⟩ := hb v
  obtain ⟨ha1, ha2⟩ := ha v
  simp only [sum_causalRel, Finset.sum_add_distrib] at hsum
  simp only [pr_three] at hb'1 hb'2 hb1 hb2 ha1 ha2 ⊢
  simp only [decide_eq_true_eq, and_true, and_false, if_false, ne_eq, not_true_eq_false,
    reduceCtorEq, not_false_eq_true, if_true, Finset.sum_const_zero, add_zero, zero_add]
    at hb'1 hb'2 hb1 hb2 ha1 ha2 ⊢
  cases R₀ <;>
    simp only [and_true, and_false, if_false, reduceCtorEq, if_true, Finset.sum_const_zero,
      add_zero, zero_add]
  · exact ⟨hb'1, hb1, (indep_of_two' hsum ha1 ha2).1⟩
  · exact ⟨(indep_of_two hsum hb'1 hb'2).1, (indep_of_two hsum hb1 hb2).1, ha1⟩
  · exact ⟨(indep_of_two hsum hb'1 hb'2).2, (indep_of_two hsum hb1 hb2).2,
      (indep_of_two' hsum ha1 ha2).2⟩
