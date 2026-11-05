-- Prove2me | solution 1 for RockafellianRelax.eq_A1_argmin_tilt_iff
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-04T12:22:38.028946+00:00
-- url     : https://prove2.me/submissions/42a5f680-5923-4373-a0ff-ab24d26da301

import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_RockafellianRelax_minValue
import Definitions.Def_RockafellianRelax_tilt

open RockafellianRelax

private lemma argmin_iff_pointwise {α : Type*} (g : α → EReal) (a : α) :
    a ∈ argmin g ↔ g a ≠ ⊤ ∧ ∀ b, g a ≤ g b := by
  constructor
  · intro h
    refine ⟨h.1, fun b => ?_⟩
    have hle : g a ≤ ⨅ b, g b := by simpa using h.2
    exact hle.trans (iInf_le g b)
  · rintro ⟨hdom, hmin⟩
    exact ⟨hdom, by simpa using (le_iInf hmin)⟩

private lemma sub_real_dom (a : EReal) (c : ℝ) : a - (c : EReal) ≠ ⊤ ↔ a ≠ ⊤ := by
  cases a <;> simp [← EReal.coe_sub]

private lemma sub_real_cancel_le (a b : EReal) (c : ℝ) :
    a - (c : EReal) ≤ b - (c : EReal) ↔ a ≤ b := by
  rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c))
    (Or.inl (EReal.coe_ne_top c)), EReal.sub_add_cancel]

private lemma inf_sub_real {α : Type*} (g : α → EReal) (c : ℝ) :
    (⨅ a, g a) - (c : EReal) = ⨅ a, g a - (c : EReal) := by
  apply le_antisymm
  · exact le_iInf fun a => EReal.sub_le_sub (iInf_le g a) le_rfl
  · apply (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).mpr
    apply le_iInf
    intro a
    exact EReal.add_le_of_le_sub (iInf_le (fun a => g a - (c : EReal)) a)

theorem solution {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (ybar : Fin m → ℝ) (us : Fin m → ℝ) (xs : Fin n → ℝ) :
    (us, xs) ∈ argmin (tilt f ybar) ↔
      us ∈ argmin (fun u : Fin m → ℝ => minValue f u - ((ybar ⬝ᵥ u : ℝ) : EReal)) ∧
        xs ∈ argmin (fun x : Fin n → ℝ => f (us, x)) := by
  rw [argmin_iff_pointwise, argmin_iff_pointwise, argmin_iff_pointwise]
  constructor
  · rintro ⟨hdom, hmin⟩
    have hrow : ∀ x, f (us, xs) ≤ f (us, x) := by
      intro x
      exact (sub_real_cancel_le _ _ _).mp (hmin (us, x))
    have heq : minValue f us = f (us, xs) :=
      le_antisymm (iInf_le _ xs) (le_iInf hrow)
    refine ⟨⟨?_, ?_⟩, ⟨?_, hrow⟩⟩
    · simpa [heq, tilt] using hdom
    · intro u
      rw [heq]
      rw [minValue, inf_sub_real]
      exact le_iInf fun x => by simpa [heq, tilt] using hmin (u, x)
    · exact (sub_real_dom _ _).mp hdom
  · rintro ⟨⟨hdom, houter⟩, ⟨hrowdom, hrow⟩⟩
    have heq : minValue f us = f (us, xs) :=
      le_antisymm (iInf_le _ xs) (le_iInf hrow)
    refine ⟨(sub_real_dom _ _).mpr hrowdom, ?_⟩
    rintro ⟨u, x⟩
    have houter' : f (us, xs) - ((ybar ⬝ᵥ us : ℝ) : EReal) ≤
        minValue f u - ((ybar ⬝ᵥ u : ℝ) : EReal) := by
      simpa only [heq] using houter u
    exact houter'.trans (EReal.sub_le_sub (iInf_le (fun x => f (u, x)) x) le_rfl)

#print axioms solution
