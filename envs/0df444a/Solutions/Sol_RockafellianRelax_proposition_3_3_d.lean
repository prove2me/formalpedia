-- Prove2me | solution 1 for RockafellianRelax.proposition_3_3_d
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-04T12:28:42.766645+00:00
-- url     : https://prove2.me/submissions/52734d61-311b-4219-b0de-2881dab90419

import Definitions.Def_RockafellianRelax_IsStrictlyExact
import Definitions.Def_RockafellianRelax_argmin
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

theorem solution {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (φ : (Fin n → ℝ) → EReal) (hf : IsRockafellian f φ) (ybar : Fin m → ℝ)
    (hne : (argmin (tilt f ybar)).Nonempty)
    (hsec : ∀ u ∈ AubinLipschitz.effDom (minValue f),
      (argmin (fun x : Fin n → ℝ => f (u, x))).Nonempty)
    (h34 : ∀ (us : Fin m → ℝ) (xs : Fin n → ℝ), (us, xs) ∈ argmin (tilt f ybar) →
      us = 0 ∧ xs ∈ argmin φ) :
    IsStrictlyExact f φ ybar := by
  obtain ⟨⟨u0, x0⟩, hz0⟩ := hne
  obtain ⟨hu0, hx0⟩ := h34 u0 x0 hz0
  subst u0
  have hx0' := (argmin_iff_pointwise φ x0).mp hx0
  have hz0' := (argmin_iff_pointwise (tilt f ybar) (0, x0)).mp hz0
  have heq0 : minValue f 0 = φ x0 := by
    apply le_antisymm
    · exact (iInf_le (fun x => f (0, x)) x0).trans_eq (hf x0)
    · exact le_iInf fun x => by simpa [hf x] using hx0'.2 x
  have hdom0 : minValue f 0 ≠ ⊤ := by simpa only [heq0] using hx0'.1
  have hbound : ∀ u, minValue f 0 + ((ybar ⬝ᵥ u : ℝ) : EReal) ≤ minValue f u := by
    intro u
    apply le_iInf
    intro x
    apply EReal.add_le_of_le_sub
    simpa [tilt, hf x0, ← heq0] using hz0'.2 (u, x)
  refine ⟨hf, ?_⟩
  intro u hu
  by_contra hnlt
  have heq : minValue f u = minValue f 0 + ((ybar ⬝ᵥ u : ℝ) : EReal) :=
    le_antisymm (not_lt.mp hnlt) (hbound u)
  have hdomu : u ∈ AubinLipschitz.effDom (minValue f) := by
    change minValue f u ≠ ⊤
    rw [heq]
    exact EReal.add_ne_top hdom0 (EReal.coe_ne_top _)
  obtain ⟨x, hx⟩ := hsec u hdomu
  have hx' := (argmin_iff_pointwise (fun x => f (u, x)) x).mp hx
  have heqx : f (u, x) = minValue f u :=
    le_antisymm (le_iInf hx'.2) (iInf_le _ x)
  have htilt : tilt f ybar (u, x) = minValue f 0 := by
    rw [tilt, heqx, heq, EReal.add_sub_cancel_right]
  have harg : (u, x) ∈ argmin (tilt f ybar) := by
    apply (argmin_iff_pointwise _ _).mpr
    refine ⟨by simpa only [htilt] using hdom0, ?_⟩
    intro z
    rw [htilt]
    apply (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).mpr
    exact (hbound z.1).trans (iInf_le _ z.2)
  exact hu (h34 u x harg).1

#print axioms solution
