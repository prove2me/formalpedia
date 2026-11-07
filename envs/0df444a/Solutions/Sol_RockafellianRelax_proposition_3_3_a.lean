-- Prove2me | solution 1 for RockafellianRelax.proposition_3_3_a
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-06T12:12:10.242655+00:00
-- url     : https://prove2.me/submissions/0db9c57b-7f5b-418b-9467-67ec984ee3af

import Definitions.Def_RockafellianRelax_IsExact
import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_RockafellianRelax_tilt

open RockafellianRelax

private lemma n06_argmin_iff {α : Type*} (g : α → EReal) (a : α) :
    a ∈ argmin g ↔ g a ≠ ⊤ ∧ ∀ b, g a ≤ g b := by
  constructor
  · intro h
    refine ⟨h.1, fun b => ?_⟩
    have hle : g a ≤ ⨅ b, g b := by simpa using h.2
    exact hle.trans (iInf_le g b)
  · rintro ⟨hdom, hmin⟩
    exact ⟨hdom, by simpa using (le_iInf hmin)⟩

theorem solution {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (φ : (Fin n → ℝ) → EReal) (ybar : Fin m → ℝ) (hex : IsExact f φ ybar) :
    ∀ xs : Fin n → ℝ, xs ∈ argmin φ → ((0 : Fin m → ℝ), xs) ∈ argmin (tilt f ybar) := by
  intro xs hxs
  obtain ⟨hdom, hmin⟩ := (n06_argmin_iff φ xs).mp hxs
  have hvalue : minValue f 0 = φ xs := by
    apply le_antisymm
    · exact (iInf_le (fun x => f (0,x)) xs).trans_eq (hex.1 xs)
    · exact le_iInf fun x => by simpa only [hex.1 x] using hmin x
  apply (n06_argmin_iff _ _).mpr
  refine ⟨by simpa [tilt, hex.1 xs] using hdom, ?_⟩
  rintro ⟨u,x⟩
  have hb : minValue f 0 + ((ybar ⬝ᵥ u : ℝ) : EReal) ≤ f (u,x) :=
    (hex.2 u).trans (iInf_le _ x)
  have hs := (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mpr hb
  simpa [tilt, hex.1 xs, hvalue] using hs

#print axioms solution
