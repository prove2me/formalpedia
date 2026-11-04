-- Prove2me | solution 1 for RockafellianRelax.proposition_3_3_c
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-03T12:32:03.894673+00:00
-- url     : https://prove2.me/submissions/f06d0342-a876-46fa-a21d-1ec1ec8adc31

import Definitions.Def_RockafellianRelax_IsStrictlyExact
import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_RockafellianRelax_tilt

open RockafellianRelax

private lemma argmin_le {α : Type*} (ψ : α → EReal) {x : α}
    (hx : x ∈ argmin ψ) (z : α) : ψ x ≤ ψ z := by
  have h : ψ x ≤ (⨅ y, ψ y) + (0 : EReal) := hx.2
  rw [add_zero] at h
  exact h.trans (iInf_le ψ z)

theorem solution {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (φ : (Fin n → ℝ) → EReal) (ybar : Fin m → ℝ) (hsx : IsStrictlyExact f φ ybar) :
    ∀ (us : Fin m → ℝ) (xs : Fin n → ℝ), (us, xs) ∈ argmin (tilt f ybar) →
      us = 0 ∧ xs ∈ argmin φ := by
  intro us xs hmin
  have hle : tilt f ybar (us, xs) ≤ minValue f 0 := by
    apply le_iInf
    intro x
    simpa [tilt] using argmin_le (tilt f ybar) hmin (0, x)
  have hzero : us = 0 := by
    by_contra hne
    have hstrict := hsx.2 us hne
    have hpoint : minValue f us ≤ f (us, xs) := iInf_le _ xs
    have hback : f (us, xs) ≤ minValue f 0 + ((ybar ⬝ᵥ us : ℝ) : EReal) := by
      exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
        (Or.inl (EReal.coe_ne_top _))).mp hle
    exact (not_lt_of_ge (hpoint.trans hback)) hstrict
  refine ⟨hzero, ?_⟩
  subst us
  constructor
  · change φ xs ≠ ⊤
    have hdom : tilt f ybar (0, xs) ≠ ⊤ := hmin.1
    simpa [tilt, hsx.1 xs] using hdom
  · have hinf : φ xs ≤ ⨅ x, φ x := by
      apply le_iInf
      intro x
      simpa [tilt, hsx.1 xs, hsx.1 x] using argmin_le (tilt f ybar) hmin (0, x)
    simpa only [EReal.coe_zero, add_zero] using hinf

#print axioms solution

