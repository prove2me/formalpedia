-- Prove2me | solution 1 for ValuativeSYZ.lemma_3_5_ctransform_involutive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T19:55:12.486469+00:00
-- url     : https://prove2.me/submissions/0a6b1460-1369-4c87-8110-d9f771191af7

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

/-! c0b0f986 ValuativeSYZ.lemma_3_5_ctransform_involutive: on P_c the c-transform is
involutive. Write φ = ψᶜ with ψ bounded by M'. Then φ is bounded (|φ| ≤ M + M'), so
χ := φᶜ is well defined and bounded below; χ ≤ ψ because ψᶜ(y) ≥ c y p - ψ p. Hence
φᶜᶜ(x) = sup_p (c x p - χ p) ≥ sup_p (c x p - ψ p) = φ x, while φᶜᶜ ≤ φ since
χ p ≥ c x p - φ x. No `Theorems.*` module is imported. -/

set_option autoImplicit false

open MeasureTheory ValuativeSYZ in
theorem solution {X B : Type*} [Nonempty X] [Nonempty B]
    (c : X → B → ℝ) (M : ℝ) (hc : ∀ x p, |c x p| ≤ M)
    (φ : X → ℝ) (hφ : φ ∈ Pc c) :
    ctransformDual c (ctransform c φ) = φ := by
  obtain ⟨ψ, ⟨M', hM'⟩, hφe⟩ := hφ
  have hbddψ : ∀ x, BddAbove (Set.range fun p => c x p - ψ p) := by
    intro x
    refine ⟨M + M', ?_⟩
    rintro _ ⟨p, rfl⟩
    have h1 := (abs_le.mp (hc x p)).2
    have h2 := (abs_le.mp (hM' p)).1
    show c x p - ψ p ≤ M + M'
    linarith
  have hφval : ∀ x, φ x = ⨆ p, (c x p - ψ p) := fun x => congrFun hφe x
  have hφge : ∀ x p, c x p - ψ p ≤ φ x := fun x p => by
    rw [hφval x]; exact le_ciSup (hbddψ x) p
  have hφle : ∀ x, φ x ≤ M + M' := fun x => by
    rw [hφval x]
    refine ciSup_le fun p => ?_
    have h1 := (abs_le.mp (hc x p)).2
    have h2 := (abs_le.mp (hM' p)).1
    linarith
  have hφlow : ∀ x, -M - M' ≤ φ x := fun x => by
    obtain ⟨p⟩ := ‹Nonempty B›
    have := hφge x p
    have h1 := (abs_le.mp (hc x p)).1
    have h2 := (abs_le.mp (hM' p)).2
    linarith
  have hbddφ : ∀ p, BddAbove (Set.range fun y => c y p - φ y) := by
    intro p
    refine ⟨M + (M + M'), ?_⟩
    rintro _ ⟨y, rfl⟩
    have h1 := (abs_le.mp (hc y p)).2
    have h2 := hφlow y
    show c y p - φ y ≤ M + (M + M')
    linarith
  have hχval : ∀ p, ctransform c φ p = ⨆ y, (c y p - φ y) := fun p => rfl
  have hχge : ∀ y p, c y p - φ y ≤ ctransform c φ p := fun y p => by
    rw [hχval p]; exact le_ciSup (hbddφ p) y
  have hχleψ : ∀ p, ctransform c φ p ≤ ψ p := fun p => by
    rw [hχval p]
    refine ciSup_le fun y => ?_
    have := hφge y p
    linarith
  have hχlow : ∀ p, -M - (M + M') ≤ ctransform c φ p := fun p => by
    obtain ⟨y⟩ := ‹Nonempty X›
    have := hχge y p
    have h1 := (abs_le.mp (hc y p)).1
    have h2 := hφle y
    linarith
  have hbddχ : ∀ x, BddAbove (Set.range fun q => c x q - ctransform c φ q) := by
    intro x
    refine ⟨M + (M + (M + M')), ?_⟩
    rintro _ ⟨q, rfl⟩
    have h1 := (abs_le.mp (hc x q)).2
    have h2 := hχlow q
    show c x q - ctransform c φ q ≤ M + (M + (M + M'))
    linarith
  funext x
  show ⨆ p, (c x p - ctransform c φ p) = φ x
  apply le_antisymm
  · refine ciSup_le fun p => ?_
    have := hχge x p
    linarith
  · rw [hφval x]
    refine ciSup_le fun p => ?_
    have h1 : c x p - ctransform c φ p ≤ ⨆ q, (c x q - ctransform c φ q) :=
      le_ciSup (hbddχ x) p
    have h2 := hχleψ p
    linarith
