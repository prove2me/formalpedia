-- Prove2me | solution 1 for PlatonicJEPA.platonic_representation_theorem
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T15:15:54.305439+00:00
-- url     : https://prove2.me/submissions/8aff33e0-1c0d-4bee-95d2-897e793c314d

import Mathlib
import Definitions.Def_PlatonicJEPA_Basic

open MeasureTheory Filter Topology
namespace PlatonicJEPA


theorem platonic_representation_theorem {Z : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}
    {ι : Type*} [Fintype ι] (hM : 2 ≤ Fintype.card ι) (X : ι → Type*)
    (p : Z → ℝ) (π : Z → Z → ℝ) (hπ : IsPairLaw p π)
    (ℓ : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (Ω : Measure (Fin k → ℝ) → EReal)
    (g : ∀ m, Z → X m) (hg : ∀ m, Function.Injective (g m))
    (huniq : ∀ h h' : Z → Fin k → ℝ,
      (∀ h'', worldLoss p π ℓ Ω h ≤ worldLoss p π ℓ Ω h'') →
      (∀ h'', worldLoss p π ℓ Ω h' ≤ worldLoss p π ℓ Ω h'') →
      ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, ∀ z, h' z = rot Q (h z)) :
    ∃ hstar : Z → Fin k → ℝ, ∀ m (f : X m → Fin k → ℝ),
      (∀ f' : X m → Fin k → ℝ, modalityLoss p π ℓ Ω (g m) f ≤ modalityLoss p π ℓ Ω (g m) f') →
      ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, ∀ z, f (g m z) = rot Q (hstar z) := by
  classical
  have key : ∀ m (f : X m → Fin k → ℝ),
      (∀ f' : X m → Fin k → ℝ, modalityLoss p π ℓ Ω (g m) f ≤ modalityLoss p π ℓ Ω (g m) f') →
      ∀ h'', worldLoss p π ℓ Ω (f ∘ g m) ≤ worldLoss p π ℓ Ω h'' := by
    intro m f hf h''
    have he : (Function.extend (g m) h'' 0) ∘ g m = h'' :=
      funext fun z => (hg m).extend_apply h'' 0 z
    calc worldLoss p π ℓ Ω (f ∘ g m) = modalityLoss p π ℓ Ω (g m) f := rfl
      _ ≤ modalityLoss p π ℓ Ω (g m) (Function.extend (g m) h'' 0) := hf _
      _ = worldLoss p π ℓ Ω ((Function.extend (g m) h'' 0) ∘ g m) := rfl
      _ = worldLoss p π ℓ Ω h'' := by rw [he]
  by_cases hex : ∃ h : Z → Fin k → ℝ, ∀ h'', worldLoss p π ℓ Ω h ≤ worldLoss p π ℓ Ω h''
  · obtain ⟨h0, hh0⟩ := hex
    refine ⟨h0, fun m f hf => ?_⟩
    obtain ⟨Q, hQ⟩ := huniq h0 (f ∘ g m) hh0 (key m f hf)
    exact ⟨Q, fun z => hQ z⟩
  · refine ⟨0, fun m f hf => ?_⟩
    exact absurd ⟨f ∘ g m, key m f hf⟩ hex


end PlatonicJEPA


open PlatonicJEPA MeasureTheory in
theorem solution {Z : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}
    {ι : Type*} [Fintype ι] (hM : 2 ≤ Fintype.card ι) (X : ι → Type*)
    (p : Z → ℝ) (π : Z → Z → ℝ) (hπ : IsPairLaw p π)
    (ℓ : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (Ω : Measure (Fin k → ℝ) → EReal)
    (g : ∀ m, Z → X m) (hg : ∀ m, Function.Injective (g m))
    (huniq : ∀ h h' : Z → Fin k → ℝ,
      (∀ h'', worldLoss p π ℓ Ω h ≤ worldLoss p π ℓ Ω h'') →
      (∀ h'', worldLoss p π ℓ Ω h' ≤ worldLoss p π ℓ Ω h'') →
      ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, ∀ z, h' z = rot Q (h z)) :
    ∃ hstar : Z → Fin k → ℝ, ∀ m (f : X m → Fin k → ℝ),
      (∀ f' : X m → Fin k → ℝ, modalityLoss p π ℓ Ω (g m) f ≤ modalityLoss p π ℓ Ω (g m) f') →
      ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, ∀ z, f (g m z) = rot Q (hstar z) :=
  PlatonicJEPA.platonic_representation_theorem hM X p π hπ ℓ Ω g hg huniq
