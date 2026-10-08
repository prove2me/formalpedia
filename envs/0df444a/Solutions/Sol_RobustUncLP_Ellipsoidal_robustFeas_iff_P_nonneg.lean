-- Prove2me | solution 1 for RobustUncLP.Ellipsoidal.robustFeas_iff_P_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:46:09.782601+00:00
-- url     : https://prove2.me/submissions/0b1ad134-2a9e-4565-9d83-02af617e42cf

import Mathlib
import Definitions.Def_RobustUncLP_Ellipsoidal_Setting
import Definitions.Def_RobustUncLP_Ellipsoidal_SystemC

open RobustUncLP.Ellipsoidal Matrix RobustUncLP.Ellipsoidal.EllipsoidalData in
theorem solution {m n k : ℕ} (D : EllipsoidalData m n k) (f : Fin n → ℝ)
    (x : Fin n → ℝ) (hfx : f ⬝ᵥ x = 1) :
    x ∈ RobustUncLP.WorstCase.robustFeas D.uncSet f ↔ ∀ i : Fin m, ∀ u ∈ PFeas D, 0 ≤ (D.Pi 0 (u 0) *ᵥ x) i := by
  constructor
  · intro hx i u hu
    have hA : D.Pi 0 (u 0) ∈ D.uncSet := by
      simp only [EllipsoidalData.uncSet, Set.mem_iInter]
      intro ℓ
      exact ⟨u ℓ, (hu.1 ℓ).symm, hu.2 ℓ⟩
    exact hx.1 _ hA i
  · intro h
    refine ⟨?_, hfx⟩
    intro A hA
    simp only [EllipsoidalData.uncSet, Set.mem_iInter] at hA
    choose u hu1 hu2 using fun ℓ => hA ℓ
    have hu : u ∈ PFeas D := ⟨fun ℓ => by rw [← hu1 ℓ, ← hu1 0], hu2⟩
    intro i
    have := h i u hu
    rw [← hu1 0] at this
    exact this
