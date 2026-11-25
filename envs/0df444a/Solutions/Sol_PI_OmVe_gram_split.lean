-- Prove2me | solution 1 for PI.OmVe.gram_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:06:45.610037+00:00
-- url     : https://prove2.me/submissions/2e3b9cae-564d-4017-be1d-1f6bfa8fe2c7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_SingleMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_CardAndAdd
import Theorems.Thm_PI_OmVe_ffH_herm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.OmVe
open PI.VolStabSW Matrix
section gen
variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
private theorem eq_or_exists_succAbove {n : ℕ} (p i : Fin (n + 1)) :
    i = p ∨ ∃ j, i = p.succAbove j := by
  by_cases h : i = p
  · exact Or.inl h
  · right
    exact (Fin.eq_self_or_eq_succAbove p i).resolve_left h
end gen
end PI.OmVe
end
end

set_option autoImplicit false
noncomputable section
open PI PI.OmVe
open PI.VolStabSW Matrix
variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
namespace PI.OmVe
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {a' : ℕ}
    (T : Matrix (Fin (a' + 1)) (Fin (a' + 1)) K) (i₀ : Fin (a' + 1)) (hr : ∀ j, T i₀ j = 0)
    (hc : ∀ j, T j i₀ = 0) (t : K) (X : Fin (a' + 1) → Fin M → K) :
    ffGram σ J X = T + Matrix.single i₀ i₀ t ↔
      ffGram σ J (fun j => X (i₀.succAbove j)) = T.submatrix i₀.succAbove i₀.succAbove ∧
        (∀ j, ffH σ J (X (i₀.succAbove j)) (X i₀) = 0) ∧ ffH σ J (X i₀) (X i₀) = t := by
  constructor
  · intro h
    have hh : ∀ i j, PI.VolStabSW.ffH σ J (X i) (X j) = T i j + Matrix.single i₀ i₀ t i j :=
      fun i j => congrFun (congrFun h i) j
    refine ⟨?_, fun j => ?_, ?_⟩
    · ext j k
      show PI.VolStabSW.ffH σ J (X (i₀.succAbove j)) (X (i₀.succAbove k)) =
        T (i₀.succAbove j) (i₀.succAbove k)
      have hne : i₀.succAbove j ≠ i₀ := Fin.succAbove_ne i₀ j
      rw [hh]
      simp [hne.symm]
    · have hne : i₀.succAbove j ≠ i₀ := Fin.succAbove_ne i₀ j
      rw [hh, hc]
      simp [hne.symm]
    · rw [hh, hr]
      simp
  · rintro ⟨h1, h2, h3⟩
    ext i j
    show PI.VolStabSW.ffH σ J (X i) (X j) = T i j + Matrix.single i₀ i₀ t i j
    rcases eq_or_exists_succAbove i₀ i with hi | ⟨i', hi⟩ <;>
      rcases eq_or_exists_succAbove i₀ j with hj | ⟨j', hj⟩ <;> rw [hi, hj]
    · rw [h3, hr]
      simp
    · have hne : i₀.succAbove j' ≠ i₀ := Fin.succAbove_ne i₀ j'
      rw [ffH_herm σ J hσ hJ (X (i₀.succAbove j')) (X i₀), h2 j', map_zero, hr]
      simp [hne.symm]
    · have hne : i₀.succAbove i' ≠ i₀ := Fin.succAbove_ne i₀ i'
      rw [h2 i', hc]
      simp [hne.symm]
    · have hne : i₀.succAbove i' ≠ i₀ := Fin.succAbove_ne i₀ i'
      rw [show PI.VolStabSW.ffH σ J (X (i₀.succAbove i')) (X (i₀.succAbove j')) =
          T (i₀.succAbove i') (i₀.succAbove j') from congrFun (congrFun h1 i') j']
      simp [hne.symm]
end PI.OmVe
