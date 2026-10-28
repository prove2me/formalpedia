-- Prove2me | solution 1 for StatComplexityDM.MAB.ber_family_subset_localized
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:28:54.665505+00:00
-- url     : https://prove2.me/submissions/49b54fa8-9b83-4863-a1e2-44b4582a1494

import Mathlib
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_StatComplexityDM_MAB_Bernoulli

open FoundationsRL.GeneralDM

namespace Aux_berloc
open StatComplexityDM.MAB

lemma fM_ber (A : ℕ) (m : Fin A → Bool → ℝ) (q : ℝ) (π : Fin A) (h : m π = ber q) :
    fM berRew m π = q := by
  unfold fM
  rw [h]
  simp [Fintype.sum_bool, ber, berRew]

end Aux_berloc

open StatComplexityDM.MAB in
theorem solution (A : ℕ) (hA : 2 ≤ A)
    (piStar : (Fin A → Bool → ℝ) → Fin A)
    (hpiStar : StatComplexityDM.LowerBound.IsArgmaxSel berRew piStar) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 2) :
    Set.range (berFamily A Δ) ⊆
      StatComplexityDM.LowerBound.linfLocalized (bernoulliBandits A) berRew piStar (fun _ => ber (1 / 2)) Δ := by
  rintro _ ⟨i, rfl⟩
  have hval : ∀ π, fM berRew (berFamily A Δ i) π = 1 / 2 + Δ * (if π = i then 1 else 0) :=
    fun π => Aux_berloc.fM_ber A _ _ π rfl
  have hbar : ∀ π, fM berRew (fun _ => ber (1 / 2)) π = 1 / 2 :=
    fun π => Aux_berloc.fM_ber A _ _ π rfl
  refine ⟨?_, ?_⟩
  · intro π
    refine ⟨?_, ?_⟩
    · intro y
      unfold berFamily ber
      split_ifs <;> linarith
    · unfold berFamily ber
      simp [Fintype.sum_bool]
  · intro π
    have hs := hpiStar (berFamily A Δ i) i
    rw [hval, hval] at hs
    have hup := hval (piStar (berFamily A Δ i))
    rw [hval, hval, hbar, hbar]
    simp only [if_pos rfl] at hs
    split_ifs at hs ⊢ <;> rw [abs_le] <;> constructor <;> linarith
