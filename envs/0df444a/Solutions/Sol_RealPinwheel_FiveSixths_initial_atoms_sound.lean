-- Prove2me | solution 1 for RealPinwheel.FiveSixths.initial_atoms_sound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:48:10.540807+00:00
-- url     : https://prove2.me/submissions/9deab78a-614e-47e3-aeeb-e2ed841ab636

import Definitions.Def_RealPinwheel_FiveSixths_LinearCertificate
open RealPinwheel.FiveSixths
theorem solution {n k : ℕ} (d : Fin n → ℝ)
    (hpos : ∀ i, 0 < d i) (hord : Antitone d)
    (hsum : (∑ i, if i.val < k then d i else 0) ≤ (5 : ℝ) / 6) :
    ∀ a ∈ initialAtoms n k, a.Holds d := by
  intro a ha
  simp only [initialAtoms, List.mem_append, List.mem_map, List.mem_finRange,
    true_and, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with (⟨i, rfl⟩ | ⟨i, rfl⟩) | rfl
  · have he : (positiveAtom i).eval d = -d i := by simp [LinearAtom.eval, positiveAtom]
    simp only [LinearAtom.Holds, positiveAtom, ↓reduceIte]
    change (positiveAtom i).eval d < 0
    rw [he]
    exact neg_neg_of_pos (hpos i)
  · have he : (orderAtom (⟨i.val, by omega⟩ : Fin n) ⟨i.val + 1, by omega⟩).eval d =
        d ⟨i.val + 1, by omega⟩ - d ⟨i.val, by omega⟩ := by
      simp [LinearAtom.eval, orderAtom, sub_mul, Finset.sum_sub_distrib]
    simp only [LinearAtom.Holds, orderAtom, Bool.false_eq_true, ↓reduceIte]
    change (orderAtom _ _).eval d ≤ 0
    rw [he]
    exact sub_nonpos.mpr (hord (by change i.val ≤ i.val + 1; omega))
  · have he : (densityAtom n k).eval d =
        6 * (∑ i, if i.val < k then d i else 0) - 5 := by
      simp [LinearAtom.eval, densityAtom, Finset.mul_sum, mul_ite, ite_mul] <;> ring
    simp only [LinearAtom.Holds, densityAtom, Bool.false_eq_true, ↓reduceIte]
    change (densityAtom n k).eval d ≤ 0
    rw [he]
    linarith

