-- Prove2me | solution 1 for SeqRankAgg.Optimality.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:23:47.501985+00:00
-- url     : https://prove2.me/submissions/2f9c38c5-9a7e-4dbc-8f60-f57470ae6afe

import Mathlib
import Definitions.Def_SeqRankAgg_Optimality_Model

open SeqRankAgg.Optimality
open MeasureTheory Filter
open scoped ENNReal

theorem solution {m : ℕ} (hm : 1 ≤ m) (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞)
    (hA1 : A1 ρ) (hA2 : A2 ρ) (hA3 : A3 M ρ)
    (hA4 : A4 M ρ) (hA5 : A5 ρ)
    (θ : Fin m → ℝ) (hθ : θ ∈ W ρ) (t : ℕ) (ht : 1 ≤ t)
    (wgt : Fin t → Fin (numPairs m) → ℝ)
    (hwgt : ∀ n, wgt n ∈ simplex (numPairs m))
    (θstar : Fin m → ℝ) (hstar : θstar ∈ W ρ ∧ ¬ SameRank θstar θ)
    (hmin : ∀ θ' ∈ {θ' ∈ W ρ | ¬ SameRank θ' θ},
      (∑ n : Fin t, ∑ a : Fin (numPairs m),
        wgt n a * Dij M (pairOf m a) θ θstar) ≤
      (∑ n : Fin t, ∑ a : Fin (numPairs m),
        wgt n a * Dij M (pairOf m a) θ θ')) :
    (∑ n : Fin t, ∑ a : Fin (numPairs m),
      wgt n a * Dij M (pairOf m a) θ θstar) ≤ (t : ℝ) * Dfun M ρ θ := by
  have htr : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  set D : (Fin m → ℝ) → Fin (numPairs m) → ℝ := fun θ' a => Dij M (pairOf m a) θ θ' with hD
  obtain ⟨wb, hwb⟩ : ∃ wb : Fin (numPairs m) → ℝ, wb = fun a => (t : ℝ)⁻¹ * ∑ n, wgt n a := ⟨_, rfl⟩
  have hS : ∀ θ', (∑ n : Fin t, ∑ a : Fin (numPairs m), wgt n a * Dij M (pairOf m a) θ θ')
      = (t : ℝ) * ∑ a, wb a * Dij M (pairOf m a) θ θ' := by
    intro θ'
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hwb, ← Finset.sum_mul]
    field_simp
  have hwbS : wb ∈ simplex (numPairs m) := by
    refine ⟨fun a => ?_, ?_⟩
    · rw [hwb]; exact mul_nonneg (inv_nonneg.mpr htr.le) (Finset.sum_nonneg (fun n _ => (hwgt n).1 a))
    · rw [hwb, ← Finset.mul_sum, Finset.sum_comm]
      simp only [(hwgt _).2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
      field_simp
  have : Nonempty (Alt ρ θ) := ⟨⟨θstar, hstar⟩⟩
  have h1 : ∑ a, wb a * Dij M (pairOf m a) θ θstar ≤ innerMin M ρ θ wb := by
    apply le_ciInf
    intro θ'
    have := hmin θ'.1 θ'.2
    rw [hS, hS] at this
    exact le_of_mul_le_mul_left this htr
  have hbdd : BddAbove (Set.range (fun w : simplex (numPairs m) => innerMin M ρ θ w.1)) := by
    refine ⟨max 0 (∑ a, |Dij M (pairOf m a) θ θstar|), ?_⟩
    rintro _ ⟨w, rfl⟩
    by_cases hb : BddBelow (Set.range (fun θ' : Alt ρ θ =>
        ∑ a : Fin (numPairs m), w.1 a * Dij M (pairOf m a) θ θ'.1))
    · have := ciInf_le hb ⟨θstar, hstar⟩
      refine le_trans this (le_trans ?_ (le_max_right _ _))
      refine Finset.sum_le_sum (fun a _ => ?_)
      have hw0 := w.2.1 a
      have hw1 : w.1 a ≤ 1 := by
        rw [← w.2.2]
        exact Finset.single_le_sum (fun b _ => w.2.1 b) (Finset.mem_univ a)
      calc w.1 a * Dij M (pairOf m a) θ θstar ≤ |w.1 a * Dij M (pairOf m a) θ θstar| := le_abs_self _
        _ = w.1 a * |Dij M (pairOf m a) θ θstar| := by rw [abs_mul, abs_of_nonneg hw0]
        _ ≤ 1 * |Dij M (pairOf m a) θ θstar| := mul_le_mul_of_nonneg_right hw1 (abs_nonneg _)
        _ = _ := one_mul _
    · unfold innerMin
      beta_reduce
      rw [Real.iInf_of_not_bddBelow hb]
      exact le_max_left _ _
  have h2 : innerMin M ρ θ wb ≤ Dfun M ρ θ :=
    le_ciSup (f := fun w : simplex (numPairs m) => innerMin M ρ θ w.1) hbdd ⟨wb, hwbS⟩
  rw [hS]
  exact mul_le_mul_of_nonneg_left (h1.trans h2) htr.le
