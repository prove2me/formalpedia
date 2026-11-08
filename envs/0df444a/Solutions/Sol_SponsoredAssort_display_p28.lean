-- Prove2me | solution 1 for SponsoredAssort.display_p28
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:07:48.400654+00:00
-- url     : https://prove2.me/submissions/e335ca1c-3f6c-4342-a2f9-bd53c2d17dbc

import Mathlib
import Definitions.Def_SponsoredAssort_worstCaseRatio
import Definitions.Def_SponsoredAssort_IsBestSelector
import Definitions.Def_SponsoredAssort_partitionMech
import Definitions.Def_SponsoredAssort_singletons

open scoped NNReal ENNReal

namespace Aux_SAp28

open SponsoredAssort MeasureTheory

theorem welfare_le {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (T : Finset (Fin n))
    (v : Attr n) : welfare r T v ≤ ∑ i ∈ T, r i * ((v i : ℝ) / (1 + (v i : ℝ))) := by
  unfold welfare
  apply Finset.sum_le_sum
  intro i hi
  unfold choiceProb
  rw [if_pos hi]
  apply mul_le_mul_of_nonneg_left _ (hr i).le
  have h0 : (0 : ℝ) ≤ v i := (v i).2
  have hle : (v i : ℝ) ≤ ∑ j ∈ T, (v j : ℝ) :=
    Finset.single_le_sum (f := fun j => (v j : ℝ)) (fun j _ => (v j).2) hi
  apply div_le_div_of_nonneg_left h0 (by linarith) (by linarith)

theorem welfare_nonneg {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (T : Finset (Fin n))
    (v : Attr n) : 0 ≤ welfare r T v := by
  unfold welfare
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (hr i).le
  unfold choiceProb
  by_cases hi : i ∈ T
  · rw [if_pos hi]
    apply div_nonneg (v i).2
    have : (0 : ℝ) ≤ ∑ j ∈ T, (v j : ℝ) := Finset.sum_nonneg (fun j _ => (v j).2)
    linarith
  · rw [if_neg hi]

theorem welfare_single {n : ℕ} (r : Fin n → ℝ) (i : Fin n) (v : Attr n) :
    welfare r {i} v = r i * ((v i : ℝ) / (1 + (v i : ℝ))) := by
  unfold welfare choiceProb
  simp

theorem part_eq {n : ℕ} (i : Fin n) : (singletons n).part i = {i} := by
  classical
  ext b
  simp only [Finset.mem_singleton]
  unfold singletons nested
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  change (i = b ∨ ((i : ℕ) < 1 ∧ (b : ℕ) < 1)) ↔ b = i
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact h.symm
    · exact Fin.ext (by omega)
  · rintro rfl; exact Or.inl rfl

end Aux_SAp28

open SponsoredAssort MeasureTheory in
theorem solution {n : ℕ} [NeZero n] (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (S : Attr n → Finset (Fin n)) (hS : IsBestSelector r (singletons n) S) :
    1 / (n : ℝ≥0∞) ≤ worstCaseRatio r (partitionMech r (singletons n) S) := by
  -- pointwise bounds
  have hsingle : ∀ v i, r i * ((v i : ℝ) / (1 + (v i : ℝ))) ≤ welfare r (S v) v := by
    intro v i
    rw [← Aux_SAp28.welfare_single, ← Aux_SAp28.part_eq]
    exact (hS v).2 _ (((singletons n).part_mem).mpr (Finset.mem_univ i))
  have hfb : ∀ v, firstBest r v ≤ (n : ℝ) * welfare r (S v) v := by
    intro v
    unfold firstBest
    apply Finset.sup'_le
    intro T _
    calc welfare r T v ≤ ∑ i ∈ T, r i * ((v i : ℝ) / (1 + (v i : ℝ))) :=
          Aux_SAp28.welfare_le r hr T v
      _ ≤ ∑ i : Fin n, r i * ((v i : ℝ) / (1 + (v i : ℝ))) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
          intro i _ _
          apply mul_nonneg (hr i).le
          apply div_nonneg (v i).2
          have : (0 : ℝ) ≤ v i := (v i).2
          linarith
      _ ≤ ∑ _i : Fin n, welfare r (S v) v := Finset.sum_le_sum (fun i _ => hsingle v i)
      _ = (n : ℝ) * welfare r (S v) v := by simp
  have hfbM : ∀ v, firstBest r v ≤ ∑ i : Fin n, r i := by
    intro v
    unfold firstBest
    apply Finset.sup'_le
    intro T _
    calc welfare r T v ≤ ∑ i ∈ T, r i * ((v i : ℝ) / (1 + (v i : ℝ))) :=
          Aux_SAp28.welfare_le r hr T v
      _ ≤ ∑ i ∈ T, r i := by
          apply Finset.sum_le_sum
          intro i _
          have h0 : (0 : ℝ) ≤ v i := (v i).2
          have : (v i : ℝ) / (1 + (v i : ℝ)) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
          nlinarith [hr i]
      _ ≤ ∑ i : Fin n, r i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
            (fun i _ _ => (hr i).le)
  unfold worstCaseRatio
  refine le_iInf (fun F => le_iInf (fun hF => le_iInf (fun hB => ?_)))
  have hBtop : expFirstBest r F ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑ i : Fin n, r i))
    unfold expFirstBest
    calc ∫⁻ v, ENNReal.ofReal (firstBest r v) ∂F
        ≤ ∫⁻ _v, ENNReal.ofReal (∑ i : Fin n, r i) ∂F :=
          lintegral_mono (fun v => ENNReal.ofReal_le_ofReal (hfbM v))
      _ = ENNReal.ofReal (∑ i : Fin n, r i) := by simp
  have hBle : expFirstBest r F ≤ (n : ℝ≥0∞) * expWelfare r (partitionMech r (singletons n) S) F := by
    unfold expFirstBest expWelfare
    rw [← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n)]
    apply lintegral_mono
    intro v
    have h1 := ENNReal.ofReal_le_ofReal (hfb v)
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast] at h1
    exact h1
  rw [ENNReal.le_div_iff_mul_le (Or.inl hB) (Or.inl hBtop)]
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    have := NeZero.ne n
    exact_mod_cast this
  calc 1 / (n : ℝ≥0∞) * expFirstBest r F
      ≤ 1 / (n : ℝ≥0∞) * ((n : ℝ≥0∞) * expWelfare r (partitionMech r (singletons n) S) F) :=
        by gcongr
    _ = expWelfare r (partitionMech r (singletons n) S) F := by
        rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel hn0 (ENNReal.natCast_ne_top n), one_mul]
