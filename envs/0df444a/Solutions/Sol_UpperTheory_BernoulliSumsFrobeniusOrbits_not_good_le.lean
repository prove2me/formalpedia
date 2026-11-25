-- Prove2me | solution 1 for UpperTheory.BernoulliSumsFrobeniusOrbits.not_good_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:27:17.903813+00:00
-- url     : https://prove2.me/submissions/4d37149d-49f8-466f-b45d-d30374fa3176

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_expectationSpec
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_TailLe
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_TilesLe
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_NotGoodLe
import Theorems.Thm_GlobalTheory_RandomTops_tiles_le
import Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_expectation_spec
import Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_tail_le
import Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_tiles_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
private theorem ngl_ind_pos {q : Prop} (h : q) : ind q = 1 := by
  unfold ind
  exact if_pos h
private theorem ngl_ind_nonneg (q : Prop) : 0 ≤ ind q := by
  unfold ind
  split_ifs <;> norm_num
private theorem ngl_ind_le {q : Prop} {x : ℝ} (h0 : 0 ≤ x) (h1 : q → 1 ≤ x) : ind q ≤ x := by
  unfold ind
  split_ifs with hq
  · exact h1 hq
  · exact h0
private theorem ngl_windows_le (p : ℕ → ℝ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (n i₀ L K K' : ℕ)
    (hK : K' ≤ K) (b : ℝ)
    (hb : ∀ A : Finset ℕ, A.card ≤ L → exP p A (fun T => ind (K' ≤ T.card)) ≤ b) :
    exP p ((Finset.range n).erase i₀)
      (fun U => ind (¬ ∀ i < n, (insert i₀ U ∩ window n i L).card ≤ K)) ≤ n * b := by
  obtain ⟨_, _, h_sum, h_mono, _, h_restr, _⟩ := expectation_spec p
  calc exP p ((Finset.range n).erase i₀)
        (fun U => ind (¬ ∀ i < n, (insert i₀ U ∩ window n i L).card ≤ K))
      ≤ exP p ((Finset.range n).erase i₀) (fun U => ∑ i ∈ Finset.range n,
          ind (K' ≤ (U ∩ (window n i L ∩ (Finset.range n).erase i₀)).card)) := by
        apply h_mono _ _ _ (fun a _ => hp a)
        intro U hU
        apply ngl_ind_le (Finset.sum_nonneg (fun i _ => ngl_ind_nonneg _))
        intro hq
        push_neg at hq
        obtain ⟨i, hi, hc⟩ := hq
        have hsub : U ∩ (window n i L ∩ (Finset.range n).erase i₀) = U ∩ window n i L := by
          ext x
          simp only [Finset.mem_inter]
          constructor
          · rintro ⟨h1, h2, _⟩
            exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨h1, h2, hU h1⟩
        have hle : (insert i₀ U ∩ window n i L).card ≤ (U ∩ window n i L).card + 1 := by
          calc (insert i₀ U ∩ window n i L).card ≤ (insert i₀ (U ∩ window n i L)).card := by
                apply Finset.card_le_card
                intro x hx
                simp only [Finset.mem_inter, Finset.mem_insert] at hx ⊢
                rcases hx with ⟨h1 | h1, h2⟩
                · exact Or.inl h1
                · exact Or.inr ⟨h1, h2⟩
            _ ≤ (U ∩ window n i L).card + 1 := Finset.card_insert_le _ _
        have hK'' : K' ≤ (U ∩ (window n i L ∩ (Finset.range n).erase i₀)).card := by
          rw [hsub]
          omega
        calc (1 : ℝ) = ind (K' ≤ (U ∩ (window n i L ∩ (Finset.range n).erase i₀)).card) :=
              (ngl_ind_pos hK'').symm
          _ ≤ ∑ j ∈ Finset.range n,
                ind (K' ≤ (U ∩ (window n j L ∩ (Finset.range n).erase i₀)).card) :=
              Finset.single_le_sum (f := fun j =>
                ind (K' ≤ (U ∩ (window n j L ∩ (Finset.range n).erase i₀)).card))
                (fun j _ => ngl_ind_nonneg _) (Finset.mem_range.2 hi)
    _ = ∑ i ∈ Finset.range n, exP p ((Finset.range n).erase i₀)
          (fun U => ind (K' ≤ (U ∩ (window n i L ∩ (Finset.range n).erase i₀)).card)) :=
        h_sum _ _ (fun i U => ind (K' ≤ (U ∩ (window n i L ∩ (Finset.range n).erase i₀)).card))
    _ = ∑ i ∈ Finset.range n, exP p (window n i L ∩ (Finset.range n).erase i₀)
          (fun T => ind (K' ≤ T.card)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h_restr _ _ (fun T => ind (K' ≤ T.card)) Finset.inter_subset_right
    _ ≤ ∑ _i ∈ Finset.range n, b := by
        apply Finset.sum_le_sum
        intro i _
        apply hb
        calc (window n i L ∩ (Finset.range n).erase i₀).card ≤ (window n i L).card :=
              Finset.card_le_card Finset.inter_subset_left
          _ ≤ (Finset.range L).card := by
              unfold window
              exact Finset.card_image_le
          _ = L := Finset.card_range L
    _ = n * b := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
end

set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
namespace UpperTheory.BernoulliSumsFrobeniusOrbits
theorem _root_.solution :
    ∀ (p : ℕ → ℝ) (δ : ℝ) (n L₂ K r u M₀ G' N₁ i₀ : ℕ), (∀ a, 3 / 4 * δ ≤ p a ∧ p a ≤ δ) → 0 ≤ δ → δ ≤ 1 → 1 ≤ u →
      (M₀ + 1) * ((6 * r + 1) * u) ≤ n →
      exP p ((range n).erase i₀) (fun U => ind (¬ GoodOrbitIntervalTileCondition n (insert i₀ U) L₂ K r u M₀ G' N₁)) ≤
        n * (L₂.choose K : ℝ) * δ ^ K + n * (1 - markedLow δ r u) ^ M₀ + n * binUpper G' δ (N₁ - 1) := by
  intro p δ n L₂ K r u M₀ G' N₁ i₀ hp hδ0 hδ1 hu hn
  obtain ⟨_, h_add, _, h_mono, _, _, _⟩ := expectation_spec p
  have hp1 : ∀ a, 0 ≤ p a ∧ p a ≤ 1 := fun a =>
    ⟨le_trans (by positivity) (hp a).1, le_trans (hp a).2 hδ1⟩
  have hpδ : ∀ (A : Finset ℕ), ∀ a ∈ A, 0 ≤ p a ∧ p a ≤ δ := fun A a _ => ⟨(hp1 a).1, (hp a).2⟩
  have hA : exP p ((range n).erase i₀) (fun U => ind (¬ CondA n (insert i₀ U) L₂ K))
      ≤ n * ((L₂.choose K : ℝ) * δ ^ K) :=
    ngl_windows_le p hp1 n i₀ L₂ K K le_rfl _
      (fun A hA => (tail_le p δ A L₂ K (hpδ A) hδ0 hδ1 hA).1)
  have hI : exP p ((range n).erase i₀) (fun U => ind (¬ CondIntervals n (insert i₀ U) G' N₁))
      ≤ n * binUpper G' δ (N₁ - 1) :=
    ngl_windows_le p hp1 n i₀ G' N₁ (N₁ - 1) (Nat.sub_le _ _) _
      (fun A hA => (tail_le p δ A G' (N₁ - 1) (hpδ A) hδ0 hδ1 hA).2)
  have hT := tiles_le p δ n r u M₀ i₀ hp hδ0 hδ1 hu hn
  have hsplit : exP p ((range n).erase i₀)
        (fun U => ind (¬ GoodOrbitIntervalTileCondition n (insert i₀ U) L₂ K r u M₀ G' N₁))
      ≤ exP p ((range n).erase i₀) (fun U => (ind (¬ CondA n (insert i₀ U) L₂ K)
          + ind (¬ CondTiles n (insert i₀ U) r u M₀))
          + ind (¬ CondIntervals n (insert i₀ U) G' N₁)) := by
    apply h_mono _ _ _ (fun a _ => hp1 a)
    intro U _
    have e1 := ngl_ind_nonneg (¬ CondA n (insert i₀ U) L₂ K)
    have e2 := ngl_ind_nonneg (¬ CondTiles n (insert i₀ U) r u M₀)
    have e3 := ngl_ind_nonneg (¬ CondIntervals n (insert i₀ U) G' N₁)
    apply ngl_ind_le (by linarith)
    intro hq
    unfold GoodOrbitIntervalTileCondition at hq
    by_cases ha : CondA n (insert i₀ U) L₂ K
    · by_cases hb : CondTiles n (insert i₀ U) r u M₀
      · have hc : ¬ CondIntervals n (insert i₀ U) G' N₁ := fun hc => hq ⟨ha, hb, hc⟩
        rw [ngl_ind_pos hc]
        linarith
      · rw [ngl_ind_pos hb]
        linarith
    · rw [ngl_ind_pos ha]
      linarith
  have hsum : exP p ((range n).erase i₀) (fun U => (ind (¬ CondA n (insert i₀ U) L₂ K)
          + ind (¬ CondTiles n (insert i₀ U) r u M₀))
          + ind (¬ CondIntervals n (insert i₀ U) G' N₁))
      = exP p ((range n).erase i₀) (fun U => ind (¬ CondA n (insert i₀ U) L₂ K))
        + exP p ((range n).erase i₀) (fun U => ind (¬ CondTiles n (insert i₀ U) r u M₀))
        + exP p ((range n).erase i₀) (fun U => ind (¬ CondIntervals n (insert i₀ U) G' N₁)) := by
    rw [h_add _ (fun U => ind (¬ CondA n (insert i₀ U) L₂ K)
          + ind (¬ CondTiles n (insert i₀ U) r u M₀))
        (fun U => ind (¬ CondIntervals n (insert i₀ U) G' N₁)),
      h_add _ (fun U => ind (¬ CondA n (insert i₀ U) L₂ K))
        (fun U => ind (¬ CondTiles n (insert i₀ U) r u M₀))]
  rw [hsum] at hsplit
  have hA' : (n : ℝ) * ((L₂.choose K : ℝ) * δ ^ K) = n * (L₂.choose K : ℝ) * δ ^ K := by ring
  linarith
end UpperTheory.BernoulliSumsFrobeniusOrbits
