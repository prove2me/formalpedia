-- Prove2me | solution 1 for SchoenfeldBRH.zero_count_upper_low_heights
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T04:02:45.214353+00:00
-- url     : https://prove2.me/submissions/da36e1e9-a8f1-4f72-958d-7deca3980303
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_dusart_psi_433_20261014_ZeroCard
import Theorems.Thm_ZeroCount_low_band_count
import Theorems.Thm_ZeroCount_mid_band_count
import Theorems.Thm_ZeroCount_grid_low
import Theorems.Thm_ZeroCount_grid_bridge
import Theorems.Thm_ZeroCount_grid_B
import Theorems.Thm_ZeroCount_grid_lowpts

open Complex DusartSmoothing.RvM

namespace ZC

theorem key_finset (t : ℝ) (ht0 : 0 ≤ t) (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ∈ zerosIn 0 t)
    (s : Finset ℝ) (hs : ∀ x ∈ s, t < x ∧ x ≤ 65000 ∧ riemannZeta (1 / 2 + (x : ℂ) * I) = 0)
    (ht : t ≤ 65000) :
    (∑ ρ ∈ S, zeroMult ρ) + s.card ≤ 85288 := by
  classical
  let f : ℝ → ℂ := fun x => (1 / 2 : ℂ) + (x : ℂ) * I
  have hf : Function.Injective f := by
    intro a b h
    have := congrArg Complex.im h
    simpa [f] using this
  let L := s.image f
  have hL : L.card = s.card := Finset.card_image_of_injective s hf
  have hdisj : Disjoint S L := by
    rw [Finset.disjoint_left]
    intro ρ hρ hρL
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hρL
    have h1 := (hS _ hρ).2.2
    have h2 := (hs x hx).1
    simp [f] at h1
    linarith
  have hU : ∀ ρ ∈ S ∪ L, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ 65000 := by
    intro ρ hρ
    rcases Finset.mem_union.mp hρ with h | h
    · obtain ⟨⟨hz, h0, h1⟩, hi0, hi1⟩ := hS ρ h
      exact ⟨hz, h0, h1, hi0, by linarith⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hx0, hx1, hz⟩ := hs x hx
      refine ⟨hz, ?_, ?_, ?_, ?_⟩ <;> simp [f] <;> linarith
  have hsplit := Finset.sum_filter_add_sum_filter_not (S ∪ L) (fun ρ : ℂ => ρ.im ≤ 121)
    (fun ρ => zeroMult ρ)
  have h1 : ∑ ρ ∈ (S ∪ L).filter (fun ρ : ℂ => ρ.im ≤ 121), zeroMult ρ ≤ 38 := by
    apply ZeroCount.low_band_count
    intro ρ hρ
    obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hρ
    obtain ⟨a, b, c, d, _⟩ := hU ρ hm
    exact ⟨a, b, c, d, hp⟩
  have h2 : ∑ ρ ∈ (S ∪ L).filter (fun ρ : ℂ => ¬ ρ.im ≤ 121), zeroMult ρ ≤ 85250 := by
    apply ZeroCount.mid_band_count
    intro ρ hρ
    obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hρ
    obtain ⟨a, b, c, _, e⟩ := hU ρ hm
    exact ⟨a, b, c, by push Not at hp; linarith, e⟩
  have hunion := Finset.sum_union hdisj (f := fun ρ => zeroMult ρ)
  have hLge : L.card ≤ ∑ ρ ∈ L, zeroMult ρ := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro ρ hρ
    obtain ⟨a, b, c, d, _⟩ := hU ρ (Finset.mem_union_right _ hρ)
    exact zeroMult_pos_of_positive_height ρ ⟨a, b, c⟩ d
  omega

theorem key (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 65000) (s : Finset ℝ)
    (hs : ∀ x ∈ s, t < x ∧ x ≤ 65000 ∧ riemannZeta (1 / 2 + (x : ℂ) * I) = 0) :
    Ncount 0 t + s.card ≤ 85288 := by
  classical
  unfold Ncount
  by_cases hfin : (zerosIn 0 t).Finite
  · rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    exact key_finset t ht0 _ (fun ρ h => hfin.mem_toFinset.mp h) s hs ht
  · have hz : ∑ᶠ ρ ∈ zerosIn 0 t, zeroMult ρ = 0 := by
      apply finsum_mem_eq_zero_of_infinite
      intro hfin2
      apply hfin
      apply hfin2.subset
      intro ρ hρ
      refine ⟨hρ, ?_⟩
      have := zeroMult_pos_of_positive_height ρ hρ.1 hρ.2.1
      simp only [Function.mem_support]
      omega
    rw [hz]
    have := key_finset t ht0 ∅ (by simp) s hs ht
    simpa using this

end ZC

theorem solution :
    ∀ t : ℝ, 14 ≤ t → t ≤ 2500 →
      (DusartSmoothing.RvM.Ncount 0 t : ℝ) ≤
        t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) - 1) + 5 / 2 := by
  intro t h14 h25
  obtain ⟨s, hR, hs⟩ : ∃ s : Finset ℝ, (85288 : ℝ) - s.card ≤
      t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) - 1) + 5 / 2 ∧
      ∀ x ∈ s, t < x ∧ x ≤ 65000 ∧ riemannZeta (1 / 2 + (x : ℂ) * Complex.I) = 0 := by
    by_cases c1 : t < 121
    · exact ZeroCount.grid_lowpts t h14 c1
    push Not at c1
    by_cases c2 : t < 520
    · exact ZeroCount.grid_B.1 t c1 c2
    push Not at c2
    by_cases c3 : t < (65573390 : ℝ) / 65536
    · exact ZeroCount.grid_bridge.1 t c2 c3
    push Not at c3
    exact ZeroCount.grid_low.1 t c3 (by norm_num; linarith)
  have hk := ZC.key t (by linarith) (by linarith) s hs
  have hk' : (DusartSmoothing.RvM.Ncount 0 t : ℝ) + s.card ≤ 85288 := by exact_mod_cast hk
  linarith
