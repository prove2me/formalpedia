-- Prove2me | solution 1 for TimeDepFolk.Asymptotic.eq_5_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:09:31.321975+00:00
-- url     : https://prove2.me/submissions/9a4f2b59-c284-42af-83a5-efb2f53b9e27

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TDFTail

open TimeDepFolk.Asymptotic Finset

theorem summable_shift (θ : Evaluation) (n : ℕ) : Summable (fun r => θ.θ (n + r)) := by
  have := (summable_nat_add_iff n).2 θ.hasSum.summable
  simpa [add_comm] using this

theorem tail_nonneg (θ : Evaluation) (n : ℕ) : 0 ≤ ∑' r, θ.θ (n + r) :=
  tsum_nonneg fun r => θ.nonneg _

theorem cont_nonneg (θ : Evaluation) (n t : ℕ) : 0 ≤ cont θ.θ n t :=
  div_nonneg (θ.nonneg _) (tail_nonneg θ n)

theorem cont_le_zero (θ : Evaluation) (n t : ℕ) : cont θ.θ n t ≤ cont θ.θ n 0 :=
  div_le_div_of_nonneg_right (θ.antitone (by omega)) (tail_nonneg θ n)

theorem cont_antitone (θ : Evaluation) (n : ℕ) : Antitone (cont θ.θ n) :=
  fun _ _ h => div_le_div_of_nonneg_right (θ.antitone (by omega)) (tail_nonneg θ n)

theorem hasSum_cont (θ : Evaluation) (n : ℕ) (h : 0 < ∑' r, θ.θ (n + r)) :
    HasSum (cont θ.θ n) 1 := by
  have := ((summable_shift θ n).hasSum).div_const (∑' r, θ.θ (n + r))
  rwa [div_self h.ne'] at this

theorem sum_range_cont (θ : Evaluation) (n m : ℕ) :
    ∑ t ∈ range m, cont θ.θ n t = (∑ t ∈ range m, θ.θ (n + t)) / ∑' r, θ.θ (n + r) := by
  simp only [cont, Finset.sum_div]

theorem tail_split (θ : Evaluation) (n m : ℕ) :
    ∑' r, θ.θ (n + r) = ∑ r ∈ range m, θ.θ (n + r) + ∑' r, θ.θ (n + m + r) := by
  have := (summable_shift θ n).sum_add_tsum_nat_add m
  rw [← this]
  congr 1
  refine tsum_congr fun r => ?_
  congr 1; omega

end TDFTail

open TimeDepFolk.Asymptotic Finset

theorem solution (θ : Evaluation) (n : ℕ) (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η)
    (hηκ : η < κ / 8) (hηκ' : η < 1 / κ) (htail : 0 < ∑' r, θ.θ (n + r))
    (hθ1 : cont θ.θ n 0 ≤ η ^ 2) :
    ∃ L : ℕ, IsPunLength θ κ η n L := by
  set c := cont θ.θ n with hc
  set S : ℕ → ℝ := fun m => ∑ t ∈ range m, c t with hS
  have hsum : HasSum c 1 := TDFTail.hasSum_cont θ n htail
  -- each weight is below `η / κ`
  have hstep : ∀ t, c t < η / κ := by
    intro t
    have h1 : η ^ 2 < η / κ := by
      rw [lt_div_iff₀ hκ]
      have : η * κ < 1 := by rwa [lt_div_iff₀ hκ] at hηκ'
      nlinarith
    exact lt_of_le_of_lt ((TDFTail.cont_le_zero θ n t).trans hθ1) h1
  have h3 : 3 * η / κ < 1 := by
    rw [div_lt_one hκ]; linarith
  -- some partial sum reaches `3η/κ`
  have hex : ∃ m, 3 * η / κ ≤ S m := by
    have ht := hsum.tendsto_sum_nat
    obtain ⟨m, hm⟩ := Filter.eventually_atTop.1 (ht.eventually (lt_mem_nhds h3))
    exact ⟨m, (hm m le_rfl).le⟩
  classical
  let m := Nat.find hex
  have hm : 3 * η / κ ≤ S m := Nat.find_spec hex
  have hpos3 : 0 < 3 * η / κ := by positivity
  have hm0 : m ≠ 0 := by
    intro h0
    have : S m = 0 := by rw [h0]; simp [hS]
    linarith
  have hm1 : m ≠ 1 := by
    intro h1
    have : S m = c 0 := by rw [h1]; simp [hS]
    have := hstep 0
    have : η / κ < 3 * η / κ := by
      apply div_lt_div_of_pos_right _ hκ; linarith
    linarith
  obtain ⟨L, hL⟩ : ∃ L, m = L + 1 := ⟨m - 1, by omega⟩
  have hprev : S L < 3 * η / κ := by
    have := Nat.find_min hex (show L < m by omega)
    exact lt_of_not_ge this
  refine ⟨L, by omega, ?_, ?_⟩
  · rw [← hL]; exact hm
  · have e : S (L + 1) = S L + c L := by simp [hS, Finset.sum_range_succ]
    show S (L + 1) < 4 * η / κ
    rw [e]
    have := hstep L
    have e2 : 4 * η / κ = 3 * η / κ + η / κ := by ring
    linarith
