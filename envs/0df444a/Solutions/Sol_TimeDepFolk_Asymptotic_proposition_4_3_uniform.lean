-- Prove2me | solution 1 for TimeDepFolk.Asymptotic.proposition_4_3_uniform
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:13:14.365825+00:00
-- url     : https://prove2.me/submissions/a363df13-76a5-4b41-a39a-11d9c1a0bbb4

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model
import Theorems.Thm_TimeDepFolk_Asymptotic_proposition_4_3
import Theorems.Thm_TimeDepFolk_Asymptotic_lemma_4_2

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

open TimeDepFolk.Asymptotic

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    (g : I → (∀ i, A i) → ℝ) (θ : ℕ → Evaluation) (hθ : IsPatient θ) :
    ∀ η > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ n : ℕ, ∀ x ∈ F g, ∃ h : ℕ → (∀ i, A i),
      purePayoff g (cont (θ k).θ n) h = x ∧
        ∀ T ≥ 1,
          ‖purePayoff g (cont (cont (θ k).θ n) T) (fun s => h (T + s)) - x‖ ≤ η := by
  classical
  intro η hη
  -- the property that fails at `(k, n)`
  let P : ℕ → ℕ → Prop := fun k n => ¬ ∀ x ∈ F g, ∃ h : ℕ → (∀ i, A i),
      purePayoff g (cont (θ k).θ n) h = x ∧
        ∀ T ≥ 1, ‖purePayoff g (cont (cont (θ k).θ n) T) (fun s => h (T + s)) - x‖ ≤ η
  let nk : ℕ → ℕ := fun k => if hk : ∃ n, P k n then hk.choose else 0
  have hnk : ∀ k, (∃ n, P k n) → P k (nk k) := by
    intro k hk
    simp only [nk, dif_pos hk]
    exact hk.choose_spec
  -- the shifted evaluations
  let E : ℕ → Evaluation := fun k =>
    if ht : 0 < ∑' r, (θ k).θ (nk k + r) then
      ⟨cont (θ k).θ (nk k), TDFTail.cont_nonneg (θ k) (nk k),
        TDFTail.cont_antitone (θ k) (nk k), TDFTail.hasSum_cont (θ k) (nk k) ht⟩
    else θ k
  have h42 := (lemma_4_2 θ hθ).2
  rw [Metric.tendstoUniformly_iff] at h42
  -- eventually every tail is positive
  have htail : ∀ᶠ k in Filter.atTop, ∀ n, 0 < ∑' r, (θ k).θ (n + r) := by
    filter_upwards [h42 (1 / 2) (by norm_num)] with k hk n
    rcases (TDFTail.tail_nonneg (θ k) n).eq_or_lt with h0 | h0
    · exfalso
      have := hk (n, 0)
      simp only [cont, ← h0, div_zero, dist_zero_right, norm_one] at this
      norm_num at this
    · exact h0
  have hE : IsPatient E := by
    rw [IsPatient, Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [h42 ε hε, htail] with k hk ht t
    have : E k = ⟨cont (θ k).θ (nk k), TDFTail.cont_nonneg (θ k) (nk k),
        TDFTail.cont_antitone (θ k) (nk k), TDFTail.hasSum_cont (θ k) (nk k) (ht _)⟩ := by
      simp only [E, dif_pos (ht (nk k))]
    rw [this]
    exact hk (nk k, t)
  obtain ⟨K, hK⟩ := proposition_4_3 g E hE η hη
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.1 htail
  refine ⟨max K K0, fun k hk n x hx => ?_⟩
  by_contra hfail
  have hP : P k n := fun hall => hfail (hall x hx)
  have hPn := hnk k ⟨n, hP⟩
  have ht := hK0 k (le_of_max_le_right hk)
  have hEk : (E k).θ = cont (θ k).θ (nk k) := by
    simp only [E, dif_pos (ht (nk k))]
  apply hPn
  intro y hy
  have := hK y hy k (le_of_max_le_left hk)
  rwa [hEk] at this
