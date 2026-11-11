-- Prove2me | solution 1 for SturtRobustStop.Structure.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T02:18:24.37269+00:00
-- url     : https://prove2.me/submissions/a0788b86-92c5-442a-bd20-71c9d72d6117

import Mathlib
import Definitions.Def_SturtRobustStop_Structure_Pruning

set_option autoImplicit false

open scoped ENNReal NNReal

namespace SturtRobustStop.Structure.Thm4Aux
open SturtRobustStop.Structure

theorem firstIndex_eq_some {T : ℕ} (p : Fin T → Prop) (t : Fin T) (ht : p t)
    (hlt : ∀ t' : Fin T, t' < t → ¬ p t') : firstIndex p = some t := by
  classical
  unfold firstIndex
  dsimp only
  split_ifs with hne
  · congr 1
    apply le_antisymm
    · exact Finset.min'_le _ _ (by simp [ht])
    · apply Finset.le_min'
      intro y hy
      have hy' : p y := by simpa using hy
      by_contra hcon
      exact hlt y (not_le.1 hcon) hy'
  · exact absurd ⟨t, by simp [ht]⟩ hne

theorem firstIndex_spec {T : ℕ} (p : Fin T → Prop) (t : Fin T)
    (h : firstIndex p = some t) : p t ∧ ∀ t' : Fin T, t' < t → ¬ p t' := by
  classical
  unfold firstIndex at h
  dsimp only at h
  split_ifs at h with hne
  · have h' := Option.some.inj h
    subst h'
    refine ⟨by simpa using Finset.min'_mem _ hne, ?_⟩
    intro t' ht' hp
    exact absurd ht' (not_lt.2 (Finset.min'_le _ t' (by simpa using hp)))

theorem firstIndex_exists {T : ℕ} (p : Fin T → Prop) (t : Fin T) (ht : p t) :
    ∃ t', firstIndex p = some t' ∧ t' ≤ t := by
  classical
  unfold firstIndex
  dsimp only
  split_ifs with hne
  · exact ⟨_, rfl, Finset.min'_le _ _ (by simpa using ht)⟩
  · exact absurd ⟨t, by simpa using ht⟩ hne

theorem firstIndex_none {T : ℕ} (p : Fin T → Prop) (h : ∀ t, ¬ p t) :
    firstIndex p = none := by
  classical
  unfold firstIndex
  dsimp only
  split_ifs with hne
  · obtain ⟨x, hx⟩ := hne
    exact absurd (by simpa using hx) (h x)
  · rfl

theorem mem_guaranteedTimes {T N d : ℕ} (D : Model T N d) (μ : Policy T (State d))
    (i : Fin N) (t : Fin T) : t ∈ guaranteedTimes D μ i ↔ box D i t ⊆ μ.stop t := by
  unfold guaranteedTimes
  simp

noncomputable def sig {T N d : ℕ} (D : Model T N d) (μ : Policy T (State d)) :
    Fin N → Fin T :=
  fun i => if h : (guaranteedTimes D μ i).Nonempty then (guaranteedTimes D μ i).min' h
    else ⟨T - 1, Nat.sub_lt D.horizon_pos Nat.one_pos⟩

theorem key {T N d : ℕ} (D : Model T N d) (μ : Policy T (State d)) (i : Fin N) :
    sampleReward D μ i ≤ sampleReward D (assignedPolicy D (sig D μ)) i := by
  by_cases hne : (guaranteedTimes D μ i).Nonempty
  · set s := (guaranteedTimes D μ i).min' hne with hs
    have hsig : sig D μ i = s := by simp only [sig, dif_pos hne, hs]
    have hs_mem : box D i s ⊆ μ.stop s :=
      (mem_guaranteedTimes D μ i s).1 (Finset.min'_mem _ _)
    have hbefore : ∀ t' : Fin T, t' < s → ∃ z ∈ box D i t', z ∉ μ.stop t' := by
      intro t' ht'
      by_contra hcon
      push Not at hcon
      have hmem : t' ∈ guaranteedTimes D μ i := (mem_guaranteedTimes D μ i t').2 hcon
      exact absurd (Finset.min'_le _ _ hmem) (not_le.2 ht')
    unfold sampleReward
    refine le_iInf fun yy => ?_
    obtain ⟨y, hy⟩ := yy
    have hyA : y s ∈ (assignedPolicy D (sig D μ)).stop s := by
      show y s ∈ ⋃ j : {j : Fin N // sig D μ j = s}, box D j.val s
      exact Set.mem_iUnion.2 ⟨⟨i, hsig⟩, hy s⟩
    obtain ⟨t, ht, hts⟩ :=
      firstIndex_exists (fun t => y t ∈ (assignedPolicy D (sig D μ)).stop t) s hyA
    have hstA : stoppingTime (assignedPolicy D (sig D μ)) y = some t := ht
    obtain ⟨htA, _⟩ := firstIndex_spec _ _ ht
    have hyt : y t ∈ μ.stop t := by
      rcases eq_or_lt_of_le hts with h | h
      · rw [h]; exact hs_mem (hy s)
      · have htA' : y t ∈ ⋃ j : {j : Fin N // sig D μ j = t}, box D j.val t := htA
        obtain ⟨⟨j, hj⟩, hjy⟩ := Set.mem_iUnion.1 htA'
        by_cases hjne : (guaranteedTimes D μ j).Nonempty
        · have hsub : box D j (sig D μ j) ⊆ μ.stop (sig D μ j) := by
            simp only [sig, dif_pos hjne]
            exact (mem_guaranteedTimes D μ j _).1 (Finset.min'_mem _ _)
          rw [hj] at hsub
          exact hsub hjy
        · exfalso
          have hl : sig D μ j = ⟨T - 1, Nat.sub_lt D.horizon_pos Nat.one_pos⟩ := by
            simp only [sig, dif_neg hjne]
          have htv : t.val = T - 1 := by rw [← hj, hl]
          have hslt := s.isLt
          rw [Fin.lt_def] at h
          omega
    choose! zf hzf using hbefore
    let y' : Path T d := fun t' => if t' < t then zf t' else y t'
    have hy' : y' ∈ uncertainty D i := by
      intro t'
      by_cases h : t' < t
      · simp only [y', if_pos h]; exact (hzf t' (lt_of_lt_of_le h hts)).1
      · simp only [y', if_neg h]; exact hy t'
    have hstop : stoppingTime μ y' = some t := by
      apply firstIndex_eq_some
      · simp only [y', lt_irrefl, if_false]; exact hyt
      · intro t' h'
        simp only [y', if_pos h']
        exact (hzf t' (lt_of_lt_of_le h' hts)).2
    calc ⨅ yy : {y // y ∈ uncertainty D i},
          (D.payoff (stoppingTime μ yy.val) (D.sample i) : ℝ≥0∞)
        ≤ (D.payoff (stoppingTime μ y') (D.sample i) : ℝ≥0∞) :=
          iInf_le_of_le ⟨y', hy'⟩ le_rfl
      _ = _ := by rw [hstop, hstA]
  · have hall : ∀ t : Fin T, ∃ z ∈ box D i t, z ∉ μ.stop t := by
      intro t
      by_contra hcon
      push Not at hcon
      exact hne ⟨t, (mem_guaranteedTimes D μ i t).2 hcon⟩
    choose zf hzf using hall
    have hmem : zf ∈ uncertainty D i := fun t => (hzf t).1
    have hnone : stoppingTime μ zf = none := firstIndex_none _ (fun t => (hzf t).2)
    calc sampleReward D μ i
        ≤ (D.payoff (stoppingTime μ zf) (D.sample i) : ℝ≥0∞) :=
          iInf_le_of_le ⟨zf, hmem⟩ le_rfl
      _ = 0 := by rw [hnone]; rfl
      _ ≤ _ := by simp

end SturtRobustStop.Structure.Thm4Aux

open SturtRobustStop.Structure in
theorem solution {T N d : ℕ} (D : Model T N d) :
    ∃ μstar : Policy T (State d), μstar ∈ family D ∧
      ∀ μ : Policy T (State d), objective D μ ≤ objective D μstar := by
  have : Nonempty (Fin T) := ⟨⟨0, D.horizon_pos⟩⟩
  obtain ⟨σ, hσ⟩ :=
    Finite.exists_max (fun σ : Fin N → Fin T => objective D (assignedPolicy D σ))
  refine ⟨assignedPolicy D σ, ⟨σ, rfl⟩, fun μ => ?_⟩
  refine le_trans ?_ (hσ (SturtRobustStop.Structure.Thm4Aux.sig D μ))
  unfold objective
  exact ENNReal.div_le_div_right
    (Finset.sum_le_sum fun i _ => SturtRobustStop.Structure.Thm4Aux.key D μ i) _
