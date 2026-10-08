-- Prove2me | solution 1 for SchedComplexity.TotalCompletion.claim_B
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:41:17.173635+00:00
-- url     : https://prove2.me/submissions/c78e38d6-a009-48d9-ad09-3b093e87a196

import Mathlib
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
import Definitions.Def_SchedComplexity_TotalCompletion_Construction



namespace SchedComplexity.TotalCompletion

theorem tc_lt_of_le {ι : Type*} (p B : ι → ℕ) (hpos : ∀ j, 0 < p j)
    (hd : ∀ j k : ι, j ≠ k → ¬ (B j < B k + p k ∧ B k < B j + p j))
    {j k : ι} (hjk : j ≠ k) (h : B j ≤ B k) : B j + p j ≤ B k := by
  by_contra hc
  push Not at hc
  exact hd j k hjk ⟨by have := hpos k; omega, hc⟩

theorem tc_chain {ι : Type*} [DecidableEq ι] (p B : ι → ℕ) (hpos : ∀ j, 0 < p j)
    (hd : ∀ j k : ι, j ≠ k → ¬ (B j < B k + p k ∧ B k < B j + p j))
    (s0 q : ℕ) (S : Finset ι) (hS : ∀ k ∈ S, s0 ≤ B k ∧ q ≤ p k) :
    (∀ z, z ∉ S → s0 ≤ B z → (∀ k ∈ S, B k < B z) → s0 + S.card * q ≤ B z) ∧
    2 * (S.card * s0) + q * (S.card * (S.card + 1)) ≤ 2 * ∑ k ∈ S, (B k + p k) := by
  revert hS
  refine Finset.induction_on_max_value B S ?_ ?_
  · intro _
    refine ⟨fun z _ h _ => by simpa using h, by simp⟩
  · intro a s ha hmax ih hS
    have hs : ∀ k ∈ s, s0 ≤ B k ∧ q ≤ p k := fun k hk => hS k (Finset.mem_insert_of_mem hk)
    obtain ⟨ihb, iha⟩ := ih hs
    have hlt : ∀ k ∈ s, B k < B a := by
      intro k hk
      have hka : k ≠ a := fun h => ha (h ▸ hk)
      have := tc_lt_of_le p B hpos hd hka (hmax k hk)
      have := hpos k
      omega
    have hBa := ihb a ha (hS a (Finset.mem_insert_self _ _)).1 hlt
    have hpa := (hS a (Finset.mem_insert_self _ _)).2
    have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha
    refine ⟨?_, ?_⟩
    · intro z hz _ hzlt
      have hza : a ≠ z := fun h => hz (h ▸ Finset.mem_insert_self _ _)
      have := tc_lt_of_le p B hpos hd hza (le_of_lt (hzlt a (Finset.mem_insert_self _ _)))
      rw [hcard]
      nlinarith
    · rw [Finset.sum_insert ha, hcard]
      nlinarith

theorem tc_len {ι : Type*} [DecidableEq ι] (p B : ι → ℕ) (hpos : ∀ j, 0 < p j)
    (hd : ∀ j k : ι, j ≠ k → ¬ (B j < B k + p k ∧ B k < B j + p j))
    (s0 : ℕ) (S : Finset ι) :
    ∀ e, s0 ≤ e → (∀ k ∈ S, s0 ≤ B k ∧ B k + p k ≤ e) → s0 + ∑ k ∈ S, p k ≤ e := by
  refine Finset.induction_on_max_value B S ?_ ?_
  · intro e he _
    simpa using he
  · intro a s ha hmax ih e he hS
    have hs : ∀ k ∈ s, s0 ≤ B k ∧ B k + p k ≤ B a := by
      intro k hk
      have hka : k ≠ a := fun h => ha (h ▸ hk)
      exact ⟨(hS k (Finset.mem_insert_of_mem hk)).1, tc_lt_of_le p B hpos hd hka (hmax k hk)⟩
    have h1 := ih (B a) (hS a (Finset.mem_insert_self _ _)).1 hs
    rw [Finset.sum_insert ha]
    have := (hS a (Finset.mem_insert_self _ _)).2
    omega


section spec
variable {t : ℕ} (a : Fin t → ℕ) (b : ℕ)

theorem tc_tau_pos : 0 < tau a b := by unfold tau; positivity

theorem tc_u_pos : 0 < uCount a b := by
  have := tc_tau_pos a b
  unfold uCount
  exact Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.succ_pos t) this) (Nat.le_add_left _ _)

theorem tc_ups_pos : 0 < upsilon a b := Nat.mul_pos (tc_u_pos a b) (Nat.succ_pos _)

theorem tc_proc_pos (j : Fin (numJobs a b)) : 0 < procTime a b j := by
  have := tc_tau_pos a b
  have := tc_ups_pos a b
  unfold procTime
  split_ifs <;> omega

theorem tc_proc_long (j : Fin (numJobs a b)) (h : j.val < t + tPrime a) :
    tau a b ≤ procTime a b j := by
  unfold procTime
  split_ifs <;> first | exact Nat.le_add_right _ _ | exact le_rfl | omega

theorem tc_mem_U (j : Fin (numJobs a b)) :
    j ∈ groupU a b ↔ t + tPrime a ≤ j.val ∧ j.val < t + tPrime a + uCount a b := by
  simp [groupU]

theorem tc_proc_U (j : Fin (numJobs a b)) (h : j ∈ groupU a b) :
    procTime a b j = upsilon a b := by
  rw [tc_mem_U] at h
  unfold procTime
  split_ifs <;> first | rfl | omega

theorem tc_proc_last : procTime a b (lastJob a b) = 1 := by
  have hv : (lastJob a b).val = t + tPrime a + uCount a b := rfl
  unfold procTime
  rw [dif_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega)]

theorem tc_not_U_last : lastJob a b ∉ groupU a b := by
  rw [tc_mem_U]; unfold lastJob; simp

theorem tc_card_filter (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter fun j : Fin n => P j.val).card = ((Finset.range n).filter P).card := by
  refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp [hj]
  · intro x _ y _ h
    exact Fin.ext h
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    exact ⟨⟨x, hx.1⟩, by simp [hx.2], rfl⟩

theorem tc_card_U : (groupU a b).card = uCount a b := by
  have : groupU a b = Finset.univ.filter fun j : Fin (numJobs a b) =>
      (t + tPrime a ≤ j.val ∧ j.val < t + tPrime a + uCount a b) := rfl
  rw [this]
  refine (tc_card_filter (numJobs a b) (fun i => t + tPrime a ≤ i ∧ i < t + tPrime a + uCount a b)).trans ?_
  have : (Finset.range (numJobs a b)).filter (fun i => t + tPrime a ≤ i ∧ i < t + tPrime a + uCount a b)
      = Finset.Ico (t + tPrime a) (t + tPrime a + uCount a b) := by
    ext i; simp [numJobs]; omega
  rw [this]; simp

theorem tc_card_L : (Finset.univ.filter fun j : Fin (numJobs a b) => j.val < t + tPrime a).card
    = t + tPrime a := by
  refine (tc_card_filter (numJobs a b) (fun i => i < t + tPrime a)).trans ?_
  have : (Finset.range (numJobs a b)).filter (fun i => i < t + tPrime a)
      = Finset.range (t + tPrime a) := by
    ext i; simp [numJobs]; omega
  rw [this]; simp


theorem tc_sum_nonU : ∑ j ∈ (groupU a b)ᶜ, procTime a b j = sigma a b := by
  classical
  let pt : ℕ → ℕ := fun i => if h : i < t then tau a b + a ⟨i, h⟩
    else if i < t + tPrime a then tau a b
    else if i < t + tPrime a + uCount a b then upsilon a b else 1
  have hp : ∀ j : Fin (numJobs a b), procTime a b j = pt j.val := fun j => rfl
  have hc : (groupU a b)ᶜ = Finset.univ.filter fun j : Fin (numJobs a b) =>
      ¬ (t + tPrime a ≤ j.val ∧ j.val < t + tPrime a + uCount a b) := by
    ext j; simp [tc_mem_U]
  rw [hc, Finset.sum_filter]
  let g : ℕ → ℕ := fun i =>
    if ¬ (t + tPrime a ≤ i ∧ i < t + tPrime a + uCount a b) then pt i else 0
  have h0 : ∑ j : Fin (numJobs a b), (if ¬ (t + tPrime a ≤ j.val ∧ j.val < t + tPrime a + uCount a b)
      then procTime a b j else 0) = ∑ j : Fin (numJobs a b), g j.val := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [g, hp]
  rw [h0, Fin.sum_univ_eq_sum_range g (numJobs a b)]
  have hn : numJobs a b = (t + tPrime a) + uCount a b + 1 := rfl
  rw [hn, Finset.sum_range_succ, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range (uCount a b), g (t + tPrime a + x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_range] at hx
    simp only [g]
    rw [if_neg (by omega)]
  have h3 : g (t + tPrime a + uCount a b) = 1 := by
    simp only [g, pt]
    rw [if_pos (by omega), dif_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have h2 : ∑ x ∈ Finset.range (t + tPrime a), g x = ∑ x ∈ Finset.range (t + tPrime a), pt x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    simp only [g]
    rw [if_pos (by omega)]
  rw [h1, h3, h2, Finset.sum_range_add]
  have h4 : ∑ x ∈ Finset.range t, pt x = ∑ i : Fin t, (tau a b + a i) := by
    rw [← Fin.sum_univ_eq_sum_range pt t]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pt]
    rw [dif_pos i.2]
  have h5 : ∑ x ∈ Finset.range (tPrime a), pt (t + x) = tPrime a * tau a b := by
    rw [Finset.sum_const_nat (m := tau a b)]
    · simp
    · intro x hx
      rw [Finset.mem_range] at hx
      simp only [pt]
      rw [dif_neg (by omega), if_pos (by omega)]
  rw [h4, h5, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  unfold sigma sumA
  ring


theorem tc_y2 : 2 * yThreshold a b = 2 * upsilon a b + uCount a b * (uCount a b + 1) * upsilon a b := by
  have h : 2 * (uCount a b * (uCount a b + 1) / 2) = uCount a b * (uCount a b + 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_succ_self _).two_dvd
  unfold yThreshold
  nlinarith [h]

theorem tc_ups_eq : upsilon a b = uCount a b * sigma a b + uCount a b := by
  unfold upsilon; ring

theorem tc_claimA_core (B : Fin (numJobs a b) → ℕ)
    (hB : IsFeasible (procTime a b) (release a b) B)
    (hy : ∑ j, completion (procTime a b) B j ≤ yThreshold a b) :
    ∀ j' j : Fin (numJobs a b), j' ∉ groupU a b → j ∈ groupU a b → B j' < B j := by
  intro j' j hj' hj
  by_contra hcon
  push Not at hcon
  have hpos := tc_proc_pos a b
  have hd := hB.2
  have hne : j ≠ j' := fun h => hj' (h ▸ hj)
  have h1 := tc_lt_of_le _ _ hpos hd hne hcon
  rw [tc_proc_U a b j hj] at h1
  have h2 := (tc_chain (procTime a b) B hpos hd 0 (upsilon a b) (groupU a b)
    (fun k hk => ⟨Nat.zero_le _, (tc_proc_U a b k hk).ge⟩)).2
  rw [tc_card_U] at h2
  have hsplit := Finset.sum_add_sum_compl (groupU a b) (fun k => completion (procTime a b) B k)
  have hj'le : completion (procTime a b) B j' ≤ ∑ k ∈ (groupU a b)ᶜ, completion (procTime a b) B k :=
    Finset.single_le_sum (f := fun k => completion (procTime a b) B k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_compl.2 hj')
  have hpj' := hpos j'
  have hy2 := tc_y2 a b
  simp only [completion] at hy hsplit hj'le
  nlinarith

theorem tc_claimB_core (B : Fin (numJobs a b) → ℕ)
    (hB : IsFeasible (procTime a b) (release a b) B)
    (hy : ∑ j, completion (procTime a b) B j ≤ yThreshold a b) :
    (∃ j ∈ groupU a b, B j ≤ sigma a b) ∧
      ∑ j ∈ (groupU a b)ᶜ, completion (procTime a b) B j ≤ uCount a b := by
  have hpos := tc_proc_pos a b
  have hd := hB.2
  have hy2 := tc_y2 a b
  have hups := tc_ups_eq a b
  have hsplit := Finset.sum_add_sum_compl (groupU a b) (fun k => completion (procTime a b) B k)
  have hlast : completion (procTime a b) B (lastJob a b) ≤ ∑ k ∈ (groupU a b)ᶜ, completion (procTime a b) B k :=
    Finset.single_le_sum (f := fun k => completion (procTime a b) B k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_compl.2 (tc_not_U_last a b))
  have hlast1 : 1 ≤ completion (procTime a b) B (lastJob a b) := by
    have := tc_proc_last a b
    simp only [completion]; omega
  have hA := tc_claimA_core a b B hB hy
  simp only [completion] at hy hsplit hlast hlast1
  refine ⟨?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    have h2 := (tc_chain (procTime a b) B hpos hd (sigma a b + 1) (upsilon a b) (groupU a b)
      (fun k hk => ⟨by have := hcon k (by simpa using hk); omega, (tc_proc_U a b k hk).ge⟩)).2
    rw [tc_card_U] at h2
    have hh : uCount a b * (sigma a b + 1) = upsilon a b := rfl
    nlinarith
  · have hσ : ∀ j ∈ groupU a b, sigma a b ≤ B j := by
      intro j hj
      have hlen := tc_len (procTime a b) B hpos hd 0 (groupU a b)ᶜ (B j) (Nat.zero_le _)
        (fun k hk => by
          have hk' : k ∉ groupU a b := Finset.mem_compl.1 hk
          have hlt := hA k j hk' hj
          have hne : k ≠ j := fun h => hk' (h ▸ hj)
          exact ⟨Nat.zero_le _, tc_lt_of_le _ _ hpos hd hne hlt.le⟩)
      rw [tc_sum_nonU] at hlen
      omega
    have h2 := (tc_chain (procTime a b) B hpos hd (sigma a b) (upsilon a b) (groupU a b)
      (fun k hk => ⟨hσ k hk, (tc_proc_U a b k hk).ge⟩)).2
    rw [tc_card_U] at h2
    simp only [completion]
    nlinarith

end spec
end SchedComplexity.TotalCompletion

open SchedComplexity.TotalCompletion


theorem solution {t : ℕ} (a : Fin t → ℕ) (b : ℕ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hbA : b < sumA a)
    (B : Fin (numJobs a b) → ℕ)
    (hB : IsFeasible (procTime a b) (release a b) B)
    (hy : ∑ j, completion (procTime a b) B j ≤ yThreshold a b) :
    (∃ j ∈ groupU a b, B j ≤ sigma a b) ∧
      ∑ j ∈ (groupU a b)ᶜ, completion (procTime a b) B j ≤ uCount a b := by
  exact tc_claimB_core a b B hB hy
