-- Prove2me | solution 1 for WorstCaseEq.Speeds.theorem4_two_speeds_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:54:55.749921+00:00
-- url     : https://prove2.me/submissions/a5f61e6e-920d-4b4c-a3a5-89f74f5c83ae

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Speeds_Model



namespace WorstCaseEq.Speeds

open Finset

lemma wce_E_prod {n m : ℕ} (p : Fin n → Fin m → ℝ) (h : Fin n → Fin m → ℝ) :
    ∑ a : Fin n → Fin m, AGT.profileProb p a * ∏ k, h k (a k) = ∏ k, ∑ j, p k j * h k j := by
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [AGT.profileProb, ← Finset.prod_mul_distrib]

lemma wce_E_coord {n m : ℕ} (p : Fin n → Fin m → ℝ) (i : Fin n)
    (hp : ∀ k, k ≠ i → ∑ j, p k j = 1) (f : Fin m → ℝ) :
    ∑ a : Fin n → Fin m, AGT.profileProb p a * f (a i) = ∑ j, p i j * f j := by
  have h1 := wce_E_prod p (fun k j => if k = i then f j else 1)
  have h2 : ∀ a : Fin n → Fin m, (∏ k, (fun k j => if k = i then f j else 1) k (a k)) = f (a i) := by
    intro a; simp
  simp only [h2] at h1
  rw [h1, Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [hb, hp b hb]
  · simp

lemma wce_E_pair {n m : ℕ} (p : Fin n → Fin m → ℝ) (i k : Fin n) (hk : k ≠ i)
    (hp : ∀ k, k ≠ i → ∑ j, p k j = 1) (g : Fin m → ℝ) :
    ∑ a : Fin n → Fin m, AGT.profileProb p a * (if a k = a i then g (a i) else 0)
      = ∑ j, p i j * p k j * g j := by
  set H : Fin m → Fin n → Fin m → ℝ := fun j k' j' =>
    (if k' = i then (if j' = j then g j else 0) else 1) *
      (if k' = k then (if j' = j then 1 else 0) else 1) with hH
  have hprod : ∀ (j : Fin m) (a : Fin n → Fin m), (∏ k', H j k' (a k')) =
      (if a i = j then g j else 0) * (if a k = j then 1 else 0) := by
    intro j a
    rw [hH]; simp only
    rw [Finset.prod_mul_distrib]
    simp
  have hsum : ∀ a : Fin n → Fin m, (if a k = a i then g (a i) else 0) = ∑ j, ∏ k', H j k' (a k') := by
    intro a
    simp only [hprod]
    rw [Finset.sum_eq_single (a i)]
    · by_cases h : a k = a i <;> simp [h]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  simp only [hsum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [wce_E_prod, Finset.prod_eq_mul i k (Ne.symm hk)]
  · rw [hH]; simp [Ne.symm hk, hk]; ring
  · intro c _ hc; rw [hH]; simp [hc.1, hc.2, hp c hc.1]
  · simp
  · simp


lemma wce_payoff_eq {n m : ℕ} (w : Fin n → ℝ) (s : Fin m → ℝ) (i : Fin n) (a : Fin n → Fin m) :
    payoff w s i a = -(w i / s (a i) +
      ∑ k ∈ Finset.univ.erase i, (if a k = a i then w k / s (a i) else 0)) := by
  unfold payoff WorstCaseEq.Identical.load
  rw [Finset.sum_filter, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [if_true, add_div, Finset.sum_div, ite_div, zero_div]

lemma wce_expPayoff {n m : ℕ} (w : Fin n → ℝ) (s : Fin m → ℝ) (q : Fin n → Fin m → ℝ) (i : Fin n)
    (hq : ∀ k, k ≠ i → ∑ j, q k j = 1) :
    AGT.expectedPayoff (payoff w s) q i = -∑ j, q i j * linkCost w s q i j := by
  unfold AGT.expectedPayoff
  simp only [wce_payoff_eq, mul_neg, mul_add, Finset.mul_sum, Finset.sum_neg_distrib,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm (t := Finset.univ.erase i)]
  have e1 := wce_E_coord q i hq (fun j => w i / s j)
  rw [e1]
  rw [Finset.sum_congr rfl (fun k hk => wce_E_pair q i k (Finset.ne_of_mem_erase hk) hq
    (fun j => w k / s j))]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold linkCost
  rw [add_div, Finset.sum_div, mul_add, Finset.mul_sum]
  refine congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun k _ => by ring)

lemma wce_linkCost_update {n m : ℕ} (w : Fin n → ℝ) (s : Fin m → ℝ) (p : Fin n → Fin m → ℝ)
    (i : Fin n) (τ : Fin m → ℝ) (j : Fin m) :
    linkCost w s (Function.update p i τ) i j = linkCost w s p i j := by
  unfold linkCost
  congr 2
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

/-- Nash characterization: for each agent `i`, the profile is Nash iff (with lotteries)
`∑ τ_j c_j ≥ ∑ p_j c_j` for all lotteries `τ`. -/
lemma wce_nash_iff {n m : ℕ} (w : Fin n → ℝ) (s : Fin m → ℝ) (p : Fin n → Fin m → ℝ)
    (hp : AGT.IsMixedProfile p) :
    IsNash w s p ↔ ∀ i (τ : Fin m → ℝ), AGT.IsLottery τ →
      ∑ j, p i j * linkCost w s p i j ≤ ∑ j, τ j * linkCost w s p i j := by
  unfold IsNash AGT.IsMixedNash
  have hq : ∀ i, ∀ k, k ≠ i → ∑ j, p k j = 1 := fun i k _ => (hp k).2
  constructor
  · rintro ⟨_, h⟩ i τ hτ
    have := h i τ hτ
    rw [wce_expPayoff w s _ i, wce_expPayoff w s _ i (hq i)] at this
    · simp only [Function.update_self, wce_linkCost_update] at this
      linarith
    · intro k hk; rw [Function.update_of_ne hk]; exact (hp k).2
  · intro h
    refine ⟨hp, fun i τ hτ => ?_⟩
    rw [wce_expPayoff w s _ i, wce_expPayoff w s _ i (hq i)]
    · simp only [Function.update_self, wce_linkCost_update]
      linarith [h i τ hτ]
    · intro k hk; rw [Function.update_of_ne hk]; exact (hp k).2


theorem nash_support_minimizes_core {n m : ℕ} [NeZero m] (w : Fin n → ℝ) (s : Fin m → ℝ)
    (p : Fin n → Fin m → ℝ) (hp : IsNash w s p) :
    (∀ i j, 0 < p i j → ∀ j', linkCost w s p i j ≤ linkCost w s p i j') ∧
      ∀ i, expCost w s p i = Finset.univ.inf' Finset.univ_nonempty (linkCost w s p i) := by
  have hprof : AGT.IsMixedProfile p := hp.1
  have hN := (wce_nash_iff w s p hprof).1 hp
  have hexp : ∀ i, expCost w s p i = ∑ j, p i j * linkCost w s p i j := by
    intro i
    unfold expCost
    rw [wce_expPayoff w s p i (fun k _ => (hprof k).2), neg_neg]
  -- the expected cost is at most every link cost
  have hle : ∀ i j', ∑ j, p i j * linkCost w s p i j ≤ linkCost w s p i j' := by
    intro i j'
    have := hN i (fun j => if j = j' then 1 else 0) ⟨fun a => by dsimp only; split_ifs <;> norm_num, by simp⟩
    simpa using this
  -- and at least the minimum
  have hge : ∀ i, Finset.univ.inf' Finset.univ_nonempty (linkCost w s p i) ≤
      ∑ j, p i j * linkCost w s p i j := by
    intro i
    set μ := Finset.univ.inf' Finset.univ_nonempty (linkCost w s p i)
    calc μ = ∑ j, p i j * μ := by rw [← Finset.sum_mul, (hprof i).2, one_mul]
      _ ≤ ∑ j, p i j * linkCost w s p i j := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ j)) ((hprof i).1 j)
  have heq : ∀ i, ∑ j, p i j * linkCost w s p i j =
      Finset.univ.inf' Finset.univ_nonempty (linkCost w s p i) := by
    intro i
    refine le_antisymm ?_ (hge i)
    obtain ⟨j0, _, hj0⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin m))
      (linkCost w s p i)
    rw [hj0]; exact hle i j0
  refine ⟨fun i j hj j' => ?_, fun i => by rw [hexp, heq]⟩
  set μ := Finset.univ.inf' Finset.univ_nonempty (linkCost w s p i) with hμ
  have hsum : ∑ k, p i k * (linkCost w s p i k - μ) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (hprof i).2, one_mul]
    rw [heq i]; ring
  have hterm : p i j * (linkCost w s p i j - μ) ≤ ∑ k, p i k * (linkCost w s p i k - μ) := by
    refine Finset.single_le_sum (f := fun k => p i k * (linkCost w s p i k - μ))
      (fun k _ => mul_nonneg ((hprof i).1 k) (sub_nonneg.2 (Finset.inf'_le _ (Finset.mem_univ k))))
      (Finset.mem_univ j)
  rw [hsum] at hterm
  have h1 : linkCost w s p i j - μ ≤ 0 := by
    by_contra hc; rw [not_le] at hc; linarith [mul_pos hj hc]
  have h2 : μ ≤ linkCost w s p i j' := Finset.inf'_le _ (Finset.mem_univ j')
  linarith

lemma wce_sup2 (f : Fin 2 → ℝ) : Finset.univ.sup' Finset.univ_nonempty f = max (f 0) (f 1) := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun j _ => ?_
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (Finset.le_sup' f (Finset.mem_univ 0)) (Finset.le_sup' f (Finset.mem_univ 1))

lemma wce_sum_fun2 (F : (Fin 2 → Fin 2) → ℝ) :
    ∑ a : Fin 2 → Fin 2, F a = F ![0, 0] + F ![0, 1] + (F ![1, 0] + F ![1, 1]) := by
  rw [← Equiv.sum_comp (finTwoArrowEquiv (Fin 2)).symm, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [finTwoArrowEquiv_symm_apply]

lemma wce_ratio_le (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂)
    (hφ : s₂ ≤ Real.goldenRatio * s₁) :
    1 + s₂ / (s₁ + s₂) ≤ Real.goldenRatio ∧
      (s₂ = Real.goldenRatio * s₁ → 1 + s₂ / (s₁ + s₂) = Real.goldenRatio) := by
  have hg := Real.goldenRatio_sq
  have hg1 := Real.one_lt_goldenRatio
  have hg2 := Real.goldenRatio_lt_two
  have hpos : 0 < s₁ + s₂ := by linarith
  constructor
  · have : s₂ / (s₁ + s₂) ≤ Real.goldenRatio - 1 := by
      rw [div_le_iff₀ hpos]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 - Real.goldenRatio)
        (by linarith : (0:ℝ) ≤ Real.goldenRatio * s₁ - s₂)]
    linarith
  · intro h
    have : s₂ / (s₁ + s₂) = Real.goldenRatio - 1 := by
      rw [div_eq_iff hpos.ne', h]
      linear_combination (-s₁) * hg
    linarith

theorem theorem4_core (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂)
    (hφ : s₂ ≤ Real.goldenRatio * s₁) :
    (∃ (n : ℕ) (w : Fin n → ℝ) (p : Fin n → Fin 2 → ℝ),
        (∀ i, 0 < w i) ∧ IsNash w ![s₁, s₂] p ∧ 0 < opt w ![s₁, s₂] ∧
          socialCost w ![s₁, s₂] p = (1 + s₂ / (s₁ + s₂)) * opt w ![s₁, s₂]) ∧
      1 + s₂ / (s₁ + s₂) ≤ Real.goldenRatio ∧
      (s₂ = Real.goldenRatio * s₁ → 1 + s₂ / (s₁ + s₂) = Real.goldenRatio) := by
  refine ⟨?_, wce_ratio_le s₁ s₂ h₁ h₁₂ hφ⟩
  have h₂ : 0 < s₂ := by linarith
  have hpos : 0 < s₁ + s₂ := by linarith
  have hg := Real.goldenRatio_sq
  have hg1 := Real.one_lt_goldenRatio
  -- the key inequality s₂² ≤ s₁ (s₁ + s₂)
  have hkey : s₂ ^ 2 ≤ s₁ * (s₁ + s₂) := by
    have e : s₁ * (s₁ + s₂) - s₂ ^ 2 =
        (Real.goldenRatio * s₁ - s₂) * (s₂ + (Real.goldenRatio - 1) * s₁) := by
      linear_combination (-(s₁ ^ 2)) * hg
    have : 0 ≤ (Real.goldenRatio * s₁ - s₂) * (s₂ + (Real.goldenRatio - 1) * s₁) :=
      mul_nonneg (by linarith) (by nlinarith)
    linarith
  set W : Fin 2 → ℝ := ![s₂, s₁] with hW
  set P : Fin 2 → Fin 2 → ℝ :=
    ![![s₁ ^ 2 / (s₂ * (s₁ + s₂)), 1 - s₁ ^ 2 / (s₂ * (s₁ + s₂))],
      ![1 - s₂ ^ 2 / (s₁ * (s₁ + s₂)), s₂ ^ 2 / (s₁ * (s₁ + s₂))]] with hP
  have hp00 : 0 ≤ s₁ ^ 2 / (s₂ * (s₁ + s₂)) := by positivity
  have hp00' : s₁ ^ 2 / (s₂ * (s₁ + s₂)) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hp11 : 0 ≤ s₂ ^ 2 / (s₁ * (s₁ + s₂)) := by positivity
  have hp11' : s₂ ^ 2 / (s₁ * (s₁ + s₂)) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hkey
  have hprof : AGT.IsMixedProfile P := by
    intro i
    fin_cases i
    · refine ⟨fun j => ?_, ?_⟩
      · fin_cases j <;> simp [hP] <;> linarith
      · simp [hP]
    · refine ⟨fun j => ?_, ?_⟩
      · fin_cases j <;> simp [hP] <;> linarith
      · simp [hP]
  set C : Fin 2 → ℝ := ![(s₁ + 2 * s₂) / (s₁ + s₂), (2 * s₁ + s₂) / (s₁ + s₂)] with hC
  have hlc : ∀ i j, linkCost W ![s₁, s₂] P i j = C i := by
    intro i j
    unfold linkCost
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [hW, hP, hC] <;> field_simp <;> ring
  have hnash : IsNash W ![s₁, s₂] P := by
    rw [wce_nash_iff _ _ _ hprof]
    intro i τ hτ
    simp only [hlc, ← Finset.sum_mul, hτ.2, (hprof i).2]
    exact le_rfl
  -- makespans of the four pure profiles
  have hM00 : makespan W ![s₁, s₂] ![0, 0] = (s₂ + s₁) / s₁ := by
    simp [makespan, wce_sup2, WorstCaseEq.Identical.load, Finset.sum_filter, Fin.sum_univ_two, hW]
    positivity
  have hM11 : makespan W ![s₁, s₂] ![1, 1] = (s₂ + s₁) / s₂ := by
    simp [makespan, wce_sup2, WorstCaseEq.Identical.load, Finset.sum_filter, Fin.sum_univ_two, hW]
    positivity
  have hM01 : makespan W ![s₁, s₂] ![0, 1] = s₂ / s₁ := by
    simp [makespan, wce_sup2, WorstCaseEq.Identical.load, Finset.sum_filter, Fin.sum_univ_two, hW]
    rw [div_le_div_iff₀ h₂ h₁]; nlinarith
  have hM10 : makespan W ![s₁, s₂] ![1, 0] = 1 := by
    simp [makespan, wce_sup2, WorstCaseEq.Identical.load, Finset.sum_filter, Fin.sum_univ_two, hW,
      h₁.ne', h₂.ne']
  have hopt : opt W ![s₁, s₂] = 1 := by
    apply le_antisymm
    · rw [← hM10]; exact Finset.inf'_le _ (Finset.mem_univ _)
    · refine Finset.le_inf' _ _ fun a _ => ?_
      have ha : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
      rw [ha]
      generalize a 0 = x
      generalize a 1 = y
      fin_cases x <;> fin_cases y
      · simp only [Fin.zero_eta, Fin.isValue]; rw [hM00, le_div_iff₀ h₁]; linarith
      · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]; rw [hM01, le_div_iff₀ h₁]; linarith
      · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]; rw [hM10]
      · simp only [Fin.mk_one, Fin.isValue]; rw [hM11, le_div_iff₀ h₂]; linarith
  refine ⟨2, W, P, ?_, hnash, by rw [hopt]; norm_num, ?_⟩
  · intro i; fin_cases i <;> simp [hW] <;> linarith
  · rw [hopt, mul_one]
    unfold socialCost
    rw [wce_sum_fun2]
    simp only [hM00, hM01, hM10, hM11]
    simp [AGT.profileProb, Fin.prod_univ_two, hP]
    field_simp
    ring

end WorstCaseEq.Speeds

open WorstCaseEq.Speeds


theorem solution (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂)
    (hφ : s₂ ≤ Real.goldenRatio * s₁) :
    (∃ (n : ℕ) (w : Fin n → ℝ) (p : Fin n → Fin 2 → ℝ),
        (∀ i, 0 < w i) ∧ IsNash w ![s₁, s₂] p ∧ 0 < opt w ![s₁, s₂] ∧
          socialCost w ![s₁, s₂] p = (1 + s₂ / (s₁ + s₂)) * opt w ![s₁, s₂]) ∧
      1 + s₂ / (s₁ + s₂) ≤ Real.goldenRatio ∧
      (s₂ = Real.goldenRatio * s₁ → 1 + s₂ / (s₁ + s₂) = Real.goldenRatio) := by
  exact theorem4_core s₁ s₂ h₁ h₁₂ hφ
