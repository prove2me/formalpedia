-- Prove2me | solution 1 for ReusableMatching.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T14:43:05.061224+00:00
-- url     : https://prove2.me/submissions/3c079776-1fa2-4100-af8a-969b876486b8

import Mathlib
import Definitions.Def_ReusableMatching_ThreeRegimes
import Definitions.Def_ReusableMatching_criticalThreshold

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ReusableMatching
namespace L8Aux

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

/-! ### `leastArgmax` -/

theorem leastArgmax_some {C : Finset V} {f : V → ℝ} {a : V} :
    leastArgmax C f = some a ↔
      a ∈ C ∧ (∀ v ∈ C, f v ≤ f a) ∧ (∀ v ∈ C, f v = f a → a ≤ v) := by
  classical
  unfold leastArgmax
  split_ifs with h
  · constructor
    · intro hs
      simp only [Option.some.injEq] at hs
      subst hs
      have hm := Finset.min'_mem (C.filter (fun v => f v = C.sup' h f)) (by
          obtain ⟨v, hv, hvM⟩ := Finset.exists_mem_eq_sup' h f
          exact ⟨v, Finset.mem_filter.2 ⟨hv, hvM.symm⟩⟩)
      rw [Finset.mem_filter] at hm
      refine ⟨hm.1, fun v hv => ?_, fun v hv hfv => ?_⟩
      · rw [hm.2]; exact Finset.le_sup' f hv
      · apply Finset.min'_le
        rw [Finset.mem_filter]; exact ⟨hv, hfv.trans hm.2⟩
    · rintro ⟨haC, hmax, hleast⟩
      have hsup : C.sup' h f = f a :=
        le_antisymm (Finset.sup'_le h f hmax) (Finset.le_sup' f haC)
      congr 1
      apply le_antisymm
      · apply Finset.min'_le; rw [Finset.mem_filter]; exact ⟨haC, hsup.symm⟩
      · apply Finset.le_min'; intro w hw; rw [Finset.mem_filter] at hw
        exact hleast w hw.1 (hw.2.trans hsup)
  · simp only [reduceCtorEq, false_iff]
    rintro ⟨haC, -, -⟩; exact h ⟨a, haC⟩

theorem leastArgmax_none {C : Finset V} {f : V → ℝ} :
    leastArgmax C f = none ↔ C = ∅ := by
  classical
  unfold leastArgmax
  split_ifs with h
  · simp only [reduceCtorEq, false_iff]; exact h.ne_empty
  · simp only [true_iff]; exact Finset.not_nonempty_iff_eq_empty.1 h

theorem leastArgmax_lower {C : Finset V} {f f' : V → ℝ} {i : V}
    (hoff : ∀ v, v ≠ i → f' v = f v) (hi : f' i ≤ f i) (hne : leastArgmax C f ≠ some i) :
    leastArgmax C f' = leastArgmax C f := by
  rcases h : leastArgmax C f with _ | a
  · rw [leastArgmax_none] at h ⊢; exact h
  · rw [h] at hne
    have hai : a ≠ i := fun e => hne (e ▸ rfl)
    obtain ⟨haC, hmax, hleast⟩ := leastArgmax_some.1 h
    rw [leastArgmax_some]
    have hfa : f' a = f a := hoff a hai
    have hle : ∀ v ∈ C, f' v ≤ f v := fun v _ => by
      by_cases hv : v = i
      · subst hv; exact hi
      · exact (hoff v hv).le
    refine ⟨haC, fun v hv => ?_, fun v hv hfv => hleast v hv ?_⟩
    · rw [hfa]; exact (hle v hv).trans (hmax v hv)
    · have := hle v hv; have := hmax v hv
      linarith

theorem leastArgmax_congr {C : Finset V} {f f' : V → ℝ} (h : ∀ v ∈ C, f v = f' v) :
    leastArgmax C f = leastArgmax C f' := by
  rcases h1 : leastArgmax C f' with _ | a
  · rw [leastArgmax_none] at h1 ⊢; exact h1
  · obtain ⟨haC, hmax, hleast⟩ := leastArgmax_some.1 h1
    rw [leastArgmax_some]
    refine ⟨haC, fun v hv => ?_, fun v hv hfv => hleast v hv ?_⟩
    · rw [h v hv, h a haC]; exact hmax v hv
    · rw [← h v hv, ← h a haC]; exact hfv

theorem step_abs {CA CB : Finset V} {f : V → ℝ} {x : V}
    (hBA : ∀ v ∈ CB, 0 < f v → v ∈ CA) (hAB : ∀ v ∈ CA, 0 < f v → v ∈ CB ∨ v = x) :
    (∀ a, leastArgmax CA f = some a → 0 < f a →
        leastArgmax CB f = some a ∨ (a = x ∧ a ∉ CB)) ∧
    (∀ b, leastArgmax CB f = some b → 0 < f b →
        leastArgmax CA f = some b ∨ (leastArgmax CA f = some x ∧ x ∉ CB)) := by
  have h1 : ∀ a, leastArgmax CA f = some a → 0 < f a →
      leastArgmax CB f = some a ∨ (a = x ∧ a ∉ CB) := by
    intro a ha hpa
    obtain ⟨haC, hmax, hleast⟩ := leastArgmax_some.1 ha
    by_cases haB : a ∈ CB
    · left
      rw [leastArgmax_some]
      refine ⟨haB, fun v hv => ?_, fun v hv hfv => hleast v (hBA v hv (hfv ▸ hpa)) hfv⟩
      by_cases hpv : 0 < f v
      · exact hmax v (hBA v hv hpv)
      · linarith
    · right
      rcases hAB a haC hpa with h | h
      · exact absurd h haB
      · exact ⟨h, haB⟩
  refine ⟨h1, fun b hb hpb => ?_⟩
  obtain ⟨hbC, -, -⟩ := leastArgmax_some.1 hb
  have hbA := hBA b hbC hpb
  rcases ha : leastArgmax CA f with _ | a
  · rw [leastArgmax_none] at ha; rw [ha] at hbA; simp at hbA
  · obtain ⟨-, hmax, -⟩ := leastArgmax_some.1 ha
    have hpa : 0 < f a := lt_of_lt_of_le hpb (hmax b hbA)
    rcases h1 a ha hpa with h | ⟨hax, haB⟩
    · rw [hb] at h; left; exact h.symm ▸ rfl
    · right; subst hax; exact ⟨rfl, haB⟩

/-! ### Runs of Periodic Reranking -/

variable (I : OBMRRInstance V n) (β : ℝ)

theorem asg_succ (Y : Seeds V n) (m u : ℕ) :
    assignment I β Y (m + 1) u =
      if u = m then (if h : m < n then chooseResource I β Y (assignment I β Y m) ⟨m, h⟩
        else none) else assignment I β Y m u := by
  rw [assignment, Function.update_apply]

theorem asg_stable (Y : Seeds V n) (u : ℕ) :
    ∀ m, u < m → assignment I β Y m u = assignment I β Y (u + 1) u := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | h
    · rw [asg_succ, if_neg (by omega), ih h]
    · subst h; rfl

theorem asg_ge (Y : Seeds V n) (u : ℕ) : ∀ m, m ≤ u → assignment I β Y m u = none := by
  intro m hm
  induction m with
  | zero => rfl
  | succ m ih => rw [asg_succ, if_neg (by omega), ih (by omega)]

theorem avail_full (Y : Seeds V n) (t : ℕ) (ht : t ≤ n) (v : V) :
    IsAvailable I (assignment I β Y t) v t ↔ IsAvailable I (assignment I β Y n) v t := by
  have key : ∀ s, s < t → assignment I β Y t s = assignment I β Y n s := by
    intro s hs
    rw [asg_stable I β Y s t hs, asg_stable I β Y s n (by omega)]
  unfold IsAvailable
  constructor
  · intro H s hs; rw [← key s hs]; exact H s hs
  · intro H s hs; rw [key s hs]; exact H s hs

theorem run_spec (Y : Seeds V n) (t : ℕ) (ht : t < n) :
    ∃ C : Finset V, (∀ v, v ∈ C ↔ (v, (⟨t, ht⟩ : Fin n)) ∈ I.E ∧
        IsAvailable I (assignment I β Y n) v t) ∧
      assignment I β Y n t = leastArgmax C (fun v => reducedPrice I β Y v ⟨t, ht⟩) := by
  classical
  refine ⟨Finset.univ.filter (fun v => (v, (⟨t, ht⟩ : Fin n)) ∈ I.E ∧
        IsAvailable I (assignment I β Y n) v t), fun v => by simp, ?_⟩
  rw [asg_stable I β Y t n ht, asg_succ, if_pos rfl, dif_pos ht]
  unfold chooseResource
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [avail_full I β Y t ht.le]

theorem chosen_avail (Y : Seeds V n) (t : ℕ) (ht : t < n) (v : V)
    (h : assignment I β Y n t = some v) :
    IsAvailable I (assignment I β Y n) v t ∧ (v, (⟨t, ht⟩ : Fin n)) ∈ I.E := by
  obtain ⟨C, hC, hrun⟩ := run_spec I β Y t ht
  rw [hrun] at h
  have := ((hC v).1 (leastArgmax_some.1 h).1)
  exact ⟨this.2, this.1⟩

theorem mem_availableSet (Y : Seeds V n) (t : Fin n) (v : V) :
    v ∈ availableSet I β Y t ↔ IsAvailable I (assignment I β Y n) v t := by
  rw [← avail_full I β Y t t.2.le]
  simp [availableSet]

/-! ### Seeds and prices -/

theorem period_ne_prev (j : Fin n) : period I j ≠ prevPeriod I j := by
  intro h
  have := congrArg Fin.val h
  simp [period, prevPeriod] at this

theorem ts_ne (Y : Seeds V n) (i : V) (j : Fin n) (y1 y1' y2 : unitInterval) (v : V)
    (p : Fin (n + 1)) (h : (v, p) ≠ (i, prevPeriod I j)) :
    twoSeed I Y i j y1 y2 (v, p) = twoSeed I Y i j y1' y2 (v, p) := by
  simp only [twoSeed, Function.update_apply]
  split_ifs <;> simp_all

theorem ts_period (Y : Seeds V n) (i : V) (j : Fin n) (y1 y2 : unitInterval) :
    twoSeed I Y i j y1 y2 (i, period I j) = y2 := by
  simp [twoSeed]

theorem ts_prev (Y : Seeds V n) (i : V) (j : Fin n) (y1 y2 : unitInterval) :
    twoSeed I Y i j y1 y2 (i, prevPeriod I j) = y1 := by
  have := (period_ne_prev I j).symm
  simp [twoSeed, Function.update_apply, this]

theorem ts_other (Y : Seeds V n) (i : V) (j : Fin n) (y1 y2 : unitInterval) (v : V)
    (hv : v ≠ i) (p : Fin (n + 1)) : twoSeed I Y i j y1 y2 (v, p) = Y (v, p) := by
  simp [twoSeed, Function.update_apply, hv]

theorem price_off (Y : Seeds V n) (i : V) (j : Fin n) (y1 y1' y2 : unitInterval) (v : V)
    (t : Fin n) (h : v ≠ i ∨ period I t ≠ prevPeriod I j) :
    reducedPrice I β (twoSeed I Y i j y1 y2) v t = reducedPrice I β (twoSeed I Y i j y1' y2) v t := by
  unfold reducedPrice
  rw [ts_ne I Y i j y1 y1' y2 v (period I t)]
  intro e
  simp only [Prod.mk.injEq] at e
  rcases h with h | h
  · exact h e.1
  · exact h e.2

theorem g_one : g β 1 = 1 := by simp [g]

theorem price_nonneg (hβ : 0 < β) (Y : Seeds V n) (v : V) (t : Fin n) :
    0 ≤ reducedPrice I β Y v t := by
  unfold reducedPrice g
  apply mul_nonneg (I.r_nonneg v)
  rw [sub_nonneg, Real.exp_le_one_iff]
  have := (Y (v, period I t)).2.2
  nlinarith

theorem price_pos_r (Y : Seeds V n) (v : V) (t : Fin n)
    (h : 0 < reducedPrice I β Y v t) : 0 < I.r v := by
  unfold reducedPrice at h
  rcases (I.r_nonneg v).lt_or_eq with h' | h'
  · exact h'
  · rw [← h', zero_mul] at h; exact absurd h (lt_irrefl 0)

theorem price_pos_of (hβ : 0 < β) (Y : Seeds V n) (v : V) (t : Fin n) (hr : 0 < I.r v)
    (hy : (Y (v, period I t) : ℝ) < 1) : 0 < reducedPrice I β Y v t := by
  unfold reducedPrice g
  apply mul_pos hr
  rw [sub_pos]
  have h0 : β * ((Y (v, period I t) : ℝ) - 1) < 0 := by nlinarith
  exact (Real.exp_lt_exp.2 h0).trans_eq Real.exp_zero

/-! ### The critical threshold -/

theorem sSup_anti {M M' : ℝ} (c : ℝ → ℝ) (hM : M' ≤ M) :
    sSup {y : ℝ | y ∈ Set.Icc (0 : ℝ) 1 ∧ M ≤ c y} ≤
      sSup {y : ℝ | y ∈ Set.Icc (0 : ℝ) 1 ∧ M' ≤ c y} := by
  rcases Set.eq_empty_or_nonempty {y : ℝ | y ∈ Set.Icc (0 : ℝ) 1 ∧ M ≤ c y} with h | h
  · rw [h, Real.sSup_empty]; exact Real.sSup_nonneg (fun y hy => hy.1.1)
  · apply csSup_le_csSup ⟨1, fun y hy => hy.1.2⟩ h
    intro y hy; exact ⟨hy.1, hM.trans hy.2⟩

theorem dite_sup_le {C C' : Finset V} [Decidable C.Nonempty] [Decidable C'.Nonempty]
    {f f' : V → ℝ} (hf : ∀ v ∈ C, 0 ≤ f v)
    (h : ∀ v ∈ C', f' v ≤ 0 ∨ ∃ w ∈ C, f' v ≤ f w) :
    (if h' : C'.Nonempty then C'.sup' h' f' else 0) ≤
      (if h : C.Nonempty then C.sup' h f else 0) := by
  have h0 : 0 ≤ (if h : C.Nonempty then C.sup' h f else 0) := by
    by_cases hC : C.Nonempty
    · rw [dif_pos hC]
      obtain ⟨w, hw⟩ := hC; exact (hf w hw).trans (Finset.le_sup' f hw)
    · rw [dif_neg hC]
  by_cases hC' : C'.Nonempty
  · rw [dif_pos hC']
    apply Finset.sup'_le; intro v hv
    rcases h v hv with h1 | ⟨w, hw, h2⟩
    · exact h1.trans h0
    · refine h2.trans ?_
      rw [dif_pos ⟨w, hw⟩]; exact Finset.le_sup' f hw
  · rw [dif_neg hC']; exact h0

theorem ct_le (hβ : 0 < β) (Y : Seeds V n) (i : V) (j : Fin n) (y1 y1' : unitInterval)
    (h : ∀ v, IsAvailable I (assignment I β (twoSeed I Y i j y1' 1) n) v j → (v, j) ∈ I.E →
      reducedPrice I β (twoSeed I Y i j y1' 1) v j ≤ 0 ∨
      ∃ w, IsAvailable I (assignment I β (twoSeed I Y i j y1 1) n) w j ∧ (w, j) ∈ I.E ∧
        reducedPrice I β (twoSeed I Y i j y1' 1) v j ≤ reducedPrice I β (twoSeed I Y i j y1 1) w j) :
    criticalThreshold I β Y i j y1 j ≤ criticalThreshold I β Y i j y1' j := by
  unfold criticalThreshold
  dsimp only
  apply sSup_anti (fun y => I.r i * (1 - g β y))
  apply dite_sup_le
  · intro v _; exact price_nonneg I β hβ _ v j
  · intro v hv
    rw [Finset.mem_filter, mem_availableSet] at hv
    rcases h v hv.1 hv.2 with h1 | ⟨w, hw1, hw2, hw3⟩
    · exact Or.inl h1
    · refine Or.inr ⟨w, ?_, hw3⟩
      rw [Finset.mem_filter, mem_availableSet]; exact ⟨hw1, hw2⟩

/-! ### Common history -/

theorem same_hist (hβ : 0 < β) (Y : Seeds V n) (i : V) (j : Fin n) (y1 : unitInterval) (T : ℕ)
    (hT : ∀ t (ht : t < n), t < T → period I ⟨t, ht⟩ = prevPeriod I j →
       assignment I β (twoSeed I Y i j y1 1) n t ≠ some i) :
    ∀ t, t < T → assignment I β (twoSeed I Y i j y1 1) n t =
      assignment I β (twoSeed I Y i j 1 1) n t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro htT
  by_cases ht : t < n
  · obtain ⟨CA, hCA, hA⟩ := run_spec I β (twoSeed I Y i j y1 1) t ht
    obtain ⟨CB, hCB, hB⟩ := run_spec I β (twoSeed I Y i j 1 1) t ht
    have hC : CA = CB := by
      ext v
      rw [hCA, hCB]
      apply and_congr_right; intro _
      unfold IsAvailable
      constructor
      · intro H u hu; rw [← ih u hu (by omega)]; exact H u hu
      · intro H u hu; rw [ih u hu (by omega)]; exact H u hu
    rw [hA, hB, ← hC]
    by_cases hp : period I ⟨t, ht⟩ = prevPeriod I j
    · symm
      apply leastArgmax_lower (i := i)
      · intro v hv; exact price_off I β Y i j 1 y1 1 v _ (Or.inl hv)
      · have h0 := price_nonneg I β hβ (twoSeed I Y i j y1 1) i ⟨t, ht⟩
        unfold reducedPrice at h0 ⊢
        rw [hp, ts_prev] at h0
        rw [hp, ts_prev, ts_prev]
        simpa [g_one] using h0
      · rw [← hA]; exact hT t ht htT hp
    · apply leastArgmax_congr
      intro v _; exact price_off I β Y i j y1 1 1 v _ (Or.inr hp)
  · rw [asg_ge I β _ t n (by omega), asg_ge I β _ t n (by omega)]

theorem part_a (hβ : 0 < β) (Y : Seeds V n) (i : V) (j : Fin n) (y1 : unitInterval)
    (hY : ∀ t : Fin n, period I t = prevPeriod I j →
      PeriodicReranking I β (twoSeed I Y i j y1 1) t ≠ some i) :
    criticalThreshold I β Y i j y1 j = criticalThreshold I β Y i j 1 j := by
  have hjn : (j : ℕ) < n := j.2
  have hs := same_hist I β hβ Y i j y1 n (fun t ht _ hp => hY ⟨t, ht⟩ hp)
  have hav : ∀ v, IsAvailable I (assignment I β (twoSeed I Y i j y1 1) n) v j ↔
      IsAvailable I (assignment I β (twoSeed I Y i j 1 1) n) v j := by
    intro v; unfold IsAvailable
    constructor
    · intro H u hu; rw [← hs u (by omega)]; exact H u hu
    · intro H u hu; rw [hs u (by omega)]; exact H u hu
  have hpr : ∀ v, reducedPrice I β (twoSeed I Y i j y1 1) v j =
      reducedPrice I β (twoSeed I Y i j 1 1) v j :=
    fun v => price_off I β Y i j y1 1 1 v j (Or.inr (period_ne_prev I j))
  apply le_antisymm
  · apply ct_le I β hβ
    intro v hv hE; right; exact ⟨v, (hav v).2 hv, hE, (hpr v).symm.le⟩
  · apply ct_le I β hβ
    intro v hv hE; right; exact ⟨v, (hav v).1 hv, hE, (hpr v).le⟩

theorem part_b (hβ : 0 < β) (Y : Seeds V n) (i : V) (j : Fin n) (y1 : unitInterval)
    (hY : ∀ v : V, v ≠ i → (Y (v, prevPeriod I j) : ℝ) < 1)
    (hnot : i ∉ availableInSubperiod I β (twoSeed I Y i j y1 1) j) :
    criticalThreshold I β Y i j y1 j ≤ criticalThreshold I β Y i j 1 j := by
  set YA := twoSeed I Y i j y1 1 with hYA
  set YB := twoSeed I Y i j 1 1 with hYB
  set hA := assignment I β YA n with hhA
  set hB := assignment I β YB n with hhB
  have hd : 1 ≤ I.d := I.one_le_d
  have hjn : (j : ℕ) < n := j.2
  have hjav : ¬ IsAvailable I hA i j := by
    intro h; apply hnot
    simp only [availableInSubperiod, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨j, rfl, le_rfl, (mem_availableSet I β YA j i).2 h⟩
  obtain ⟨s, hsj, hAs, hjs⟩ : ∃ s, s < (j : ℕ) ∧ hA s = some i ∧ (j : ℕ) < s + I.d := by
    unfold IsAvailable at hjav; push Not at hjav; exact hjav
  have hsn : s < n := by omega
  have hsav := (chosen_avail I β YA s hsn i hAs).1
  have hdiv1 : s / I.d ≤ (j : ℕ) / I.d := Nat.div_le_div_right hsj.le
  have hdiv2 : (j : ℕ) / I.d ≤ s / I.d + 1 := by
    rw [← Nat.add_div_right s (by omega : 0 < I.d)]; exact Nat.div_le_div_right hjs.le
  have hsd : s / I.d + 1 = (j : ℕ) / I.d := by
    by_contra hne
    have heq : (j : ℕ) / I.d = s / I.d := by omega
    apply hnot
    simp only [availableInSubperiod, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨s, hsn⟩, ?_, ?_, (mem_availableSet I β YA _ i).2 hsav⟩
    · ext; simp [period, heq]
    · exact Fin.le_iff_val_le_val.2 hsj.le
  have hper : ∀ t (ht : t < n), s ≤ t → t ≤ (j : ℕ) →
      period I ⟨t, ht⟩ = prevPeriod I j ∨ period I ⟨t, ht⟩ = period I j := by
    intro t ht h1 h2
    have := Nat.div_le_div_right (c := I.d) h1
    have := Nat.div_le_div_right (c := I.d) h2
    rcases (show t / I.d = s / I.d ∨ t / I.d = (j : ℕ) / I.d by omega) with h | h
    · left; ext; simp [period, prevPeriod]; omega
    · right; ext; simp [period, h]
  have hpi : ∀ t (ht : t < n), s ≤ t → t ≤ (j : ℕ) → reducedPrice I β YB i ⟨t, ht⟩ = 0 := by
    intro t ht h1 h2
    unfold reducedPrice
    rcases hper t ht h1 h2 with h | h <;> rw [h] <;> simp [hYB, ts_prev, ts_period, g_one]
  have hmono : ∀ v t (ht : t + 1 < n), s ≤ t → t + 1 ≤ (j : ℕ) →
      0 < reducedPrice I β YB v ⟨t + 1, ht⟩ → 0 < reducedPrice I β YB v ⟨t, by omega⟩ := by
    intro v t ht h1 h2 hpos
    by_cases hv : v = i
    · rw [hv, hpi (t + 1) ht (by omega) h2] at hpos; exact absurd hpos (lt_irrefl 0)
    · have hr := price_pos_r I β YB v _ hpos
      rcases hper t (by omega) h1 (by omega) with h | h
      · apply price_pos_of I β hβ YB v _ hr
        rw [h, hYB, ts_other I Y i j 1 1 v hv]; exact hY v hv
      · have h' : period I ⟨t + 1, ht⟩ = period I j := by
          rcases hper (t + 1) ht (by omega) h2 with h'' | h''
          · exfalso
            have e1 := congrArg Fin.val h
            have e2 := congrArg Fin.val h''
            simp only [period, prevPeriod] at e1 e2
            have := Nat.div_le_div_right (c := I.d) (Nat.le_add_right t 1)
            omega
          · exact h''
        unfold reducedPrice at hpos ⊢; rw [h', ← h] at hpos; exact hpos
  have hsame := same_hist I β hβ Y i j y1 s (by
    intro t ht hts hp hAt
    have h1 := hsav t hts hAt
    have e := congrArg Fin.val hp
    simp only [period, prevPeriod] at e
    have h2 := Nat.lt_div_mul_add (a := s) (show 0 < I.d by omega)
    have h3 := Nat.div_mul_le_self t I.d
    have h4 : t / I.d = s / I.d := by omega
    rw [h4] at h3
    generalize s / I.d * I.d = m at h2 h3
    omega)
  replace hsame : ∀ u < s, hA u = hB u := hsame
  let R : V → ℕ → Prop := fun v t => ∀ u, u < s → hA u = some v → u + I.d ≤ t
  let UA : ℕ → V → Prop := fun t v => ∃ u, s ≤ u ∧ u < t ∧ hA u = some v
  let UB : ℕ → V → Prop := fun t v => ∃ u, s ≤ u ∧ u < t ∧ hB u = some v
  have havA : ∀ t, s < t → t ≤ (j : ℕ) → ∀ v, IsAvailable I hA v t ↔ R v t ∧ ¬ UA t v := by
    intro t h1 h2 v
    constructor
    · intro H
      refine ⟨fun u hu hAu => H u (by omega) hAu, ?_⟩
      rintro ⟨u, hsu, hut, hAu⟩
      have := H u hut hAu; omega
    · rintro ⟨hR, hU⟩ u hut hAu
      by_cases hus : u < s
      · exact hR u hus hAu
      · exact absurd ⟨u, by omega, hut, hAu⟩ hU
  have havB : ∀ t, s < t → t ≤ (j : ℕ) → ∀ v, IsAvailable I hB v t ↔ R v t ∧ ¬ UB t v := by
    intro t h1 h2 v
    constructor
    · intro H
      refine ⟨fun u hu hAu => H u (by omega) (by rw [← hsame u hu]; exact hAu), ?_⟩
      rintro ⟨u, hsu, hut, hBu⟩
      have := H u hut hBu; omega
    · rintro ⟨hR, hU⟩ u hut hBu
      by_cases hus : u < s
      · exact hR u hus (by rw [hsame u hus]; exact hBu)
      · exact absurd ⟨u, by omega, hut, hBu⟩ hU
  have hUs : ∀ (h : ℕ → Option V) t v, s ≤ t →
      ((∃ u, s ≤ u ∧ u < t + 1 ∧ h u = some v) ↔
        (∃ u, s ≤ u ∧ u < t ∧ h u = some v) ∨ h t = some v) := by
    intro h t v hst
    constructor
    · rintro ⟨u, h1, h2, h3⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | h2
      · exact Or.inl ⟨u, h1, h2, h3⟩
      · rw [h2] at h3; exact Or.inr h3
    · rintro (⟨u, h1, h2, h3⟩ | h3)
      · exact ⟨u, h1, by omega, h3⟩
      · exact ⟨t, hst, by omega, h3⟩
  have hinv : ∀ t, s + 1 ≤ t → t ≤ (j : ℕ) →
      (∀ v (ht : t < n), 0 < reducedPrice I β YB v ⟨t, ht⟩ → UA t v → UB t v) ∧
      ∃ x, ∀ v (ht : t < n), 0 < reducedPrice I β YB v ⟨t, ht⟩ → UB t v → UA t v ∨ v = x := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      intro _
      refine ⟨?_, ?_⟩
      · rintro v ht hpos ⟨u, h1, h2, h3⟩
        have hu : u = s := by omega
        rw [hu, hAs, Option.some.injEq] at h3
        rw [← h3, hpi _ ht (by omega) (by omega)] at hpos
        exact absurd hpos (lt_irrefl 0)
      · refine ⟨(hB s).getD i, ?_⟩
        rintro v ht hpos ⟨u, h1, h2, h3⟩
        have hu : u = s := by omega
        rw [hu] at h3
        right; rw [h3]; rfl
    | succ t hst ih =>
      intro hk
      obtain ⟨hI1, x, hI2⟩ := ih (by omega)
      have htn : t < n := by omega
      obtain ⟨CA, hCA, hrA⟩ := run_spec I β YA t htn
      obtain ⟨CB, hCB, hrB⟩ := run_spec I β YB t htn
      change ∀ v, v ∈ CA ↔ _ ∧ IsAvailable I hA v t at hCA
      change ∀ v, v ∈ CB ↔ _ ∧ IsAvailable I hB v t at hCB
      change hA t = _ at hrA
      change hB t = _ at hrB
      have hrA' : hA t = leastArgmax CA (fun v => reducedPrice I β YB v ⟨t, htn⟩) := by
        rw [hrA]; apply leastArgmax_congr
        intro v hv
        have hvi : v ≠ i := by
          rintro rfl
          have := ((havA t (by omega) (by omega) v).1 ((hCA v).1 hv).2).2
          exact this ⟨s, le_rfl, by omega, hAs⟩
        exact price_off I β Y i j y1 1 1 v _ (Or.inl hvi)
      have hBA : ∀ v ∈ CB, 0 < reducedPrice I β YB v ⟨t, htn⟩ → v ∈ CA := by
        intro v hv hpos
        rw [hCB] at hv; rw [hCA]
        refine ⟨hv.1, ?_⟩
        rw [havB t (by omega) (by omega)] at hv
        rw [havA t (by omega) (by omega)]
        exact ⟨hv.2.1, fun hU => hv.2.2 (hI1 v htn hpos hU)⟩
      have hAB : ∀ v ∈ CA, 0 < reducedPrice I β YB v ⟨t, htn⟩ → v ∈ CB ∨ v = x := by
        intro v hv hpos
        by_cases hU : UB t v
        · rcases hI2 v htn hpos hU with h | h
          · exfalso; rw [hCA, havA t (by omega) (by omega)] at hv; exact hv.2.2 h
          · exact Or.inr h
        · left; rw [hCA, havA t (by omega) (by omega)] at hv
          rw [hCB, havB t (by omega) (by omega)]
          exact ⟨hv.1, hv.2.1, hU⟩
      obtain ⟨S1, S2⟩ := step_abs hBA hAB
      rw [← hrA', ← hrB] at S1 S2
      refine ⟨?_, ?_⟩
      · intro v ht1 hpos hU
        have hpos' := hmono v t ht1 (by omega) (by omega) hpos
        rcases (hUs hA t v (by omega)).1 hU with hU | hU
        · exact (hUs hB t v (by omega)).2 (Or.inl (hI1 v htn hpos' hU))
        · rcases S1 v hU hpos' with h | ⟨-, hvB⟩
          · exact (hUs hB t v (by omega)).2 (Or.inr h)
          · have hvA : v ∈ CA := by rw [hrA'] at hU; exact (leastArgmax_some.1 hU).1
            rw [hCA, havA t (by omega) (by omega)] at hvA
            rw [hCB, havB t (by omega) (by omega)] at hvB
            by_contra hcon
            exact hvB ⟨hvA.1, hvA.2.1,
              fun hUB => hcon ((hUs hB t v (by omega)).2 (Or.inl hUB))⟩
      · by_cases hx : hA t = some x
        · refine ⟨(hB t).getD x, ?_⟩
          intro v ht1 hpos hU
          have hpos' := hmono v t ht1 (by omega) (by omega) hpos
          rcases (hUs hB t v (by omega)).1 hU with hU | hU
          · rcases hI2 v htn hpos' hU with h | h
            · exact Or.inl ((hUs hA t v (by omega)).2 (Or.inl h))
            · rw [h]; exact Or.inl ((hUs hA t x (by omega)).2 (Or.inr hx))
          · right; rw [hU]; rfl
        · refine ⟨x, ?_⟩
          intro v ht1 hpos hU
          have hpos' := hmono v t ht1 (by omega) (by omega) hpos
          rcases (hUs hB t v (by omega)).1 hU with hU | hU
          · rcases hI2 v htn hpos' hU with h | h
            · exact Or.inl ((hUs hA t v (by omega)).2 (Or.inl h))
            · exact Or.inr h
          · rcases S2 v hU hpos' with h | ⟨h, -⟩
            · exact Or.inl ((hUs hA t v (by omega)).2 (Or.inr h))
            · exact absurd h hx
  obtain ⟨hI1, -⟩ := hinv j (by omega) le_rfl
  apply ct_le I β hβ
  intro v hv hE
  by_cases hpos : 0 < reducedPrice I β YB v j
  · right
    have hvi : v ≠ i := by
      rintro rfl
      have := hpi j hjn (by omega) le_rfl
      rw [this] at hpos; exact absurd hpos (lt_irrefl 0)
    refine ⟨v, ?_, hE, (price_off I β Y i j 1 y1 1 v j (Or.inl hvi)).le⟩
    have hvB := (havB j (by omega) le_rfl v).1 hv
    exact (havA j (by omega) le_rfl v).2 ⟨hvB.1, fun hU => hvB.2 (hI1 v hjn hpos hU)⟩
  · left; exact not_lt.1 hpos

end L8Aux
end ReusableMatching

open ReusableMatching ReusableMatching.L8Aux in
theorem solution {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n)
    (β : ℝ) (hβ : 0 < β) (i : V) (j : Fin n) (hij : (i, j) ∈ I.E) (Y : Seeds V n)
    (z1 z2 : unitInterval) (hz : z1 ≤ z2) (h7 : ThreeRegimes I β Y i j z1 z2) :
    (∀ y1 : unitInterval, z2 < y1 →
      criticalThreshold I β Y i j y1 j = criticalThreshold I β Y i j 1 j) ∧
    ((∀ v : V, v ≠ i → (Y (v, prevPeriod I j) : ℝ) < 1) →
      ∀ y1 : unitInterval, z1 < y1 → y1 < z2 →
        criticalThreshold I β Y i j y1 j ≤ criticalThreshold I β Y i j 1 j) :=
  ⟨fun y1 hy1 => part_a I β hβ Y i j y1 (fun t ht hm => (h7.1 y1 hy1).2 ⟨t, ht, hm⟩),
   fun hY y1 h1 h2 => part_b I β hβ Y i j y1 hY (h7.2.1 y1 h1 h2).1⟩
