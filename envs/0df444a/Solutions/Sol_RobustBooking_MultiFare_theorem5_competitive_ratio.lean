-- Prove2me | solution 1 for RobustBooking.MultiFare.theorem5_competitive_ratio
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:59:10.617697+00:00
-- url     : https://prove2.me/submissions/db464b16-284d-4727-a519-a07a723b1fb3

import Mathlib
import Definitions.Def_RobustBooking_MultiFare_NestedPolicies
import Theorems.Thm_RobustBooking_MultiFare_lemma1_control_identities
import Theorems.Thm_RobustBooking_MultiFare_theorem4_no_policy_exceeds

open MeasureTheory

namespace Aux_RB_thm5

open RobustBooking.MultiFare

lemma f_pos (m : ℕ) (f : ℕ → ℝ) (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m)
    {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) : 0 < f i := by
  rcases him.lt_or_eq with h | h
  · exact lt_trans hfm (hf ⟨hi1, him⟩ ⟨by omega, le_rfl⟩ h)
  · rw [h]; exact hfm

lemma f_le_of_le (m : ℕ) (f : ℕ → ℝ) (hf : StrictAntiOn f (Set.Icc 1 m))
    {i j : ℕ} (hi1 : 1 ≤ i) (hij : i ≤ j) (hjm : j ≤ m) : f j ≤ f i := by
  rcases hij.lt_or_eq with h | h
  · exact (hf ⟨hi1, le_trans hij hjm⟩ ⟨le_trans hi1 hij, hjm⟩ h).le
  · rw [h]

lemma f_lt_of_lt (m : ℕ) (f : ℕ → ℝ) (hf : StrictAntiOn f (Set.Icc 1 m))
    {i j : ℕ} (hi1 : 1 ≤ i) (hij : i < j) (hjm : j ≤ m) : f j < f i :=
  hf ⟨hi1, by omega⟩ ⟨by omega, hjm⟩ hij

lemma f_le_iff (m : ℕ) (f : ℕ → ℝ) (hf : StrictAntiOn f (Set.Icc 1 m))
    {i j : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    f j ≤ f i ↔ i ≤ j := by
  constructor
  · intro hle
    by_contra hlt
    have hji : j < i := by omega
    have := f_lt_of_lt m f hf hj1 hji him
    linarith
  · intro hij
    exact f_le_of_le m f hf hi1 hij hjm

lemma weight_pos (m : ℕ) (f : ℕ → ℝ) (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m)
    {i : ℕ} (hi2 : 2 ≤ i) (him : i ≤ m) : 0 < 1 - f i / f (i - 1) := by
  have h1 : 0 < f (i - 1) := f_pos m f hf hfm (by omega) (by omega)
  have h2 : f i < f (i - 1) := hf ⟨by omega, by omega⟩ ⟨by omega, him⟩ (by omega)
  have h3 : f i / f (i - 1) < 1 := (div_lt_one h1).mpr h2
  linarith

lemma delta_eq_one_add_sum (m : ℕ) (f : ℕ → ℝ) (hm : 2 ≤ m) :
    Delta m f = 1 + ∑ i ∈ Finset.Icc 2 m, (1 - f i / f (i - 1)) := by
  unfold Delta
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc]
  have hcard : m + 1 - 2 = m - 1 := by omega
  rw [hcard, nsmul_eq_mul, mul_one, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  ring

lemma delta_ge_one (m : ℕ) (f : ℕ → ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) : 1 ≤ Delta m f := by
  rw [delta_eq_one_add_sum m f hm]
  have hsum : 0 ≤ ∑ i ∈ Finset.Icc 2 m, (1 - f i / f (i - 1)) := by
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_Icc] at hi
    exact (weight_pos m f hf hfm hi.1 hi.2).le
  linarith

lemma delta_pos (m : ℕ) (f : ℕ → ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) : 0 < Delta m f :=
  lt_of_lt_of_le zero_lt_one (delta_ge_one m f hm hf hfm)

lemma Q_one (m : ℕ) (f : ℕ → ℝ) (n : ℝ) : Q m f n 1 = n := by
  simp [Q, theta]

lemma Q_m_add_one (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m) : Q m f n (m + 1) = 0 := by
  have hm0 : m ≠ 0 := by omega
  simp [Q, theta, hm0]

lemma Q_strict_step (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) : Q m f n (i + 1) < Q m f n i := by
  obtain ⟨h1, h2, _⟩ := lemma1_control_identities m f n hm hf hfm hn
  have hΔ : 0 < Delta m f := delta_pos m f hm hf hfm
  have hfi : 0 < f i := f_pos m f hf hfm hi1 him
  rcases him.lt_or_eq with hlt | heq
  · have hmem : i ∈ Finset.Icc 1 (m - 1) := Finset.mem_Icc.mpr ⟨hi1, by omega⟩
    have heq1 := h1 i hmem
    have hdiff : 0 < f i - f (i + 1) := sub_pos.mpr (f_lt_of_lt m f hf hi1 (by omega) (by omega))
    have hprod : 0 < f i * (Q m f n i - Q m f n (i + 1)) := by
      rw [heq1]
      exact mul_pos (div_pos hn hΔ) hdiff
    have hsub : 0 < Q m f n i - Q m f n (i + 1) := pos_of_mul_pos_right hprod hfi.le
    linarith
  · subst heq
    have hprod : 0 < f i * (Q i f n i - Q i f n (i + 1)) := by
      rw [h2]
      exact div_pos (mul_pos hfm hn) hΔ
    have hsub : 0 < Q i f n i - Q i f n (i + 1) := pos_of_mul_pos_right hprod hfi.le
    linarith

lemma Q_anti (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n) :
    ∀ {i j : ℕ}, 1 ≤ i → i ≤ j → j ≤ m + 1 → Q m f n j ≤ Q m f n i := by
  intro i j hi1 hij hjm
  induction j with
  | zero => omega
  | succ j ih =>
    rcases hij.eq_or_lt with h | h
    · rw [h]
    · have hj_le : Q m f n (j + 1) ≤ Q m f n j :=
        (Q_strict_step m f n hm hf hfm hn (by omega) (by omega)).le
      exact le_trans hj_le (ih (by omega) (by omega))

lemma Q_strict_anti (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {i j : ℕ} (hi1 : 1 ≤ i) (hij : i < j) (hjm : j ≤ m + 1) :
    Q m f n j < Q m f n i := by
  have h1 : Q m f n j ≤ Q m f n (i + 1) := Q_anti m f n hm hf hfm hn (by omega) (by omega) hjm
  have h2 : Q m f n (i + 1) < Q m f n i := Q_strict_step m f n hm hf hfm hn hi1 (by omega)
  exact lt_of_le_of_lt h1 h2

lemma Q_nonneg (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m + 1) : 0 ≤ Q m f n i := by
  have h := Q_anti m f n hm hf hfm hn hi1 him le_rfl
  rw [Q_m_add_one m f n hm] at h
  exact h

-- General properties of `runFrom`
lemma runFrom_map_fst (n : ℝ) (B : DetPolicy) :
    ∀ (I : List Request) (past : List (Request × ℝ)),
      (runFrom n B past I).map Prod.fst = past.map Prod.fst ++ I
  | [], past => by simp [runFrom]
  | r :: rs, past => by
    simp only [runFrom]
    rw [runFrom_map_fst n B rs]
    simp [List.map_append]

lemma run_map_fst (n : ℝ) (B : DetPolicy) (I : List Request) :
    (run n B I).map Prod.fst = I := by
  simpa [run] using runFrom_map_fst n B I []

lemma map_fst_comp (L : List (Request × ℝ)) (g : Request → ℝ) :
    L.map (fun p => g p.1) = (L.map Prod.fst).map g := by
  rw [List.map_map]
  rfl

lemma runFrom_inv (m : ℕ) (n : ℝ) (B : DetPolicy) :
    ∀ (I : List Request) (past : List (Request × ℝ)),
      IsInstance m I →
      (∀ p ∈ past, 1 ≤ p.1.cls ∧ p.1.cls ≤ m ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1.qty) →
      (past.map Prod.snd).sum ≤ n →
      (∀ p ∈ runFrom n B past I, 1 ≤ p.1.cls ∧ p.1.cls ≤ m ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1.qty) ∧
      ((runFrom n B past I).map Prod.snd).sum ≤ n
  | [], past, _, hpast, hsum => ⟨hpast, hsum⟩
  | r :: rs, past, hI, hpast, hsum => by
    have hr : 1 ≤ r.cls ∧ r.cls ≤ m ∧ 0 < r.qty := hI r List.mem_cons_self
    have hrs : IsInstance m rs := fun q hq => hI q (List.mem_cons_of_mem _ hq)
    set used := (past.map Prod.snd).sum
    set y := clip n used r (B past r)
    have hy0 : 0 ≤ y := le_max_left 0 _
    have hy_qty : y ≤ r.qty := by
      dsimp [y, clip]
      exact max_le hr.2.2.le (le_trans (min_le_right _ _) (min_le_left _ _))
    have hy_cap : y ≤ n - used := by
      dsimp [y, clip]
      exact max_le (by linarith) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hpast' : ∀ p ∈ past ++ [(r, y)], 1 ≤ p.1.cls ∧ p.1.cls ≤ m ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1.qty := by
      intro p hp
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact hpast p hp
      · exact ⟨hr.1, hr.2.1, hy0, hy_qty⟩
    have hsum' : ((past ++ [(r, y)]).map Prod.snd).sum ≤ n := by
      rw [List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      dsimp [used] at hy_cap
      linarith
    exact runFrom_inv m n B rs (past ++ [(r, y)]) hrs hpast' hsum'

lemma sum_fin_eq_map_sum {α : Type*} (g : α → ℝ) :
    ∀ (I : List α), (∑ k : Fin I.length, g (I.get k)) = (I.map g).sum
  | [] => by simp
  | a :: as => by
    rw [List.map_cons, List.sum_cons, ← sum_fin_eq_map_sum g as]
    exact Fin.sum_univ_succ (fun k : Fin (as.length + 1) => g ((a :: as).get k))

lemma offlineOpt_nonempty (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hn : 0 < n)
    {I : List Request} (hI : IsInstance m I) :
    {v : ℝ | ∃ x : Fin I.length → ℝ,
      (∀ k, 0 ≤ x k ∧ x k ≤ (I.get k).qty) ∧ ∑ k, x k ≤ n ∧
      v = ∑ k, f (I.get k).cls * x k}.Nonempty := by
  refine ⟨0, fun _ => 0, ⟨fun k => ⟨le_rfl, ?_⟩, by simp [hn.le], by simp⟩⟩
  exact (hI (I.get k) (List.get_mem I k)).2.2.le

lemma offlineOpt_le_full (m : ℕ) (f : ℕ → ℝ) (n : ℝ)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {I : List Request} (hI : IsInstance m I) :
    offlineOpt f n I ≤ (I.map fun r => f r.cls * r.qty).sum := by
  unfold offlineOpt
  apply csSup_le (offlineOpt_nonempty m f n hn hI)
  rintro v ⟨x, hx1, _, rfl⟩
  rw [← sum_fin_eq_map_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hr := hI (I.get k) (List.get_mem I k)
  have hfk : 0 < f (I.get k).cls := f_pos m f hf hfm hr.1 hr.2.1
  exact mul_le_mul_of_nonneg_left (hx1 k).2 hfk.le

lemma offlineOpt_le_split (m : ℕ) (f : ℕ → ℝ) (n : ℝ)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {I : List Request} (hI : IsInstance m I) {i' : ℕ} (hi'1 : 1 ≤ i') (hi'm : i' ≤ m) :
    offlineOpt f n I ≤
      f i' * n + (I.map fun r => if r.cls < i' then (f r.cls - f i') * r.qty else 0).sum := by
  unfold offlineOpt
  have hfi' : 0 < f i' := f_pos m f hf hfm hi'1 hi'm
  apply csSup_le (offlineOpt_nonempty m f n hn hI)
  rintro v ⟨x, hx1, hx2, rfl⟩
  rw [← sum_fin_eq_map_sum]
  calc ∑ k : Fin I.length, f (I.get k).cls * x k
      ≤ ∑ k : Fin I.length,
          (f i' * x k + (if (I.get k).cls < i' then (f (I.get k).cls - f i') * (I.get k).qty else 0)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hr := hI (I.get k) (List.get_mem I k)
        split_ifs with hlt
        · have hdiff : 0 ≤ f (I.get k).cls - f i' :=
            sub_nonneg.mpr (f_lt_of_lt m f hf hr.1 hlt hi'm).le
          have hmul : (f (I.get k).cls - f i') * x k ≤ (f (I.get k).cls - f i') * (I.get k).qty :=
            mul_le_mul_of_nonneg_left (hx1 k).2 hdiff
          linarith
        · have hle : f (I.get k).cls ≤ f i' := f_le_of_le m f hf hi'1 (by omega) hr.2.1
          have hmul : f (I.get k).cls * x k ≤ f i' * x k :=
            mul_le_mul_of_nonneg_right hle (hx1 k).1
          linarith
    _ = f i' * (∑ k : Fin I.length, x k) +
          ∑ k : Fin I.length, (if (I.get k).cls < i' then (f (I.get k).cls - f i') * (I.get k).qty else 0) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ f i' * n +
          ∑ k : Fin I.length, (if (I.get k).cls < i' then (f (I.get k).cls - f i') * (I.get k).qty else 0) := by
        linarith [mul_le_mul_of_nonneg_left hx2 hfi'.le]

lemma sum_diff_le_sum_full (m : ℕ) (f : ℕ → ℝ)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m)
    {j₀ : ℕ} (hj₀1 : 1 ≤ j₀) (hj₀m : j₀ ≤ m) :
    ∀ (I : List Request),
      IsInstance m I →
      (I.map fun r => if r.cls < j₀ then (f r.cls - f j₀) * r.qty else 0).sum ≤
        (I.map fun r => if r.cls < j₀ then f r.cls * r.qty else 0).sum
  | [], _ => by simp
  | r :: rs, hI => by
    have hr := hI r List.mem_cons_self
    have hrs : IsInstance m rs := fun q hq => hI q (List.mem_cons_of_mem _ hq)
    have ih := sum_diff_le_sum_full m f hf hfm hj₀1 hj₀m rs hrs
    have hfj₀ : 0 < f j₀ := f_pos m f hf hfm hj₀1 hj₀m
    simp only [List.map_cons, List.sum_cons]
    split_ifs with hlt
    · have : (f r.cls - f j₀) * r.qty ≤ f r.cls * r.qty := by nlinarith [hr.2.2]
      linarith
    · linarith

-- Extraction of minimum rejected class
lemma all_full_or_min_rejected (m : ℕ) (L : List (Request × ℝ))
    (hL : ∀ p ∈ L, 1 ≤ p.1.cls ∧ p.1.cls ≤ m ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1.qty) :
    (∀ p ∈ L, p.2 = p.1.qty) ∨
      ∃ i', 1 ≤ i' ∧ i' ≤ m ∧
        (∃ p₀ ∈ L, p₀.1.cls = i' ∧ p₀.2 < p₀.1.qty) ∧
        (∀ p ∈ L, p.1.cls < i' → p.2 = p.1.qty) := by
  classical
  set S := ((L.filter fun p => decide (p.2 < p.1.qty)).map fun p => p.1.cls).toFinset
  by_cases hS : S.Nonempty
  · right
    let i' := S.min' hS
    have hi'_mem : i' ∈ S := Finset.min'_mem S hS
    simp only [S, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hi'_mem
    rcases hi'_mem with ⟨p₀, ⟨hp₀_mem, hp₀_lt⟩, hp₀_cls⟩
    have hp₀_bds := hL p₀ hp₀_mem
    refine ⟨i', hp₀_cls ▸ hp₀_bds.1, hp₀_cls ▸ hp₀_bds.2.1, ⟨p₀, hp₀_mem, hp₀_cls, hp₀_lt⟩, ?_⟩
    intro p hp hlt
    have hp_le := (hL p hp).2.2.2
    rcases hp_le.lt_or_eq with hlt_qty | heq
    · exfalso
      have hmem : p.1.cls ∈ S := by
        simp only [S, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
        exact ⟨p, ⟨hp, hlt_qty⟩, rfl⟩
      have hmin : i' ≤ p.1.cls := Finset.min'_le S p.1.cls hmem
      omega
    · exact heq
  · left
    rw [Finset.not_nonempty_iff_eq_empty] at hS
    intro p hp
    have hp_le := (hL p hp).2.2.2
    rcases hp_le.lt_or_eq with hlt_qty | heq
    · exfalso
      have hmem : p.1.cls ∈ S := by
        simp only [S, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
        exact ⟨p, ⟨hp, hlt_qty⟩, rfl⟩
      rw [hS] at hmem
      exact Finset.notMem_empty _ hmem
    · exact heq

-- Part 1: Protection-Level Policy (`protectionPolicy`)
lemma acceptedAtOrBelow_append_singleton (past : List (Request × ℝ)) (r : Request) (y : ℝ) (j : ℕ) :
    acceptedAtOrBelow (past ++ [(r, y)]) j =
      acceptedAtOrBelow past j + (if j ≤ r.cls then y else 0) := by
  unfold acceptedAtOrBelow
  rw [List.filter_append]
  by_cases h : j ≤ r.cls <;> simp [h]

lemma acceptedAtOrBelow_one (past : List (Request × ℝ)) (h : ∀ p ∈ past, 1 ≤ p.1.cls) :
    acceptedAtOrBelow past 1 = (past.map Prod.snd).sum := by
  unfold acceptedAtOrBelow
  have hfilt : past.filter (fun p => decide (1 ≤ p.1.cls)) = past := by
    rw [List.filter_eq_self]
    intro p hp
    simp [h p hp]
  rw [hfilt]

lemma acceptedAtOrBelow_gt_m (m : ℕ) (past : List (Request × ℝ)) (h : ∀ p ∈ past, p.1.cls ≤ m)
    {j : ℕ} (hj : m < j) : acceptedAtOrBelow past j = 0 := by
  unfold acceptedAtOrBelow
  have hfilt : past.filter (fun p => decide (j ≤ p.1.cls)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp
    simp only [decide_eq_true_eq, not_le]
    exact lt_of_le_of_lt (h p hp) hj
  rw [hfilt]
  simp

lemma protectionPolicy_step (m : ℕ) (f : ℕ → ℝ) (n : ℝ)
    (past : List (Request × ℝ)) (r : Request)
    (hpast1 : ∀ p ∈ past, 1 ≤ p.1.cls)
    (hr : 1 ≤ r.cls ∧ r.cls ≤ m ∧ 0 < r.qty)
    (hQ : ∀ j ∈ Finset.Icc 1 (m + 1), acceptedAtOrBelow past j ≤ Q m f n j) :
    clip n (past.map Prod.snd).sum r (protectionPolicy m f n past r) =
      min r.qty ((Finset.Icc 1 r.cls).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hr.1⟩⟩
        (fun j => Q m f n j - acceptedAtOrBelow past j)) ∧
    0 ≤ min r.qty ((Finset.Icc 1 r.cls).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hr.1⟩⟩
        (fun j => Q m f n j - acceptedAtOrBelow past j)) := by
  set M := (Finset.Icc 1 r.cls).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hr.1⟩⟩
    (fun j => Q m f n j - acceptedAtOrBelow past j)
  have hM_nonneg : 0 ≤ M := by
    refine (Finset.le_inf'_iff _ _).mpr fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    have hj_mem : j ∈ Finset.Icc 1 (m + 1) := Finset.mem_Icc.mpr ⟨hj.1, by omega⟩
    linarith [hQ j hj_mem]
  have hmin_nonneg : 0 ≤ min r.qty M := le_min hr.2.2.le hM_nonneg
  have hsup : protectionPolicy m f n past r = min r.qty M := by
    unfold protectionPolicy
    apply IsGreatest.csSup_eq
    constructor
    · refine ⟨hmin_nonneg, min_le_left _ _, fun j hj => ?_⟩
      have h1 : min r.qty M ≤ M := min_le_right _ _
      have h2 : M ≤ Q m f n j - acceptedAtOrBelow past j := Finset.inf'_le _ hj
      linarith
    · rintro α ⟨_, hα_qty, hα_Q⟩
      refine le_min hα_qty ?_
      refine (Finset.le_inf'_iff _ _).mpr fun j hj => ?_
      linarith [hα_Q j hj]
  have h1_mem : 1 ∈ Finset.Icc 1 r.cls := Finset.mem_Icc.mpr ⟨le_rfl, hr.1⟩
  have hM_le_cap : M ≤ n - (past.map Prod.snd).sum := by
    calc M ≤ Q m f n 1 - acceptedAtOrBelow past 1 := Finset.inf'_le _ h1_mem
      _ = n - (past.map Prod.snd).sum := by rw [Q_one, acceptedAtOrBelow_one past hpast1]
  refine ⟨?_, hmin_nonneg⟩
  rw [hsup]
  unfold clip
  have hmin2 : min (min r.qty M) (min r.qty (n - (past.map Prod.snd).sum)) = min r.qty M := by
    apply min_eq_left
    exact min_le_min le_rfl hM_le_cap
  rw [hmin2, max_eq_right hmin_nonneg]

lemma runFrom_protection_props (m : ℕ) (f : ℕ → ℝ) (n : ℝ) :
    ∀ (I : List Request) (past : List (Request × ℝ)),
      IsInstance m I →
      (∀ p ∈ past, 1 ≤ p.1.cls ∧ p.1.cls ≤ m ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1.qty) →
      (∀ j ∈ Finset.Icc 1 (m + 1), acceptedAtOrBelow past j ≤ Q m f n j) →
      let final := runFrom n (protectionPolicy m f n) past I
      (∀ j ∈ Finset.Icc 1 (m + 1), acceptedAtOrBelow past j ≤ acceptedAtOrBelow final j ∧
        acceptedAtOrBelow final j ≤ Q m f n j) ∧
      (∀ p ∈ final, p.2 < p.1.qty →
        p ∈ past ∨ ∃ j₀ ∈ Finset.Icc 1 p.1.cls, acceptedAtOrBelow final j₀ = Q m f n j₀)
  | [], past, _, _, hQ => by
    simp only [runFrom]
    exact ⟨fun j hj => ⟨le_rfl, hQ j hj⟩, fun p hp _ => Or.inl hp⟩
  | r :: rs, past, hI, hpast, hQ => by
    simp only [runFrom]
    have hr : 1 ≤ r.cls ∧ r.cls ≤ m ∧ 0 < r.qty := hI r List.mem_cons_self
    have hrs : IsInstance m rs := fun q hq => hI q (List.mem_cons_of_mem _ hq)
    have hpast1 : ∀ p ∈ past, 1 ≤ p.1.cls := fun p hp => (hpast p hp).1
    obtain ⟨hy_eq, hy0⟩ := protectionPolicy_step m f n past r hpast1 hr hQ
    set M := (Finset.Icc 1 r.cls).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hr.1⟩⟩
      (fun j => Q m f n j - acceptedAtOrBelow past j)
    set y := clip n (past.map Prod.snd).sum r (protectionPolicy m f n past r)
    have hy_qty : y ≤ r.qty := hy_eq ▸ min_le_left _ _
    have hpast' : ∀ p ∈ past ++ [(r, y)], 1 ≤ p.1.cls ∧ p.1.cls ≤ m ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1.qty := by
      intro p hp
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact hpast p hp
      · exact ⟨hr.1, hr.2.1, hy_eq ▸ hy0, hy_qty⟩
    have hQ' : ∀ j ∈ Finset.Icc 1 (m + 1), acceptedAtOrBelow (past ++ [(r, y)]) j ≤ Q m f n j := by
      intro j hj
      rw [acceptedAtOrBelow_append_singleton]
      split_ifs with hle
      · have hj_mem : j ∈ Finset.Icc 1 r.cls := Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, hle⟩
        have hM_le : M ≤ Q m f n j - acceptedAtOrBelow past j := Finset.inf'_le _ hj_mem
        have hy_le_M : y ≤ M := hy_eq ▸ min_le_right _ _
        linarith
      · linarith [hQ j hj]
    obtain ⟨ih_Q, ih_p⟩ := runFrom_protection_props m f n rs (past ++ [(r, y)]) hrs hpast' hQ'
    refine ⟨fun j hj => ?_, fun p hp hlt => ?_⟩
    · obtain ⟨h1, h2⟩ := ih_Q j hj
      have hstep : acceptedAtOrBelow past j ≤ acceptedAtOrBelow (past ++ [(r, y)]) j := by
        rw [acceptedAtOrBelow_append_singleton]
        have hy_nonneg : 0 ≤ y := hy_eq ▸ hy0
        split_ifs <;> linarith
      exact ⟨le_trans hstep h1, h2⟩
    · rcases ih_p p hp hlt with hp_in | htight
      · simp only [List.mem_append, List.mem_singleton] at hp_in
        rcases hp_in with hp_in | rfl
        · exact Or.inl hp_in
        · right
          change y < r.qty at hlt
          have hy_eq_M : y = M := by
            rw [hy_eq] at hlt ⊢
            exact min_eq_right (le_of_not_ge fun hge => hlt.not_ge (min_eq_left hge).ge)
          obtain ⟨j₀, hj₀_mem, hj₀_eq⟩ := Finset.exists_mem_eq_inf'
            ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hr.1⟩⟩
            (fun j => Q m f n j - acceptedAtOrBelow past j)
          refine ⟨j₀, hj₀_mem, ?_⟩
          have hj₀_Icc : j₀ ∈ Finset.Icc 1 (m + 1) :=
            Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj₀_mem).1, by linarith [(Finset.mem_Icc.mp hj₀_mem).2, hr.2.1]⟩
          obtain ⟨h1, h2⟩ := ih_Q j₀ hj₀_Icc
          have htight_step : acceptedAtOrBelow (past ++ [(r, y)]) j₀ = Q m f n j₀ := by
            rw [acceptedAtOrBelow_append_singleton, if_pos (Finset.mem_Icc.mp hj₀_mem).2, hy_eq_M]
            linarith [hj₀_eq]
          linarith
      · exact Or.inr htight

lemma acceptedAtOrBelow_cons_diff (p : Request × ℝ) (ps : List (Request × ℝ)) (i : ℕ) :
    (acceptedAtOrBelow (p :: ps) i - acceptedAtOrBelow (p :: ps) (i + 1)) =
      (acceptedAtOrBelow ps i - acceptedAtOrBelow ps (i + 1)) +
        (if i = p.1.cls then p.2 else 0) := by
  unfold acceptedAtOrBelow
  simp only [List.filter_cons]
  by_cases h1 : i ≤ p.1.cls
  · by_cases h2 : i + 1 ≤ p.1.cls
    · have hne : i ≠ p.1.cls := by omega
      simp [h1, h2, hne]
    · have heq : i = p.1.cls := by omega
      simp [heq]
      ring
  · have h2 : ¬ (i + 1 ≤ p.1.cls) := by omega
    have hne : i ≠ p.1.cls := by omega
    simp [h1, h2, hne]

lemma list_rev_split_acceptedAtOrBelow (m : ℕ) (f : ℕ → ℝ) (j₀ : ℕ) :
    ∀ (L : List (Request × ℝ)),
      (∀ p ∈ L, 1 ≤ p.1.cls ∧ p.1.cls ≤ m) →
      (L.map fun p => f p.1.cls * p.2).sum =
        (L.map fun p => if p.1.cls < j₀ then f p.1.cls * p.2 else 0).sum +
          ∑ i ∈ Finset.Icc j₀ m, f i * (acceptedAtOrBelow L i - acceptedAtOrBelow L (i + 1))
  | [], _ => by simp [acceptedAtOrBelow]
  | p :: ps, hL => by
    have hp := hL p List.mem_cons_self
    have ih := list_rev_split_acceptedAtOrBelow m f j₀ ps (fun q hq => hL q (List.mem_cons_of_mem _ hq))
    simp only [List.map_cons, List.sum_cons]
    have hsum_step :
        ∑ i ∈ Finset.Icc j₀ m, f i * (acceptedAtOrBelow (p :: ps) i - acceptedAtOrBelow (p :: ps) (i + 1)) =
          ∑ i ∈ Finset.Icc j₀ m, f i * (acceptedAtOrBelow ps i - acceptedAtOrBelow ps (i + 1)) +
            (if j₀ ≤ p.1.cls then f p.1.cls * p.2 else 0) := by
      have hcongr :
          ∑ i ∈ Finset.Icc j₀ m, f i * (acceptedAtOrBelow (p :: ps) i - acceptedAtOrBelow (p :: ps) (i + 1)) =
            ∑ i ∈ Finset.Icc j₀ m,
              (f i * (acceptedAtOrBelow ps i - acceptedAtOrBelow ps (i + 1)) +
                (if i = p.1.cls then f p.1.cls * p.2 else 0)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [acceptedAtOrBelow_cons_diff, mul_add]
        split_ifs with heq
        · rw [heq]
        · ring
      rw [hcongr, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_Icc, hp.2, and_true]
    rw [ih, hsum_step]
    by_cases hlt : p.1.cls < j₀
    · have hnot : ¬ (j₀ ≤ p.1.cls) := by omega
      simp [hlt, hnot]
      ring
    · have hge : j₀ ≤ p.1.cls := by omega
      simp [hlt, hge]
      ring

lemma sum_by_parts_protection (f u Qv : ℕ → ℝ) (j₀ : ℕ) (hj₀1 : 1 ≤ j₀) :
    ∀ k : ℕ, j₀ ≤ k →
      ∑ i ∈ Finset.Icc j₀ k, f i * (u i - u (i + 1)) -
        ∑ i ∈ Finset.Icc j₀ k, f i * (Qv i - Qv (i + 1)) =
      f j₀ * (u j₀ - Qv j₀) - f k * (u (k + 1) - Qv (k + 1)) +
        ∑ i ∈ Finset.Icc j₀ (k - 1), (f i - f (i + 1)) * (Qv (i + 1) - u (i + 1))
  | 0, h => by omega
  | k + 1, hjk => by
    rcases hjk.eq_or_lt with heq | hlt
    · subst heq
      have hIcc : (Finset.Icc (k + 1) k : Finset ℕ) = ∅ := by
        ext x; simp
      simp only [Finset.Icc_self, Finset.sum_singleton, Nat.add_sub_cancel, hIcc, Finset.sum_empty]
      ring
    · have ih := sum_by_parts_protection f u Qv j₀ hj₀1 k (by omega)
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      have hsub : k + 1 - 1 = k := by omega
      have hprev : k = (k - 1) + 1 := by omega
      rw [hsub]
      conv_rhs => rw [hprev, Finset.sum_Icc_succ_top (by omega), ← hprev]
      linarith

lemma protection_tail_rev_ge (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    (L : List (Request × ℝ))
    (hL_cls : ∀ p ∈ L, 1 ≤ p.1.cls ∧ p.1.cls ≤ m)
    (hL_Q : ∀ j ∈ Finset.Icc 1 (m + 1), acceptedAtOrBelow L j ≤ Q m f n j)
    {j₀ : ℕ} (hj₀1 : 1 ≤ j₀) (hj₀m : j₀ ≤ m)
    (htight : acceptedAtOrBelow L j₀ = Q m f n j₀) :
    f j₀ * (n / Delta m f) ≤
      ∑ i ∈ Finset.Icc j₀ m, f i * (acceptedAtOrBelow L i - acceptedAtOrBelow L (i + 1)) := by
  obtain ⟨_, _, hsum_Q⟩ := lemma1_control_identities m f n hm hf hfm hn
  rw [← hsum_Q j₀ (Finset.mem_Icc.mpr ⟨hj₀1, hj₀m⟩)]
  have hsbp := sum_by_parts_protection f (acceptedAtOrBelow L) (Q m f n) j₀ hj₀1 m hj₀m
  have hum1 : acceptedAtOrBelow L (m + 1) = 0 :=
    acceptedAtOrBelow_gt_m m L (fun p hp => (hL_cls p hp).2) (by omega)
  have hQm1 : Q m f n (m + 1) = 0 := Q_m_add_one m f n hm
  have hnonneg : 0 ≤ ∑ i ∈ Finset.Icc j₀ (m - 1),
      (f i - f (i + 1)) * (Q m f n (i + 1) - acceptedAtOrBelow L (i + 1)) := by
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hdiff_f : 0 ≤ f i - f (i + 1) :=
      sub_nonneg.mpr (f_lt_of_lt m f hf (by omega) (by omega) (by omega)).le
    have hdiff_Q : 0 ≤ Q m f n (i + 1) - acceptedAtOrBelow L (i + 1) :=
      sub_nonneg.mpr (hL_Q (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    exact mul_nonneg hdiff_f hdiff_Q
  rw [htight, hum1, hQm1] at hsbp
  linarith

lemma protection_instance_bound (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {I : List Request} (hI : IsInstance m I) :
    1 / Delta m f * offlineOpt f n I ≤ revenue f n (protectionPolicy m f n) I := by
  have hΔ_ge1 : 1 ≤ Delta m f := delta_ge_one m f hm hf hfm
  have hΔ_pos : 0 < Delta m f := delta_pos m f hm hf hfm
  have h1Δ_le1 : 1 / Delta m f ≤ 1 := (div_le_one hΔ_pos).mpr hΔ_ge1
  have h1Δ_pos : 0 < 1 / Delta m f := one_div_pos.mpr hΔ_pos
  set B := protectionPolicy m f n
  set L := run n B I
  have hL_inv : (∀ p ∈ L, 1 ≤ p.1.cls ∧ p.1.cls ≤ m ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1.qty) ∧
      (L.map Prod.snd).sum ≤ n :=
    runFrom_inv m n B I [] hI (by simp) (by simp [hn.le])
  have hQ_init : ∀ j ∈ Finset.Icc 1 (m + 1), acceptedAtOrBelow [] j ≤ Q m f n j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    simpa [acceptedAtOrBelow] using Q_nonneg m f n hm hf hfm hn hj.1 hj.2
  obtain ⟨hL_Q, hL_tight⟩ := runFrom_protection_props m f n I [] hI (by simp) hQ_init
  rcases all_full_or_min_rejected m L hL_inv.1 with hfull | ⟨i', hi'1, hi'm, ⟨p₀, hp₀_mem, hp₀_cls, hp₀_lt⟩, hfull_lt⟩
  · -- Case 1: all requests accepted in full
    have hrev_eq : revenue f n B I = (I.map fun r => f r.cls * r.qty).sum := by
      unfold revenue
      have hcongr : L.map (fun p => f p.1.cls * p.2) = L.map (fun p => f p.1.cls * p.1.qty) := by
        apply List.map_congr_left
        intro p hp
        rw [hfull p hp]
      rw [hcongr, map_fst_comp L (fun r => f r.cls * r.qty), run_map_fst]
    have hopt_le := offlineOpt_le_full m f n hf hfm hn hI
    have hopt_nonneg : 0 ≤ offlineOpt f n I := by
      unfold offlineOpt
      exact le_csSup_of_le (by
        refine ⟨(I.map fun r => f r.cls * r.qty).sum, ?_⟩
        rintro v ⟨x, hx1, _, rfl⟩
        rw [← sum_fin_eq_map_sum]
        refine Finset.sum_le_sum fun k _ => ?_
        have hr := hI (I.get k) (List.get_mem I k)
        exact mul_le_mul_of_nonneg_left (hx1 k).2 (f_pos m f hf hfm hr.1 hr.2.1).le)
        ⟨fun _ => 0, ⟨fun k => ⟨le_rfl, (hI (I.get k) (List.get_mem I k)).2.2.le⟩, by simp [hn.le], by simp⟩⟩
        le_rfl
    calc 1 / Delta m f * offlineOpt f n I
        ≤ 1 * offlineOpt f n I := mul_le_mul_of_nonneg_right h1Δ_le1 hopt_nonneg
      _ = offlineOpt f n I := one_mul _
      _ ≤ (I.map fun r => f r.cls * r.qty).sum := hopt_le
      _ = revenue f n B I := hrev_eq.symm
  · -- Case 2: some request of class i' not accepted in full
    rcases hL_tight p₀ hp₀_mem hp₀_lt with hp₀_nil | ⟨j₀, hj₀_mem, hj₀_eq⟩
    · simp at hp₀_nil
    · rw [hp₀_cls, Finset.mem_Icc] at hj₀_mem
      have hj₀1 : 1 ≤ j₀ := hj₀_mem.1
      have hj₀m : j₀ ≤ m := le_trans hj₀_mem.2 hi'm
      have hrev_split := list_rev_split_acceptedAtOrBelow m f j₀ L
        (fun p hp => ⟨(hL_inv.1 p hp).1, (hL_inv.1 p hp).2.1⟩)
      have htail_ge := protection_tail_rev_ge m f n hm hf hfm hn L
        (fun p hp => ⟨(hL_inv.1 p hp).1, (hL_inv.1 p hp).2.1⟩)
        (fun j hj => (hL_Q j hj).2) hj₀1 hj₀m hj₀_eq
      have hhead_eq :
          (L.map fun p => if p.1.cls < j₀ then f p.1.cls * p.2 else 0).sum =
            (I.map fun r => if r.cls < j₀ then f r.cls * r.qty else 0).sum := by
        have hcongr :
            L.map (fun p => if p.1.cls < j₀ then f p.1.cls * p.2 else 0) =
              L.map (fun p => if p.1.cls < j₀ then f p.1.cls * p.1.qty else 0) := by
          apply List.map_congr_left
          intro p hp
          split_ifs with hlt
          · rw [hfull_lt p hp (lt_of_lt_of_le hlt hj₀_mem.2)]
          · rfl
        rw [hcongr, map_fst_comp L (fun r => if r.cls < j₀ then f r.cls * r.qty else 0),
          run_map_fst]
      have hhead_ge_diff := sum_diff_le_sum_full m f hf hfm hj₀1 hj₀m I hI
      have hdiff_nonneg :
          0 ≤ (I.map fun r => if r.cls < j₀ then (f r.cls - f j₀) * r.qty else 0).sum := by
        apply List.sum_nonneg
        intro x hx
        rw [List.mem_map] at hx
        rcases hx with ⟨r, hr_mem, rfl⟩
        have hr := hI r hr_mem
        split_ifs with hlt
        · exact mul_nonneg (sub_nonneg.mpr (f_lt_of_lt m f hf hr.1 hlt hj₀m).le) hr.2.2.le
        · exact le_rfl
      have hopt_le := offlineOpt_le_split m f n hf hfm hn hI hj₀1 hj₀m
      unfold revenue
      set S_diff := (I.map fun r => if r.cls < j₀ then (f r.cls - f j₀) * r.qty else 0).sum
      calc 1 / Delta m f * offlineOpt f n I
          ≤ 1 / Delta m f * (f j₀ * n + S_diff) :=
            mul_le_mul_of_nonneg_left hopt_le h1Δ_pos.le
        _ = f j₀ * (n / Delta m f) + 1 / Delta m f * S_diff := by ring
        _ ≤ f j₀ * (n / Delta m f) + 1 * S_diff := by
            linarith [mul_le_mul_of_nonneg_right h1Δ_le1 hdiff_nonneg]
        _ ≤ ∑ i ∈ Finset.Icc j₀ m, f i * (acceptedAtOrBelow L i - acceptedAtOrBelow L (i + 1)) +
              (L.map fun p => if p.1.cls < j₀ then f p.1.cls * p.2 else 0).sum := by
            rw [one_mul, hhead_eq]
            linarith [htail_ge, hhead_ge_diff]
        _ = (L.map fun p => f p.1.cls * p.2).sum := by linarith [hrev_split]

-- Part 2: Order Quantity Policy (`orderQuantityPolicy`)
lemma orderPrice_le_iff (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {q : ℝ} (hq0 : 0 ≤ q) (hqn : q ≤ n) {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ m) :
    orderPrice m f n q ≤ f c ↔ q ≤ Q m f n c := by
  unfold orderPrice
  by_cases hq_zero : q = 0
  · subst hq_zero
    rw [if_pos rfl]
    exact ⟨fun _ => Q_nonneg m f n hm hf hfm hn hc1 (by omega),
      fun _ => (f_pos m f hf hfm hc1 hcm).le⟩
  · rw [if_neg hq_zero]
    set k := Nat.findGreatest (fun i => q ≤ Q m f n i) m
    have hQ1 : q ≤ Q m f n 1 := by rw [Q_one]; exact hqn
    have hk_ge1 : 1 ≤ k := Nat.le_findGreatest (by omega : 1 ≤ m) hQ1
    have hk_le_m : k ≤ m := Nat.findGreatest_le m
    have hk_spec : q ≤ Q m f n k :=
      Nat.findGreatest_spec (P := fun i => q ≤ Q m f n i) (by omega : 1 ≤ m) hQ1
    rw [f_le_iff m f hf hc1 hcm hk_ge1 hk_le_m]
    constructor
    · intro hck
      exact le_trans hk_spec (Q_anti m f n hm hf hfm hn hc1 hck (by omega))
    · intro hq_le
      exact Nat.le_findGreatest hcm hq_le

lemma orderQuantityPolicy_step (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    (past : List (Request × ℝ)) (r : Request)
    (hq0 : 0 ≤ (past.map Prod.snd).sum) (hqn : (past.map Prod.snd).sum ≤ n)
    (hr : 1 ≤ r.cls ∧ r.cls ≤ m ∧ 0 < r.qty) :
    clip n (past.map Prod.snd).sum r (orderQuantityPolicy m f n past r) =
      max 0 (min r.qty (Q m f n r.cls - (past.map Prod.snd).sum)) := by
  set qhat := (past.map Prod.snd).sum
  have hQr_le_n : Q m f n r.cls ≤ n := by
    have h := Q_anti m f n hm hf hfm hn le_rfl hr.1 (by omega)
    rw [Q_one] at h
    exact h
  by_cases hq_le : qhat ≤ Q m f n r.cls
  · have hprice : orderPrice m f n qhat ≤ f r.cls :=
      (orderPrice_le_iff m f n hm hf hfm hn hq0 hqn hr.1 hr.2.1).mpr hq_le
    have hnot_lt : ¬ (f r.cls < orderPrice m f n qhat) := not_lt.mpr hprice
    have hM0 : 0 ≤ min r.qty (Q m f n r.cls - qhat) := le_min hr.2.2.le (by linarith)
    have hsup : orderQuantityPolicy m f n past r = min r.qty (Q m f n r.cls - qhat) := by
      unfold orderQuantityPolicy
      dsimp only
      rw [if_neg hnot_lt]
      apply IsGreatest.csSup_eq
      constructor
      · refine ⟨hM0, min_le_left _ _, ?_, ?_⟩
        · have : min r.qty (Q m f n r.cls - qhat) ≤ Q m f n r.cls - qhat := min_le_right _ _
          linarith
        · rw [orderPrice_le_iff m f n hm hf hfm hn (by linarith) (by
            have : min r.qty (Q m f n r.cls - qhat) ≤ Q m f n r.cls - qhat := min_le_right _ _
            linarith) hr.1 hr.2.1]
          have : min r.qty (Q m f n r.cls - qhat) ≤ Q m f n r.cls - qhat := min_le_right _ _
          linarith
      · rintro α ⟨hα0, hα_qty, hα_n, hα_price⟩
        rw [orderPrice_le_iff m f n hm hf hfm hn (by linarith) hα_n hr.1 hr.2.1] at hα_price
        exact le_min hα_qty (by linarith)
    rw [hsup]
    unfold clip
    have hmin2 :
        min (min r.qty (Q m f n r.cls - qhat)) (min r.qty (n - qhat)) =
          min r.qty (Q m f n r.cls - qhat) := by
      apply min_eq_left
      exact min_le_min le_rfl (by linarith)
    rw [hmin2]
  · have hprice : f r.cls < orderPrice m f n qhat := by
      by_contra hge
      have hle := (orderPrice_le_iff m f n hm hf hfm hn hq0 hqn hr.1 hr.2.1).mp (not_lt.mp hge)
      exact hq_le hle
    have hpol0 : orderQuantityPolicy m f n past r = 0 := by
      unfold orderQuantityPolicy
      dsimp only
      rw [if_pos hprice]
    rw [hpol0]
    unfold clip
    have h1 : min (0 : ℝ) (min r.qty (n - qhat)) = 0 :=
      min_eq_left (le_min hr.2.2.le (by linarith))
    have h2 : max 0 (min r.qty (Q m f n r.cls - qhat)) = 0 :=
      max_eq_left (le_trans (min_le_right _ _) (by linarith))
    rw [h1, max_self, h2]

-- Bracket length and potential function V_tail
noncomputable def brkLen (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (i : ℕ) (q : ℝ) : ℝ :=
  min q (Q m f n i) - min q (Q m f n (i + 1))

noncomputable def V_tail (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (i' : ℕ) (q : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc i' m, f i * brkLen m f n i q

lemma min_sub_min_mono {a b q₁ q₂ : ℝ} (hab : a ≤ b) (hq : q₁ ≤ q₂) :
    min q₁ b - min q₁ a ≤ min q₂ b - min q₂ a := by
  rcases le_total q₁ a with h1 | h1 <;>
  rcases le_total q₁ b with h2 | h2 <;>
  rcases le_total q₂ a with h3 | h3 <;>
  rcases le_total q₂ b with h4 | h4 <;>
  simp only [min_eq_left, min_eq_right, *] <;> linarith

lemma brkLen_mono (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) {q₁ q₂ : ℝ} (hq : q₁ ≤ q₂) :
    brkLen m f n i q₁ ≤ brkLen m f n i q₂ :=
  min_sub_min_mono (Q_strict_step m f n hm hf hfm hn hi1 him).le hq

lemma sum_brkLen_Icc (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (q : ℝ) :
    ∀ (a k : ℕ), a ≤ k →
      ∑ i ∈ Finset.Icc a k, brkLen m f n i q = min q (Q m f n a) - min q (Q m f n (k + 1))
  | a, 0, hak => by
    have : a = 0 := by omega
    subst this
    simp [brkLen]
  | a, k + 1, hak => by
    rcases hak.eq_or_lt with rfl | hlt
    · simp [brkLen]
    · rw [Finset.sum_Icc_succ_top (by omega), sum_brkLen_Icc m f n q a k (by omega)]
      unfold brkLen
      ring

lemma V_tail_zero (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {i' : ℕ} (hi'1 : 1 ≤ i') : V_tail m f n i' 0 = 0 := by
  unfold V_tail brkLen
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_Icc] at hi
  have h1 : 0 ≤ Q m f n i := Q_nonneg m f n hm hf hfm hn (by omega) (by omega)
  have h2 : 0 ≤ Q m f n (i + 1) := Q_nonneg m f n hm hf hfm hn (by omega) (by omega)
  rw [min_eq_left h1, min_eq_left h2, sub_self, mul_zero]

lemma V_tail_ge_Q (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {i' : ℕ} (hi'1 : 1 ≤ i') (hi'm : i' ≤ m) {q : ℝ} (hq : Q m f n i' ≤ q) :
    V_tail m f n i' q = f i' * (n / Delta m f) := by
  obtain ⟨_, _, hsum⟩ := lemma1_control_identities m f n hm hf hfm hn
  rw [← hsum i' (Finset.mem_Icc.mpr ⟨hi'1, hi'm⟩)]
  unfold V_tail brkLen
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Icc] at hi
  have h1 : Q m f n i ≤ q := le_trans (Q_anti m f n hm hf hfm hn hi'1 hi.1 (by omega)) hq
  have h2 : Q m f n (i + 1) ≤ q := le_trans (Q_anti m f n hm hf hfm hn hi'1 (by omega) (by omega)) hq
  rw [min_eq_right h1, min_eq_right h2]

lemma V_tail_step_bound (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {i' : ℕ} (hi'1 : 1 ≤ i') (hi'm : i' ≤ m)
    {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ m)
    {q y : ℝ} (hy0 : 0 ≤ y) (hy_Q : 0 < y → q + y ≤ Q m f n c) :
    V_tail m f n i' (q + y) - V_tail m f n i' q ≤
      (if c < i' then f i' else f c) * y := by
  rcases hy0.eq_or_lt with rfl | hy_pos
  · simp
  · have hq_le : q + y ≤ Q m f n c := hy_Q hy_pos
    unfold V_tail
    rw [← Finset.sum_sub_distrib]
    have hcongr :
        ∑ i ∈ Finset.Icc i' m, (f i * brkLen m f n i (q + y) - f i * brkLen m f n i q) =
          ∑ i ∈ Finset.Icc i' m, f i * (brkLen m f n i (q + y) - brkLen m f n i q) := by
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hcongr]
    split_ifs with hlt
    · -- Case c < i': every i ∈ Icc i' m has f i ≤ f i'
      calc ∑ i ∈ Finset.Icc i' m, f i * (brkLen m f n i (q + y) - brkLen m f n i q)
          ≤ ∑ i ∈ Finset.Icc i' m, f i' * (brkLen m f n i (q + y) - brkLen m f n i q) := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [Finset.mem_Icc] at hi
            have hfi : f i ≤ f i' := f_le_of_le m f hf hi'1 hi.1 hi.2
            have hbrk : 0 ≤ brkLen m f n i (q + y) - brkLen m f n i q :=
              sub_nonneg.mpr (brkLen_mono m f n hm hf hfm hn (by omega) hi.2 (by linarith))
            exact mul_le_mul_of_nonneg_right hfi hbrk
        _ = f i' * (∑ i ∈ Finset.Icc i' m, brkLen m f n i (q + y) -
              ∑ i ∈ Finset.Icc i' m, brkLen m f n i q) := by
            rw [← Finset.mul_sum, Finset.sum_sub_distrib]
        _ = f i' * ((min (q + y) (Q m f n i') - min (q + y) (Q m f n (m + 1))) -
              (min q (Q m f n i') - min q (Q m f n (m + 1)))) := by
            rw [sum_brkLen_Icc m f n (q + y) i' m hi'm, sum_brkLen_Icc m f n q i' m hi'm]
        _ ≤ f i' * y := by
            apply mul_le_mul_of_nonneg_left _ (f_pos m f hf hfm hi'1 hi'm).le
            have h1 : min (q + y) (Q m f n i') - min q (Q m f n i') ≤ y := by
              rcases le_total (q + y) (Q m f n i') with h | h <;>
              rcases le_total q (Q m f n i') with h' | h' <;>
              simp only [min_eq_left, min_eq_right, *] <;> linarith
            have h2 : min q (Q m f n (m + 1)) ≤ min (q + y) (Q m f n (m + 1)) := by
              rcases le_total (q + y) (Q m f n (m + 1)) with h | h <;>
              rcases le_total q (Q m f n (m + 1)) with h' | h' <;>
              simp only [min_eq_left, min_eq_right, *] <;> linarith
            linarith
    · -- Case i' ≤ c: for i < c, brkLen(q + y) = brkLen(q) = 0; for i ≥ c, f i ≤ f c
      calc ∑ i ∈ Finset.Icc i' m, f i * (brkLen m f n i (q + y) - brkLen m f n i q)
          ≤ ∑ i ∈ Finset.Icc i' m, f c * (brkLen m f n i (q + y) - brkLen m f n i q) := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [Finset.mem_Icc] at hi
            by_cases hic : i < c
            · have hQ1 : q + y ≤ Q m f n (i + 1) :=
                le_trans hq_le (Q_anti m f n hm hf hfm hn (by omega) (by omega) (by omega))
              have hQ2 : q + y ≤ Q m f n i :=
                le_trans hq_le (Q_anti m f n hm hf hfm hn (by omega) (by omega) (by omega))
              have hbrk1 : brkLen m f n i (q + y) = 0 := by
                unfold brkLen
                rw [min_eq_left hQ2, min_eq_left hQ1, sub_self]
              have hbrk2 : brkLen m f n i q = 0 := by
                unfold brkLen
                rw [min_eq_left (by linarith), min_eq_left (by linarith), sub_self]
              rw [hbrk1, hbrk2, sub_self, mul_zero, mul_zero]
            · have hci : c ≤ i := by omega
              have hfi : f i ≤ f c := f_le_of_le m f hf hc1 hci hi.2
              have hbrk : 0 ≤ brkLen m f n i (q + y) - brkLen m f n i q :=
                sub_nonneg.mpr (brkLen_mono m f n hm hf hfm hn (by omega) hi.2 (by linarith))
              exact mul_le_mul_of_nonneg_right hfi hbrk
        _ = f c * ((min (q + y) (Q m f n i') - min (q + y) (Q m f n (m + 1))) -
              (min q (Q m f n i') - min q (Q m f n (m + 1)))) := by
            rw [← Finset.mul_sum, Finset.sum_sub_distrib,
              sum_brkLen_Icc m f n (q + y) i' m hi'm, sum_brkLen_Icc m f n q i' m hi'm]
        _ ≤ f c * y := by
            apply mul_le_mul_of_nonneg_left _ (f_pos m f hf hfm hc1 hcm).le
            have h1 : min (q + y) (Q m f n i') - min q (Q m f n i') ≤ y := by
              rcases le_total (q + y) (Q m f n i') with h | h <;>
              rcases le_total q (Q m f n i') with h' | h' <;>
              simp only [min_eq_left, min_eq_right, *] <;> linarith
            have h2 : min q (Q m f n (m + 1)) ≤ min (q + y) (Q m f n (m + 1)) := by
              rcases le_total (q + y) (Q m f n (m + 1)) with h | h <;>
              rcases le_total q (Q m f n (m + 1)) with h' | h' <;>
              simp only [min_eq_left, min_eq_right, *] <;> linarith
            linarith

lemma runFrom_orderQuantity_props (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {i' : ℕ} (hi'1 : 1 ≤ i') (hi'm : i' ≤ m) :
    ∀ (I : List Request) (past : List (Request × ℝ)),
      IsInstance m I →
      (∀ p ∈ past, 1 ≤ p.1.cls ∧ p.1.cls ≤ m ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1.qty) →
      (past.map Prod.snd).sum ≤ n →
      let final := runFrom n (orderQuantityPolicy m f n) past I
      (past.map Prod.snd).sum ≤ (final.map Prod.snd).sum ∧
      (∀ p ∈ final, p.2 < p.1.qty → p ∈ past ∨ Q m f n p.1.cls ≤ (final.map Prod.snd).sum) ∧
      V_tail m f n i' ((final.map Prod.snd).sum) +
        (final.map fun p => if p.1.cls < i' then (f p.1.cls - f i') * p.2 else 0).sum -
        (V_tail m f n i' ((past.map Prod.snd).sum) +
          (past.map fun p => if p.1.cls < i' then (f p.1.cls - f i') * p.2 else 0).sum) ≤
        (final.map fun p => f p.1.cls * p.2).sum - (past.map fun p => f p.1.cls * p.2).sum
  | [], past, _, _, _ => by
    simp only [runFrom]
    refine ⟨le_rfl, fun p hp _ => Or.inl hp, by linarith⟩
  | r :: rs, past, hI, hpast, hsum => by
    simp only [runFrom]
    have hr : 1 ≤ r.cls ∧ r.cls ≤ m ∧ 0 < r.qty := hI r List.mem_cons_self
    have hrs : IsInstance m rs := fun q hq => hI q (List.mem_cons_of_mem _ hq)
    set qhat := (past.map Prod.snd).sum
    have hq0 : 0 ≤ qhat :=
      List.sum_nonneg (by intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨p, hp, rfl⟩; exact (hpast p hp).2.2.1)
    have hy_eq := orderQuantityPolicy_step m f n hm hf hfm hn past r hq0 hsum hr
    set y := clip n qhat r (orderQuantityPolicy m f n past r)
    have hy0 : 0 ≤ y := le_max_left 0 _
    have hy_qty : y ≤ r.qty := by
      have hy_eq' : y = max 0 (min r.qty (Q m f n r.cls - qhat)) := hy_eq
      rw [hy_eq']
      exact max_le hr.2.2.le (min_le_left _ _)
    have hQr_le_n : Q m f n r.cls ≤ n := by
      have h := Q_anti m f n hm hf hfm hn le_rfl hr.1 (by omega)
      rw [Q_one] at h
      exact h
    have hy_Q : 0 < y → qhat + y ≤ Q m f n r.cls := by
      intro hy_pos
      have hy_eq' : y = max 0 (min r.qty (Q m f n r.cls - qhat)) := hy_eq
      rw [hy_eq'] at hy_pos ⊢
      have hmin_pos : 0 < min r.qty (Q m f n r.cls - qhat) := by
        by_contra hle
        rw [max_eq_left (not_lt.mp hle)] at hy_pos
        exact lt_irrefl 0 hy_pos
      rw [max_eq_right hmin_pos.le]
      have : min r.qty (Q m f n r.cls - qhat) ≤ Q m f n r.cls - qhat := min_le_right _ _
      linarith
    have hpast' : ∀ p ∈ past ++ [(r, y)], 1 ≤ p.1.cls ∧ p.1.cls ≤ m ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1.qty := by
      intro p hp
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact hpast p hp
      · exact ⟨hr.1, hr.2.1, hy0, hy_qty⟩
    have hsum_step : ((past ++ [(r, y)]).map Prod.snd).sum = qhat + y := by
      rw [List.map_append, List.sum_append]
      simp [qhat]
    have hsum' : ((past ++ [(r, y)]).map Prod.snd).sum ≤ n := by
      rw [hsum_step]
      rcases hy0.eq_or_lt with h0 | hpos
      · linarith
      · linarith [hy_Q hpos]
    obtain ⟨ih_mono, ih_rej, ih_V⟩ :=
      runFrom_orderQuantity_props m f n hm hf hfm hn hi'1 hi'm rs (past ++ [(r, y)]) hrs hpast' hsum'
    refine ⟨?_, ?_, ?_⟩
    · linarith [hsum_step, ih_mono]
    · intro p hp hlt
      rcases ih_rej p hp hlt with hp_in | hge
      · simp only [List.mem_append, List.mem_singleton] at hp_in
        rcases hp_in with hp_in | rfl
        · exact Or.inl hp_in
        · right
          change y < r.qty at hlt
          have hy_eq' : y = max 0 (min r.qty (Q m f n r.cls - qhat)) := hy_eq
          have hq_ge : Q m f n r.cls ≤ qhat + y := by
            rw [hy_eq'] at hlt ⊢
            have hmin_lt : min r.qty (Q m f n r.cls - qhat) < r.qty :=
              lt_of_le_of_lt (le_max_right _ _) hlt
            have hmin_eq : min r.qty (Q m f n r.cls - qhat) = Q m f n r.cls - qhat :=
              min_eq_right (le_of_not_ge fun hge => hmin_lt.not_ge (min_eq_left hge).ge)
            have : Q m f n r.cls - qhat ≤ max 0 (min r.qty (Q m f n r.cls - qhat)) := by
              rw [hmin_eq]; exact le_max_right _ _
            linarith
          change Q m f n r.cls ≤ _
          linarith [hsum_step, ih_mono]
      · exact Or.inr hge
    · have hV_step := V_tail_step_bound m f n hm hf hfm hn hi'1 hi'm hr.1 hr.2.1 hy0 hy_Q
      have hmap1 :
          ((past ++ [(r, y)]).map fun p => if p.1.cls < i' then (f p.1.cls - f i') * p.2 else 0).sum =
            (past.map fun p => if p.1.cls < i' then (f p.1.cls - f i') * p.2 else 0).sum +
              (if r.cls < i' then (f r.cls - f i') * y else 0) := by
        rw [List.map_append, List.sum_append]
        simp
      have hmap2 :
          ((past ++ [(r, y)]).map fun p => f p.1.cls * p.2).sum =
            (past.map fun p => f p.1.cls * p.2).sum + f r.cls * y := by
        rw [List.map_append, List.sum_append]
        simp
      rw [hsum_step, hmap1, hmap2] at ih_V
      have hstep_ineq :
          (V_tail m f n i' (qhat + y) - V_tail m f n i' qhat) +
            (if r.cls < i' then (f r.cls - f i') * y else 0) ≤ f r.cls * y := by
        split_ifs at hV_step ⊢ with hlt
        · linarith
        · linarith
      linarith

lemma orderQuantity_instance_bound (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {I : List Request} (hI : IsInstance m I) :
    1 / Delta m f * offlineOpt f n I ≤ revenue f n (orderQuantityPolicy m f n) I := by
  have hΔ_ge1 : 1 ≤ Delta m f := delta_ge_one m f hm hf hfm
  have hΔ_pos : 0 < Delta m f := delta_pos m f hm hf hfm
  have h1Δ_le1 : 1 / Delta m f ≤ 1 := (div_le_one hΔ_pos).mpr hΔ_ge1
  have h1Δ_pos : 0 < 1 / Delta m f := one_div_pos.mpr hΔ_pos
  set B := orderQuantityPolicy m f n
  set L := run n B I
  have hL_inv : (∀ p ∈ L, 1 ≤ p.1.cls ∧ p.1.cls ≤ m ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1.qty) ∧
      (L.map Prod.snd).sum ≤ n :=
    runFrom_inv m n B I [] hI (by simp) (by simp [hn.le])
  rcases all_full_or_min_rejected m L hL_inv.1 with hfull | ⟨i', hi'1, hi'm, ⟨p₀, hp₀_mem, hp₀_cls, hp₀_lt⟩, hfull_lt⟩
  · -- Case 1: all requests accepted in full
    have hrev_eq : revenue f n B I = (I.map fun r => f r.cls * r.qty).sum := by
      unfold revenue
      have hcongr : L.map (fun p => f p.1.cls * p.2) = L.map (fun p => f p.1.cls * p.1.qty) := by
        apply List.map_congr_left
        intro p hp
        rw [hfull p hp]
      rw [hcongr, map_fst_comp L (fun r => f r.cls * r.qty), run_map_fst]
    have hopt_le := offlineOpt_le_full m f n hf hfm hn hI
    have hopt_nonneg : 0 ≤ offlineOpt f n I := by
      unfold offlineOpt
      exact le_csSup_of_le (by
        refine ⟨(I.map fun r => f r.cls * r.qty).sum, ?_⟩
        rintro v ⟨x, hx1, _, rfl⟩
        rw [← sum_fin_eq_map_sum]
        refine Finset.sum_le_sum fun k _ => ?_
        have hr := hI (I.get k) (List.get_mem I k)
        exact mul_le_mul_of_nonneg_left (hx1 k).2 (f_pos m f hf hfm hr.1 hr.2.1).le)
        ⟨fun _ => 0, ⟨fun k => ⟨le_rfl, (hI (I.get k) (List.get_mem I k)).2.2.le⟩, by simp [hn.le], by simp⟩⟩
        le_rfl
    calc 1 / Delta m f * offlineOpt f n I
        ≤ 1 * offlineOpt f n I := mul_le_mul_of_nonneg_right h1Δ_le1 hopt_nonneg
      _ = offlineOpt f n I := one_mul _
      _ ≤ (I.map fun r => f r.cls * r.qty).sum := hopt_le
      _ = revenue f n B I := hrev_eq.symm
  · -- Case 2: some request of class i' not accepted in full
    obtain ⟨_, hL_rej, hL_V⟩ :=
      runFrom_orderQuantity_props m f n hm hf hfm hn hi'1 hi'm I [] hI (by simp) (by simp [hn.le])
    rcases hL_rej p₀ hp₀_mem hp₀_lt with hp₀_nil | hq_ge
    · simp at hp₀_nil
    · rw [hp₀_cls] at hq_ge
      have hV_final : V_tail m f n i' ((L.map Prod.snd).sum) = f i' * (n / Delta m f) :=
        V_tail_ge_Q m f n hm hf hfm hn hi'1 hi'm hq_ge
      have hV_zero : V_tail m f n i' 0 = 0 := V_tail_zero m f n hm hf hfm hn hi'1
      simp only [List.map_nil, List.sum_nil, hV_zero, add_zero, sub_zero] at hL_V
      have hhead_eq :
          (L.map fun p => if p.1.cls < i' then (f p.1.cls - f i') * p.2 else 0).sum =
            (I.map fun r => if r.cls < i' then (f r.cls - f i') * r.qty else 0).sum := by
        have hcongr :
            L.map (fun p => if p.1.cls < i' then (f p.1.cls - f i') * p.2 else 0) =
              L.map (fun p => if p.1.cls < i' then (f p.1.cls - f i') * p.1.qty else 0) := by
          apply List.map_congr_left
          intro p hp
          split_ifs with hlt
          · rw [hfull_lt p hp hlt]
          · rfl
        rw [hcongr, map_fst_comp L (fun r => if r.cls < i' then (f r.cls - f i') * r.qty else 0),
          run_map_fst]
      have hdiff_nonneg :
          0 ≤ (I.map fun r => if r.cls < i' then (f r.cls - f i') * r.qty else 0).sum := by
        apply List.sum_nonneg
        intro x hx
        rw [List.mem_map] at hx
        rcases hx with ⟨r, hr_mem, rfl⟩
        have hr := hI r hr_mem
        split_ifs with hlt
        · exact mul_nonneg (sub_nonneg.mpr (f_lt_of_lt m f hf hr.1 hlt hi'm).le) hr.2.2.le
        · exact le_rfl
      have hopt_le := offlineOpt_le_split m f n hf hfm hn hI hi'1 hi'm
      unfold revenue
      set S_diff := (I.map fun r => if r.cls < i' then (f r.cls - f i') * r.qty else 0).sum
      calc 1 / Delta m f * offlineOpt f n I
          ≤ 1 / Delta m f * (f i' * n + S_diff) :=
            mul_le_mul_of_nonneg_left hopt_le h1Δ_pos.le
        _ = f i' * (n / Delta m f) + 1 / Delta m f * S_diff := by ring
        _ ≤ f i' * (n / Delta m f) + 1 * S_diff := by
            linarith [mul_le_mul_of_nonneg_right h1Δ_le1 hdiff_nonneg]
        _ = V_tail m f n i' ((L.map Prod.snd).sum) +
              (L.map fun p => if p.1.cls < i' then (f p.1.cls - f i') * p.2 else 0).sum := by
            rw [one_mul, hV_final, hhead_eq]
        _ ≤ (L.map fun p => f p.1.cls * p.2).sum := hL_V

lemma cr_eq_of_instance_bound (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    (B : DetPolicy)
    (hB : ∀ {I : List Request}, IsInstance m I → 1 / Delta m f * offlineOpt f n I ≤ revenue f n B I) :
    competitiveRatio m f n B = 1 / Delta m f := by
  apply le_antisymm
  · let μ0 : Measure Unit := Measure.dirac ()
    have hprob : IsProbabilityMeasure μ0 := Measure.dirac.isProbabilityMeasure
    exact (theorem4_no_policy_exceeds m f n hm hf hfm hn μ0 (fun _ => B) (fun _ _ => measurable_const)).1 B
  · unfold competitiveRatio
    apply le_csInf
    · -- Nonempty: single request [⟨1, n⟩]
      let I0 : List Request := [⟨1, n⟩]
      have hI0 : IsInstance m I0 := by
        intro r hr
        simp only [I0, List.mem_singleton] at hr
        subst hr
        dsimp only
        exact ⟨le_rfl, by omega, hn⟩
      have hopt0 : 0 < offlineOpt f n I0 := by
        unfold offlineOpt
        have hf1 : 0 < f 1 := f_pos m f hf hfm le_rfl (by omega)
        apply lt_of_lt_of_le (mul_pos hf1 hn)
        apply le_csSup
        · refine ⟨f 1 * n, ?_⟩
          rintro v ⟨x, hx1, _, rfl⟩
          simp only [I0, List.length_singleton, Fin.sum_univ_one, List.get_eq_getElem] at hx1 ⊢
          exact mul_le_mul_of_nonneg_left (hx1 0).2 hf1.le
        · refine ⟨fun _ => n, ⟨fun k => ?_, ?_, ?_⟩⟩
          · simp [I0, hn.le]
          · simp [I0]
          · simp [I0]
      exact ⟨revenue f n B I0 / offlineOpt f n I0, I0, hI0, hopt0, rfl⟩
    · rintro c ⟨I, hI, hopt, rfl⟩
      rw [le_div_iff₀ hopt]
      exact hB hI

end Aux_RB_thm5

namespace RobustBooking.MultiFare

open Aux_RB_thm5

theorem theorem5_competitive_ratio (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n) :
    competitiveRatio m f n (protectionPolicy m f n) = 1 / Delta m f ∧
    competitiveRatio m f n (orderQuantityPolicy m f n) = 1 / Delta m f :=
  ⟨cr_eq_of_instance_bound m f n hm hf hfm hn (protectionPolicy m f n)
      (fun hI => protection_instance_bound m f n hm hf hfm hn hI),
   cr_eq_of_instance_bound m f n hm hf hfm hn (orderQuantityPolicy m f n)
      (fun hI => orderQuantity_instance_bound m f n hm hf hfm hn hI)⟩

end RobustBooking.MultiFare

open RobustBooking.MultiFare in
theorem solution (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n) :
    competitiveRatio m f n (protectionPolicy m f n) = 1 / Delta m f ∧
    competitiveRatio m f n (orderQuantityPolicy m f n) = 1 / Delta m f :=
  theorem5_competitive_ratio m f n hm hf hfm hn
