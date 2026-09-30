-- Prove2me | solution 1 for SchedulingAlgorithms.identical_pmtn_weighted_completion_nonpreemptive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:56:26.647317+00:00
-- url     : https://prove2.me/submissions/f108956f-af10-432c-9710-7f7b53e89462

import Mathlib
import Definitions.Def_SchedulingAlgorithms_ParallelMachines

namespace SchedulingAlgorithms
open Finset MeasureTheory

variable {n m : ℕ}

/-! ## Generic list helpers -/

lemma wc_list_sum_eq {α : Type*} (L : List α) (g : α → ℝ) :
    (L.map g).sum = ∑ i : Fin L.length, g (L.get i) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih]
    exact (Fin.sum_univ_succ (n := L.length) (fun i => g ((a :: L).get i))).symm

lemma wc_list_filter_sum {α : Type*} (L : List α) (p : α → Prop) [DecidablePred p] (f : α → ℝ) :
    ((L.filter (fun q => decide (p q))).map f).sum = (L.map (fun q => if p q then f q else 0)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => by_cases h : p a <;> simp [h, ih]

lemma wc_makespan_nonneg (S : PreemptiveSchedule n m) : 0 ≤ makespan S := by
  unfold makespan
  induction S with
  | nil => simp
  | cons a S ih => simp only [List.map_cons, List.foldr_cons]; exact le_max_of_le_right ih

lemma wc_stop_le (S : PreemptiveSchedule n m) : ∀ q ∈ S, q.stop ≤ makespan S := by
  unfold makespan
  induction S with
  | nil => simp
  | cons a S ih =>
    intro q hq
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp hq with rfl | hq
    · exact le_max_left _ _
    · exact le_max_of_le_right (ih q hq)

lemma wc_completion_nonneg (S : PreemptiveSchedule n m) (i : Fin n) : 0 ≤ completion S i := by
  unfold completion
  induction S with
  | nil => simp
  | cons a S ih =>
    by_cases h : a.job = i
    · simp only [List.filter_cons, h, decide_true, if_true, List.map_cons, List.foldr_cons]
      exact le_max_of_le_right ih
    · simpa [List.filter_cons, h] using ih

lemma wc_completion_le_makespan (S : PreemptiveSchedule n m) (i : Fin n) :
    completion S i ≤ makespan S := by
  unfold completion makespan
  induction S with
  | nil => simp
  | cons a S ih =>
    by_cases h : a.job = i
    · simp only [List.filter_cons, h, decide_true, if_true, List.map_cons, List.foldr_cons]
      exact max_le_max le_rfl ih
    · simp only [List.filter_cons, h, decide_false, List.map_cons, List.foldr_cons]
      simpa using le_max_of_le_right ih

lemma wc_stop_le_completion (S : PreemptiveSchedule n m) :
    ∀ q ∈ S, q.stop ≤ completion S q.job := by
  intro q hq
  unfold completion
  induction S with
  | nil => simp at hq
  | cons a S ih =>
    rcases List.mem_cons.mp hq with rfl | hq'
    · simp
    · by_cases h : a.job = q.job
      · simp only [List.filter_cons, h, decide_true, if_true, List.map_cons, List.foldr_cons]
        exact le_max_of_le_right (ih hq')
      · simpa [List.filter_cons, h] using ih hq'

/-! ## Compact list schedules -/

/-- Start time of job `i` in the compact list schedule: machine `a i`, jobs on a machine in
increasing `r`-order, no idle time. -/
def listStart (p : Fin n → ℝ) (a : Fin n → Fin m) (r : Fin n → Fin n) (i : Fin n) : ℝ :=
  ∑ j ∈ univ.filter (fun j => a j = a i ∧ r j < r i), p j

def listPiece (p : Fin n → ℝ) (a : Fin n → Fin m) (r : Fin n → Fin n) (i : Fin n) :
    Piece n m :=
  ⟨i, a i, listStart p a r i, listStart p a r i + p i⟩

def listSchedule (p : Fin n → ℝ) (a : Fin n → Fin m) (r : Fin n → Fin n) :
    PreemptiveSchedule n m :=
  (List.finRange n).map (listPiece p a r)

lemma finRange_filter_eq (i : Fin n) :
    (List.finRange n).filter (fun k => decide (k = i)) = [i] := by
  rw [List.filter_eq, List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange i)]
  rfl

lemma listSchedule_filter (p : Fin n → ℝ) (a : Fin n → Fin m) (r : Fin n → Fin n) (i : Fin n) :
    (listSchedule p a r).filter (fun q => decide (q.job = i)) = [listPiece p a r i] := by
  unfold listSchedule
  rw [List.filter_map]
  have : ((fun q : Piece n m => decide (q.job = i)) ∘ listPiece p a r) =
      fun k => decide (k = i) := by
    funext k; simp only [Function.comp_apply, listPiece]; exact decide_eq_decide.mpr Iff.rfl
  rw [this, finRange_filter_eq]
  rfl

lemma listStart_nonneg (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (a : Fin n → Fin m)
    (r : Fin n → Fin n) (i : Fin n) : 0 ≤ listStart p a r i :=
  sum_nonneg fun j _ => hp j

lemma listStart_add_le (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (a : Fin n → Fin m)
    (r : Fin n → Fin n) {i j : Fin n} (ha : a i = a j) (hr : r i < r j) :
    listStart p a r i + p i ≤ listStart p a r j := by
  unfold listStart
  have hnot : i ∉ univ.filter (fun k => a k = a i ∧ r k < r i) := by simp
  rw [add_comm, ← sum_insert hnot]
  apply sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [mem_insert, mem_filter, mem_univ, true_and] at hk ⊢
    rcases hk with rfl | ⟨h1, h2⟩
    · exact ⟨ha, hr⟩
    · exact ⟨h1.trans ha, h2.trans hr⟩
  · intro k _ _; exact hp k

lemma listSchedule_nonpreemptive (p : Fin n → ℝ) (a : Fin n → Fin m) (r : Fin n → Fin n) :
    Nonpreemptive (listSchedule p a r) := by
  intro i
  rw [listSchedule_filter]
  rfl

lemma completion_listSchedule (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (a : Fin n → Fin m)
    (r : Fin n → Fin n) (i : Fin n) :
    completion (listSchedule p a r) i = listStart p a r i + p i := by
  unfold completion
  rw [listSchedule_filter]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, listPiece]
  exact max_eq_left (add_nonneg (listStart_nonneg p hp a r i) (hp i))

lemma listSchedule_feasible (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) (a : Fin n → Fin m)
    (r : Fin n → Fin n) (hr : Function.Injective r) :
    IsFeasible (fun _ => 1) p (listSchedule p a r) := by
  have hp0 : ∀ i, 0 ≤ p i := fun i => (hp i).le
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    simp only [listSchedule, List.mem_map] at hq
    obtain ⟨i, -, rfl⟩ := hq
    exact ⟨listStart_nonneg p hp0 a r i, by simp [listPiece, hp0 i]⟩
  · unfold listSchedule
    rw [List.pairwise_map]
    refine (List.nodup_finRange n).imp ?_
    intro i j hij h
    have hm : a i = a j := by
      rcases h with h | h
      · exact h
      · exact absurd h hij
    rcases lt_trichotomy (r i) (r j) with hlt | heq | hgt
    · left; exact listStart_add_le p hp0 a r hm hlt
    · exact absurd (hr heq) hij
    · right; exact listStart_add_le p hp0 a r hm.symm hgt
  · intro i
    unfold work
    rw [listSchedule_filter]
    simp [listPiece]

/-- Suffix weight of `j` on its machine (dual variable `y_j`). -/
def sufW (w : Fin n → ℝ) (a : Fin n → Fin m) (r : Fin n → Fin n) (j : Fin n) : ℝ :=
  ∑ i ∈ univ.filter (fun i => a i = a j ∧ r j ≤ r i), w i

lemma cost_listSchedule (p w : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (a : Fin n → Fin m)
    (r : Fin n → Fin n) (hr : Function.Injective r) :
    totalWeightedCompletionOf w (listSchedule p a r) = ∑ j, p j * sufW w a r j := by
  unfold totalWeightedCompletionOf
  have hsplit : ∀ i, listStart p a r i + p i =
      ∑ j ∈ univ.filter (fun j => a j = a i ∧ r j ≤ r i), p j := by
    intro i
    unfold listStart
    have hnot : i ∉ univ.filter (fun k => a k = a i ∧ r k < r i) := by simp
    rw [add_comm, ← sum_insert hnot]
    congr 1
    ext k
    simp only [mem_insert, mem_filter, mem_univ, true_and]
    constructor
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨rfl, le_rfl⟩
      · exact ⟨h1, h2.le⟩
    · rintro ⟨h1, h2⟩
      rcases h2.lt_or_eq with h2 | h2
      · exact Or.inr ⟨h1, h2⟩
      · exact Or.inl (hr h2)
  calc ∑ i, w i * completion (listSchedule p a r) i
      = ∑ i, ∑ j, if (a j = a i ∧ r j ≤ r i) then w i * p j else 0 := by
        refine sum_congr rfl fun i _ => ?_
        rw [completion_listSchedule p hp, hsplit, mul_sum, sum_filter]
    _ = ∑ j, ∑ i, if (a j = a i ∧ r j ≤ r i) then w i * p j else 0 := sum_comm
    _ = ∑ j, p j * sufW w a r j := by
        refine sum_congr rfl fun j _ => ?_
        unfold sufW
        rw [mul_sum, sum_filter]
        refine sum_congr rfl fun i _ => ?_
        by_cases h : a i = a j ∧ r j ≤ r i
        · rw [if_pos ⟨h.1.symm, h.2⟩, if_pos h]; ring
        · rw [if_neg (fun h' => h ⟨h'.1.symm, h'.2⟩), if_neg h]

/-! ## Reverse greedy assignment -/

/-- Reverse-greedy property: when `j` was inserted (at the front), its machine was a lightest
machine with respect to the jobs of larger rank. -/
def GreedyProp (w : Fin n → ℝ) (a : Fin n → Fin m) (r : Fin n → Fin n) : Prop :=
  ∀ j μ, ∑ i ∈ univ.filter (fun i => a i = a j ∧ r j < r i), w i ≤
    ∑ i ∈ univ.filter (fun i => a i = μ ∧ r j < r i), w i

lemma sum_filter_fin_succ {N : ℕ} (P : Fin (N + 1) → Prop) [DecidablePred P] (f : Fin (N + 1) → ℝ) :
    ∑ t ∈ univ.filter P, f t =
      (if P 0 then f 0 else 0) + ∑ t ∈ univ.filter (fun t : Fin N => P t.succ), f t.succ := by
  rw [sum_filter, Fin.sum_univ_succ, sum_filter]

lemma exists_greedy_rank (hm : 0 < m) : ∀ (N : ℕ) (v : Fin N → ℝ), ∃ b : Fin N → Fin m,
    ∀ s μ, ∑ t ∈ univ.filter (fun t => b t = b s ∧ s < t), v t ≤
      ∑ t ∈ univ.filter (fun t => b t = μ ∧ s < t), v t := by
  intro N
  induction N with
  | zero => intro v; exact ⟨fun s => s.elim0, fun s => s.elim0⟩
  | succ N ih =>
    intro v
    obtain ⟨b', hb'⟩ := ih (fun s => v s.succ)
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    obtain ⟨μ₀, -, hμ₀⟩ := exists_min_image univ
      (fun μ => ∑ t ∈ univ.filter (fun t => b' t = μ), v t.succ) univ_nonempty
    refine ⟨Fin.cons μ₀ b', ?_⟩
    intro s μ
    refine Fin.cases ?_ (fun s' => ?_) s
    · rw [sum_filter_fin_succ, sum_filter_fin_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, lt_irrefl, and_false, if_false, zero_add,
        Fin.succ_pos, and_true]
      exact hμ₀ μ (mem_univ _)
    · rw [sum_filter_fin_succ, sum_filter_fin_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_lt_succ_iff, zero_add,
        (Fin.succ_pos s').not_gt, and_false, if_false]
      exact hb' s' μ

lemma exists_greedy (hm : 0 < m) (w : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    ∃ a : Fin n → Fin m, GreedyProp w a σ.symm := by
  obtain ⟨b, hb⟩ := exists_greedy_rank hm n (fun t => w (σ t))
  refine ⟨fun i => b (σ.symm i), ?_⟩
  intro j μ
  have key : ∀ (P : Fin n → Prop) [DecidablePred P],
      ∑ i ∈ univ.filter P, w i = ∑ t ∈ univ.filter (fun t => P (σ t)), w (σ t) := by
    intro P _
    rw [sum_filter, sum_filter]
    exact (Equiv.sum_comp σ (fun i => if P i then w i else 0)).symm
  rw [key, key]
  simpa only [Equiv.symm_apply_apply] using hb (σ.symm j) μ

/-! ## Dual feasibility of the suffix weights -/

lemma dual_feasible (hm : 0 < m) (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (a : Fin n → Fin m)
    (r : Fin n → Fin n) (hr : Function.Injective r) (hG : GreedyProp w a r)
    (U : Finset (Fin n)) (hU : ∀ i ∈ U, ∀ j, r i ≤ r j → j ∈ U)
    (J : Finset (Fin n)) (hJU : J ⊆ U) (hJm : J.card ≤ m) :
    ∑ j ∈ J, sufW w a r j ≤ ∑ i ∈ U, w i := by
  classical
  set V : Fin m → ℝ := fun μ => ∑ i ∈ U.filter (fun i => a i = μ), w i with hV
  have hV0 : ∀ μ, 0 ≤ V μ := fun μ => sum_nonneg fun i _ => hw i
  have hVsum : ∑ μ, V μ = ∑ i ∈ U, w i := sum_fiberwise U a w
  set F := J.filter (fun j => ∀ i ∈ U, a i = a j → r j ≤ r i) with hF
  -- first jobs: suffix weight equals machine weight
  have hFirst : ∀ j ∈ F, sufW w a r j = V (a j) := by
    intro j hj
    simp only [hF, mem_filter] at hj
    unfold sufW
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨hU j (hJU hj.1) i h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, hj.2 i h1 h2⟩
  -- other jobs: suffix weight at most every machine weight
  have hOther : ∀ j ∈ J \ F, ∀ μ, sufW w a r j ≤ V μ := by
    intro j hj μ
    simp only [hF, mem_sdiff, mem_filter, not_and, not_forall, not_le] at hj
    obtain ⟨i₀, hi₀U, hi₀a, hi₀r⟩ := hj.2 hj.1
    unfold sufW
    calc ∑ i ∈ univ.filter (fun i => a i = a j ∧ r j ≤ r i), w i
        ≤ ∑ i ∈ univ.filter (fun i => a i = a i₀ ∧ r i₀ < r i), w i := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro i hi
            simp only [mem_filter, mem_univ, true_and] at hi ⊢
            exact ⟨hi.1.trans hi₀a.symm, hi₀r.trans_le hi.2⟩
          · intro i _ _; exact hw i
      _ ≤ ∑ i ∈ univ.filter (fun i => a i = μ ∧ r i₀ < r i), w i := hG i₀ μ
      _ ≤ V μ := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro i hi
            simp only [mem_filter, mem_univ, true_and] at hi ⊢
            exact ⟨hU i₀ hi₀U i hi.2.le, hi.1⟩
          · intro i _ _; exact hw i
  have hinj : Set.InjOn a F := by
    intro j hj j' hj' h
    simp only [hF, coe_filter, Set.mem_ofPred_eq] at hj hj'
    exact hr (le_antisymm (hj.2 j' (hJU hj'.1) h.symm) (hj'.2 j (hJU hj.1) h))
  have hsplit := sum_sdiff (f := sufW w a r) (filter_subset (fun j => ∀ i ∈ U, a i = a j → r j ≤ r i) J)
  rw [← hF] at hsplit
  have hFsum : ∑ j ∈ F, sufW w a r j = ∑ μ ∈ F.image a, V μ := by
    rw [sum_image hinj]
    exact sum_congr rfl hFirst
  have hcardF : (F.image a).card = F.card := card_image_of_injOn hinj
  have hrest : ∑ j ∈ J \ F, sufW w a r j ≤ ∑ μ ∈ univ \ F.image a, V μ := by
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    obtain ⟨μ₀, -, hμ₀⟩ := exists_min_image univ V univ_nonempty
    have hFJ : F ⊆ J := filter_subset _ J
    have hc1 : (J \ F).card ≤ (univ \ F.image a).card := by
      rw [card_sdiff_of_subset hFJ, card_sdiff_of_subset (subset_univ _),
        card_univ, Fintype.card_fin, hcardF]
      have := card_le_card hFJ
      omega
    calc ∑ j ∈ J \ F, sufW w a r j ≤ (J \ F).card • V μ₀ :=
          sum_le_card_nsmul _ _ _ fun j hj => hOther j hj μ₀
      _ ≤ (univ \ F.image a).card • V μ₀ := by
          rw [nsmul_eq_mul, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc1) (hV0 μ₀)
      _ ≤ ∑ μ ∈ univ \ F.image a, V μ :=
          card_nsmul_le_sum _ _ _ fun μ _ => hμ₀ μ (mem_univ _)
  have htot := sum_sdiff (f := V) (subset_univ (F.image a))
  linarith

/-! ## Weak duality -/

lemma weak_duality (p w : Fin n → ℝ) (S : PreemptiveSchedule n m)
    (hS : IsFeasible (fun _ => 1) p S) (y : Fin n → ℝ)
    (hy : ∀ t : ℝ, ∀ J : Finset (Fin n), J ⊆ univ.filter (fun j => t < completion S j) →
      J.card ≤ m → ∑ j ∈ J, y j ≤ ∑ j ∈ univ.filter (fun j => t < completion S j), w j) :
    ∑ j, p j * y j ≤ totalWeightedCompletionOf w S := by
  classical
  obtain ⟨hpos, hpw, hwork⟩ := hS
  set T := makespan S with hT
  have hT0 : 0 ≤ T := wc_makespan_nonneg S
  set e : Fin S.length → Piece n m := S.get
  have hmem : ∀ x, e x ∈ S := fun x => List.get_mem S x
  have hL : ∑ j, p j * y j = ∑ x, y (e x).job * ((e x).stop - (e x).start) := by
    have hp : ∀ j, p j = ∑ x, if (e x).job = j then ((e x).stop - (e x).start) else 0 := by
      intro j
      rw [← hwork j]
      unfold work
      rw [wc_list_filter_sum S (fun q => q.job = j) (fun q => 1 * (q.stop - q.start)),
        wc_list_sum_eq]
      simp [e]
    simp_rw [hp, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    simp only [ite_mul, zero_mul]
    rw [sum_ite_eq]
    simp only [mem_univ, if_true]
    ring
  set μ : Measure ℝ := volume.restrict (Set.Icc 0 T)
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩; simp [μ, Real.volume_Icc]
  set F : Fin S.length → ℝ → ℝ := fun x t =>
    (Set.Ico (e x).start (e x).stop).indicator (fun _ => y (e x).job) t
  set G : Fin n → ℝ → ℝ := fun j t =>
    (Set.Ico 0 (completion S j)).indicator (fun _ => w j) t
  have hFint : ∀ x, Integrable (F x) μ := fun x => (integrable_const _).indicator measurableSet_Ico
  have hGint : ∀ j, Integrable (G j) μ := fun j => (integrable_const _).indicator measurableSet_Ico
  have hFval : ∀ x, ∫ t, F x t ∂μ = y (e x).job * ((e x).stop - (e x).start) := by
    intro x
    simp only [F]
    rw [integral_indicator_const _ measurableSet_Ico, Measure.real, Measure.restrict_apply
      measurableSet_Ico]
    have hsub : Set.Ico (e x).start (e x).stop ⊆ Set.Icc 0 T := fun t ht =>
      ⟨(hpos _ (hmem x)).1.trans ht.1, ht.2.le.trans (wc_stop_le S _ (hmem x))⟩
    rw [Set.inter_eq_left.mpr hsub, Real.volume_Ico, ENNReal.toReal_ofReal
      (by linarith [(hpos _ (hmem x)).2]), smul_eq_mul]
    ring
  have hGval : ∀ j, ∫ t, G j t ∂μ = w j * completion S j := by
    intro j
    simp only [G]
    rw [integral_indicator_const _ measurableSet_Ico, Measure.real, Measure.restrict_apply
      measurableSet_Ico]
    have hsub : Set.Ico 0 (completion S j) ⊆ Set.Icc 0 T := fun t ht =>
      ⟨ht.1, ht.2.le.trans (wc_completion_le_makespan S j)⟩
    rw [Set.inter_eq_left.mpr hsub, Real.volume_Ico, sub_zero,
      ENNReal.toReal_ofReal (wc_completion_nonneg S j), smul_eq_mul]
    ring
  have hpt : ∀ t, ∑ x, F x t ≤ ∑ j, G j t := by
    intro t
    by_cases ht : 0 ≤ t
    · have hG : ∑ j, G j t = ∑ j ∈ univ.filter (fun j => t < completion S j), w j := by
        rw [sum_filter]
        refine sum_congr rfl fun j _ => ?_
        simp only [G, Set.indicator_apply, Set.mem_Ico, ht, true_and]
      set I := univ.filter (fun x => t ∈ Set.Ico (e x).start (e x).stop)
      have hFI : ∑ x, F x t = ∑ x ∈ I, y (e x).job := by
        rw [sum_filter]
        refine sum_congr rfl fun x _ => ?_
        simp only [F, Set.indicator_apply]
      have hsep : ∀ x ∈ I, ∀ z ∈ I,
          ((e x).machine = (e z).machine ∨ (e x).job = (e z).job) → x = z := by
        intro x hx z hz hxz
        simp only [I, mem_filter, mem_univ, true_and, Set.mem_Ico] at hx hz
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have := List.pairwise_iff_get.mp hpw x z hlt hxz
          rcases this with h | h <;> linarith [hx.1, hx.2, hz.1, hz.2]
        · have := List.pairwise_iff_get.mp hpw z x hlt (hxz.imp Eq.symm Eq.symm)
          rcases this with h | h <;> linarith [hx.1, hx.2, hz.1, hz.2]
      have hinjM : Set.InjOn (fun x => (e x).machine) I :=
        fun x hx z hz h => hsep x hx z hz (Or.inl h)
      have hinjJ : Set.InjOn (fun x => (e x).job) I :=
        fun x hx z hz h => hsep x hx z hz (Or.inr h)
      rw [hFI, hG, ← sum_image hinjJ]
      apply hy
      · intro j hj
        simp only [mem_image] at hj
        obtain ⟨x, hx, rfl⟩ := hj
        simp only [I, mem_filter, mem_univ, true_and, Set.mem_Ico] at hx
        simp only [mem_filter, mem_univ, true_and]
        exact lt_of_lt_of_le hx.2 (wc_stop_le_completion S _ (hmem x))
      · rw [card_image_of_injOn hinjJ, ← card_image_of_injOn hinjM]
        exact (card_le_univ _).trans (by simp)
    · have h1 : ∀ x, F x t = 0 := by
        intro x
        simp only [F]
        exact Set.indicator_of_notMem (fun h => ht ((hpos _ (hmem x)).1.trans h.1)) _
      have h2 : ∀ j, G j t = 0 := by
        intro j
        simp only [G]
        exact Set.indicator_of_notMem (fun h => ht h.1) _
      simp [h1, h2]
  calc ∑ j, p j * y j = ∑ x, y (e x).job * ((e x).stop - (e x).start) := hL
    _ = ∑ x, ∫ t, F x t ∂μ := by simp_rw [hFval]
    _ = ∫ t, ∑ x, F x t ∂μ := (integral_finsetSum _ fun x _ => hFint x).symm
    _ ≤ ∫ t, ∑ j, G j t ∂μ :=
        integral_mono (integrable_finsetSum _ fun x _ => hFint x)
          (integrable_finsetSum _ fun j _ => hGint j) hpt
    _ = ∑ j, ∫ t, G j t ∂μ := integral_finsetSum _ fun j _ => hGint j
    _ = totalWeightedCompletionOf w S := by
        simp_rw [hGval]; rfl

/-! ## Assembly -/

lemma listSchedule_le (hm : 0 < m) (p w : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hw : ∀ i, 0 ≤ w i)
    (S : PreemptiveSchedule n m) (hS : IsFeasible (fun _ => 1) p S)
    (σ : Equiv.Perm (Fin n)) (hσ : Monotone (completion S ∘ σ))
    (a : Fin n → Fin m) (ha : GreedyProp w a σ.symm) :
    totalWeightedCompletionOf w (listSchedule p a σ.symm) ≤ totalWeightedCompletionOf w S := by
  rw [cost_listSchedule p w (fun i => (hp i).le) a σ.symm σ.symm.injective]
  refine weak_duality p w S hS _ ?_
  intro t J hJ hJm
  refine dual_feasible hm w hw a σ.symm σ.symm.injective ha _ ?_ J hJ hJm
  intro i hi j hij
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  have := hσ hij
  simp only [Function.comp, Equiv.apply_symm_apply] at this
  linarith

theorem wc_main {n m : ℕ} (hm : 0 < m)
    (p w : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hw : ∀ i, 0 ≤ w i) :
    ∃ S : PreemptiveSchedule n m, IsFeasible (fun _ => 1) p S ∧ Nonpreemptive S ∧
      ∀ S' : PreemptiveSchedule n m, IsFeasible (fun _ => 1) p S' →
        totalWeightedCompletionOf w S ≤ totalWeightedCompletionOf w S' := by
  classical
  let A : Equiv.Perm (Fin n) → Fin n → Fin m := fun σ => Classical.choose (exists_greedy hm w σ)
  have hA : ∀ σ, GreedyProp w (A σ) σ.symm := fun σ => Classical.choose_spec (exists_greedy hm w σ)
  let F : Equiv.Perm (Fin n) → PreemptiveSchedule n m := fun σ => listSchedule p (A σ) σ.symm
  obtain ⟨σ₀, -, hσ₀⟩ := exists_min_image (univ : Finset (Equiv.Perm (Fin n)))
    (fun σ => totalWeightedCompletionOf w (F σ)) univ_nonempty
  refine ⟨F σ₀, listSchedule_feasible p hp _ _ σ₀.symm.injective,
    listSchedule_nonpreemptive p _ _, fun S' hS' => ?_⟩
  let σ' := Tuple.sort (completion S')
  calc totalWeightedCompletionOf w (F σ₀) ≤ totalWeightedCompletionOf w (F σ') :=
        hσ₀ σ' (mem_univ _)
    _ ≤ totalWeightedCompletionOf w S' :=
        listSchedule_le hm p w hp hw S' hS' σ' (Tuple.monotone_sort _) _ (hA σ')

end SchedulingAlgorithms

open SchedulingAlgorithms

theorem solution {n m : ℕ} (hm : 0 < m)
    (p w : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hw : ∀ i, 0 ≤ w i) :
    ∃ S : PreemptiveSchedule n m, IsFeasible (fun _ => 1) p S ∧ Nonpreemptive S ∧
      ∀ S' : PreemptiveSchedule n m, IsFeasible (fun _ => 1) p S' →
        totalWeightedCompletionOf w S ≤ totalWeightedCompletionOf w S' :=
  wc_main hm p w hp hw

