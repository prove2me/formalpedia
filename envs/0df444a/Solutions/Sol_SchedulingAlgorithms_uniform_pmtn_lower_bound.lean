-- Prove2me | solution 1 for SchedulingAlgorithms.uniform_pmtn_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T22:54:00.220357+00:00
-- url     : https://prove2.me/submissions/324c17d6-adab-4704-825f-a2907acfb7dd

import Mathlib
import Definitions.Def_SchedulingAlgorithms_ParallelMachines

namespace SchedulingAlgorithms

open Finset MeasureTheory

lemma sa_card_fin_lt (m c : ℕ) (h : c ≤ m) :
    (Finset.univ.filter (fun j : Fin m => (j : ℕ) < c)).card = c := by
  have : (Finset.univ.filter (fun j : Fin m => (j : ℕ) < c)).image Fin.val = Finset.range c := by
    ext r
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hr; exact ⟨⟨r, by omega⟩, hr, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, this, Finset.card_range]

lemma sa_list_sum_eq {α : Type*} (L : List α) (g : α → ℝ) :
    (L.map g).sum = ∑ i : Fin L.length, g (L.get i) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih]
    exact (Fin.sum_univ_succ (n := L.length) (fun i => g ((a :: L).get i))).symm

lemma sa_list_filter_sum {α : Type*} (L : List α) (p : α → Prop) [DecidablePred p] (f : α → ℝ) :
    ((L.filter (fun q => decide (p q))).map f).sum = (L.map (fun q => if p q then f q else 0)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => by_cases h : p a <;> simp [h, ih]

/-- `∑_P f ≤ ∑_Q f` when `|P| ≤ |Q|`, every value on `P` is at most every value on `Q`,
and the values on `P` are nonnegative. -/
lemma sa_sum_exchange {ι : Type*} (P Q : Finset ι) (f : ι → ℝ) (hcard : P.card ≤ Q.card)
    (hle : ∀ i ∈ P, ∀ w ∈ Q, f i ≤ f w) (hnn : ∀ i ∈ P, 0 ≤ f i) (hQ : ∀ w ∈ Q, 0 ≤ f w) :
    ∑ i ∈ P, f i ≤ ∑ w ∈ Q, f w := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · simpa using sum_nonneg hQ
  · obtain ⟨i0, hi0, hmax⟩ := exists_max_image P f hP
    calc ∑ i ∈ P, f i ≤ P.card • f i0 := sum_le_card_nsmul P f (f i0) hmax
      _ ≤ Q.card • f i0 := by
          rw [nsmul_eq_mul, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hnn i0 hi0)
      _ ≤ ∑ w ∈ Q, f w := card_nsmul_le_sum Q f (f i0) (fun w hw => hle i0 hi0 w hw)

variable {n m : ℕ}

/-- Any `≤ k` machines have total speed at most that of the `k` fastest. -/
lemma sa_top_sum (s : Fin m → ℝ) (hs0 : ∀ j, 0 ≤ s j) (hsa : Antitone s) (M : Finset (Fin m))
    (k : ℕ) (hMk : M.card ≤ k) (hk : k ≤ m) : ∑ j ∈ M, s j ≤ prefixSum s k := by
  classical
  set F := Finset.univ.filter (fun j : Fin m => (j : ℕ) < M.card) with hF
  have hFc : F.card = M.card := sa_card_fin_lt m M.card (hMk.trans hk)
  have h1 : ∑ j ∈ M, s j ≤ ∑ j ∈ F, s j := by
    have hsplitM := sum_sdiff (s₁ := M ∩ F) (s₂ := M) (f := s) inter_subset_left
    have hsplitF := sum_sdiff (s₁ := M ∩ F) (s₂ := F) (f := s) inter_subset_right
    have e1 : M \ (M ∩ F) = M \ F := by ext; simp
    have e2 : F \ (M ∩ F) = F \ M := by ext; simp
    rw [e1] at hsplitM; rw [e2] at hsplitF
    have hc1 := card_sdiff_add_card_inter M F
    have hc2 := card_sdiff_add_card_inter F M
    rw [inter_comm] at hc2
    have hex := sa_sum_exchange (M \ F) (F \ M) s (by omega)
      (fun i hi w hw => by
        simp only [mem_sdiff, hF, mem_filter, mem_univ, true_and, not_lt] at hi hw
        exact hsa (Fin.le_def.mpr (by omega)))
      (fun i _ => hs0 i) (fun w _ => hs0 w)
    linarith
  have h2 : ∑ j ∈ F, s j ≤ prefixSum s k := by
    unfold prefixSum
    apply sum_le_sum_of_subset_of_nonneg
    · intro j hj
      simp only [hF, mem_filter, mem_univ, true_and] at hj ⊢
      omega
    · intro j _ _; exact hs0 j
  linarith

lemma sa_makespan_nonneg (S : PreemptiveSchedule n m) : 0 ≤ makespan S := by
  unfold makespan
  induction S with
  | nil => simp
  | cons a S ih => simp only [List.map_cons, List.foldr_cons]; exact le_max_of_le_right ih

lemma sa_stop_le (S : PreemptiveSchedule n m) : ∀ q ∈ S, q.stop ≤ makespan S := by
  unfold makespan
  induction S with
  | nil => simp
  | cons a S ih =>
    intro q hq
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp hq with rfl | hq
    · exact le_max_left _ _
    · exact le_max_of_le_right (ih q hq)

/-- The key work bound: the jobs of `A` receive at most `C_max · S_k` units of work, where
`k ≥ min(|A|, m)`. -/
lemma sa_work_bound (s : Fin m → ℝ) (hs0 : ∀ j, 0 ≤ s j) (hsa : Antitone s)
    (S : PreemptiveSchedule n m) (hpos : ∀ q ∈ S, 0 ≤ q.start ∧ q.start ≤ q.stop)
    (hpw : S.Pairwise (fun a b => (a.machine = b.machine ∨ a.job = b.job) → Piece.Disjoint a b))
    (A : Finset (Fin n)) (k : ℕ) (hk1 : min A.card m ≤ k) (hkm : k ≤ m) :
    ∑ i ∈ A, work s S i ≤ makespan S * prefixSum s k := by
  classical
  set T := makespan S with hT
  have hT0 : 0 ≤ T := sa_makespan_nonneg S
  set e : Fin S.length → Piece n m := S.get
  have hmem : ∀ x, e x ∈ S := fun x => List.get_mem S x
  set f : Piece n m → ℝ := fun q => s q.machine * (q.stop - q.start)
  have hwork : ∀ i, work s S i = ∑ x, if (e x).job = i then f (e x) else 0 := by
    intro i
    unfold work
    rw [sa_list_filter_sum S (fun q => q.job = i) f, sa_list_sum_eq]
  have hsum : ∑ i ∈ A, work s S i = ∑ x, if (e x).job ∈ A then f (e x) else 0 := by
    simp_rw [hwork]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_ite_eq]
  rw [hsum]
  set μ : Measure ℝ := volume.restrict (Set.Icc 0 T)
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩; simp [μ, Real.volume_Icc]
  set F : Fin S.length → ℝ → ℝ := fun x t =>
    if (e x).job ∈ A then (Set.Ico (e x).start (e x).stop).indicator (fun _ => s (e x).machine) t
    else 0
  have hFint : ∀ x, Integrable (F x) μ := by
    intro x
    simp only [F]
    split_ifs
    · exact (integrable_const _).indicator measurableSet_Ico
    · exact integrable_const _
  have hFval : ∀ x, ∫ t, F x t ∂μ = if (e x).job ∈ A then f (e x) else 0 := by
    intro x
    simp only [F]
    split_ifs
    · rw [integral_indicator_const _ measurableSet_Ico, Measure.real, Measure.restrict_apply
        measurableSet_Ico]
      have hsub : Set.Ico (e x).start (e x).stop ⊆ Set.Icc 0 T := fun t ht =>
        ⟨(hpos _ (hmem x)).1.trans ht.1, ht.2.le.trans (sa_stop_le S _ (hmem x))⟩
      rw [Set.inter_eq_left.mpr hsub, Real.volume_Ico, ENNReal.toReal_ofReal
        (by linarith [(hpos _ (hmem x)).2]), smul_eq_mul]
      simp only [f]; ring
    · simp
  -- pointwise bound
  have hpt : ∀ t, ∑ x, F x t ≤ prefixSum s k := by
    intro t
    set I := Finset.univ.filter (fun x => (e x).job ∈ A ∧ t ∈ Set.Ico (e x).start (e x).stop)
    have hFI : ∑ x, F x t = ∑ x ∈ I, s (e x).machine := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x => (e x).job ∈ A ∧ t ∈ Set.Ico (e x).start (e x).stop)]
      have h0 : ∑ x ∈ Finset.univ.filter
          (fun x => ¬ ((e x).job ∈ A ∧ t ∈ Set.Ico (e x).start (e x).stop)), F x t = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        simp only [mem_filter, mem_univ, true_and, not_and] at hx
        simp only [F]
        split_ifs with hA
        · exact Set.indicator_of_notMem (hx hA) _
        · rfl
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := (Finset.mem_filter.mp hx).2
      simp only [F, if_pos hx'.1, Set.indicator_of_mem hx'.2]
    -- two active pieces share neither machine nor job
    have hsep : ∀ x ∈ I, ∀ y ∈ I, ((e x).machine = (e y).machine ∨ (e x).job = (e y).job) → x = y := by
      intro x hx y hy hxy
      simp only [I, mem_filter, mem_univ, true_and, Set.mem_Ico] at hx hy
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := List.pairwise_iff_get.mp hpw x y hlt hxy
        rcases this with h | h <;> linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]
      · have := List.pairwise_iff_get.mp hpw y x hlt (hxy.imp Eq.symm Eq.symm)
        rcases this with h | h <;> linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]
    have hinjM : Set.InjOn (fun x => (e x).machine) I := fun x hx y hy h => hsep x hx y hy (Or.inl h)
    have hinjJ : Set.InjOn (fun x => (e x).job) I := fun x hx y hy h => hsep x hx y hy (Or.inr h)
    rw [hFI, ← Finset.sum_image hinjM]
    apply sa_top_sum s hs0 hsa _ k _ hkm
    rw [Finset.card_image_of_injOn hinjM]
    have hA : I.card ≤ A.card := by
      apply Finset.card_le_card_of_injOn (fun x => (e x).job)
      · intro x hx; exact (mem_filter.mp hx).2.1
      · exact hinjJ
    have hm : I.card ≤ m := by
      rw [← Finset.card_image_of_injOn hinjM]
      exact (Finset.card_le_univ _).trans (by simp)
    exact (le_min hA hm).trans hk1
  calc ∑ x, (if (e x).job ∈ A then f (e x) else 0) = ∑ x, ∫ t, F x t ∂μ := by
        simp_rw [hFval]
    _ = ∫ t, ∑ x, F x t ∂μ := (integral_finsetSum _ fun x _ => hFint x).symm
    _ ≤ ∫ _t, prefixSum s k ∂μ :=
        integral_mono (integrable_finsetSum _ fun x _ => hFint x) (integrable_const _) hpt
    _ = T * prefixSum s k := by
        rw [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ,
          Set.univ_inter, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
        ring

end SchedulingAlgorithms

namespace SchedulingAlgorithms

open Finset

lemma sa_prefix_pos {m : ℕ} (s : Fin m → ℝ) (hs : ∀ j, 0 < s j) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    0 < prefixSum s j := by
  unfold prefixSum
  apply sum_pos (fun i _ => hs i)
  exact ⟨⟨0, by omega⟩, by simp only [mem_filter, mem_univ, true_and]; omega⟩

theorem ulb_main {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (s : Fin m → ℝ) (hs : ∀ j, 0 < s j) (hs' : Antitone s)
    (p : Fin n → ℝ) (S : PreemptiveSchedule n m) (hS : IsFeasible s p S) :
    levelBound s p ≤ makespan S := by
  classical
  have hs0 : ∀ j, 0 ≤ s j := fun j => (hs j).le
  have hbound : ∀ (A : Finset (Fin n)) (k : ℕ), min A.card m ≤ k → k ≤ m →
      ∑ i ∈ A, p i ≤ makespan S * prefixSum s k := by
    intro A k hk1 hkm
    have := sa_work_bound s hs0 hs' S hS.1 hS.2.1 A k hk1 hkm
    simp_rw [hS.2.2] at this
    exact this
  unfold levelBound
  apply Finset.max'_le
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · have hPn : prefixSum p n = ∑ i ∈ (univ : Finset (Fin n)), p i := by
      unfold prefixSum; congr 1; ext i; simp
    rw [div_le_iff₀ (sa_prefix_pos s hs m hm le_rfl), hPn]
    exact hbound univ m (min_le_right _ _) le_rfl
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hj1, hjm⟩ := Finset.mem_Ico.mp hj
    set A := univ.filter (fun i : Fin n => (i : ℕ) < j)
    have hA : A.card = j := sa_card_fin_lt n j (by omega)
    rw [div_le_iff₀ (sa_prefix_pos s hs j hj1 hjm.le)]
    exact hbound A j (by rw [hA]; exact min_le_left _ _) hjm.le

end SchedulingAlgorithms

open SchedulingAlgorithms

theorem solution {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (s : Fin m → ℝ) (hs : ∀ j, 0 < s j) (hs' : Antitone s)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hp' : Antitone p)
    (S : PreemptiveSchedule n m) (hS : IsFeasible s p S) :
    levelBound s p ≤ makespan S :=
  ulb_main hm hmn s hs hs' p S hS
