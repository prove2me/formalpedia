-- Prove2me | solution 1 for SchedulingAlgorithms.uniform_pmtn_feasible_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T00:32:25.333223+00:00
-- url     : https://prove2.me/submissions/d5f21335-67c9-4555-8aa6-4d80bf821c39

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


namespace SchedulingAlgorithms

open Finset

lemma sa_flatMap_sum {α β : Type*} (l : List α) (f : α → List β) (g : β → ℝ) :
    ((l.flatMap f).map g).sum = (l.map (fun a => ((f a).map g).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

lemma sa_finRange_sum {n : ℕ} (f : Fin n → ℝ) : ((List.finRange n).map f).sum = ∑ i, f i := by
  rw [← List.ofFn_eq_map, List.sum_ofFn]

lemma sa_makespan_le {n m : ℕ} (S : PreemptiveSchedule n m) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ q ∈ S, q.stop ≤ B) : makespan S ≤ B := by
  unfold makespan
  induction S with
  | nil => simpa using hB
  | cons a S ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h a (List.mem_cons_self ..)) (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

lemma bv_filterMap_sum {α β : Type*} (l : List α) (f : α → Option β) (g : β → ℝ) :
    ((l.filterMap f).map g).sum = (l.map (fun a => ((f a).map g).getD 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.filterMap_cons]
    cases h : f a <;> simp [h, ih]

lemma bv_take_mono (l : List ℝ) (hl : ∀ x ∈ l, 0 ≤ x) {k k' : ℕ} (h : k ≤ k') :
    (l.take k).sum ≤ (l.take k').sum := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.sum_append]
  have : 0 ≤ ((l.drop k).take d).sum :=
    List.sum_nonneg fun x hx => hl x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  linarith

section BV
variable {n m : ℕ}

/-- The time matrix padded to a square matrix with all row and column sums `T`. -/
noncomputable def bvY (T : ℝ) (X : Fin n → Fin m → ℝ) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ
  | Sum.inl i, Sum.inl i' => if i = i' then T - ∑ j, X i j else 0
  | Sum.inl i, Sum.inr j => X i j
  | Sum.inr j, Sum.inl i => X i j
  | Sum.inr j, Sum.inr j' => if j = j' then T - ∑ i, X i j else 0

lemma bvY_ds (T : ℝ) (hT : 0 < T) (X : Fin n → Fin m → ℝ) (hX0 : ∀ i j, 0 ≤ X i j)
    (hrow : ∀ i, ∑ j, X i j ≤ T) (hcol : ∀ j, ∑ i, X i j ≤ T) :
    T⁻¹ • bvY T X ∈ doublyStochastic ℝ (Fin n ⊕ Fin m) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun a b => ?_, fun a => ?_, fun b => ?_⟩
  · simp only [Matrix.smul_apply, smul_eq_mul]
    refine mul_nonneg (inv_nonneg.mpr hT.le) ?_
    rcases a with i | j <;> rcases b with i' | j' <;> simp only [bvY]
    · split_ifs
      · linarith [hrow i]
      · exact le_rfl
    · exact hX0 i j'
    · exact hX0 i' j
    · split_ifs
      · linarith [hcol j]
      · exact le_rfl
  · simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, Fintype.sum_sum_type]
    rcases a with i | j <;> simp only [bvY]
    · rw [Finset.sum_ite_eq]; simp only [mem_univ, if_true]; field_simp; ring
    · rw [Finset.sum_ite_eq]; simp only [mem_univ, if_true]; field_simp; ring
  · simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, Fintype.sum_sum_type]
    rcases b with i | j <;> simp only [bvY]
    · rw [Finset.sum_ite_eq']; simp only [mem_univ, if_true]; field_simp; ring
    · rw [Finset.sum_ite_eq']; simp only [mem_univ, if_true]; field_simp; ring


/-- The pieces of one time slot `[a, b)` for the permutation `σ`: job `i` runs on machine `j`
whenever `σ` sends `inl i` to `inr j`. -/
def bvSlot (σ : Equiv.Perm (Fin n ⊕ Fin m)) (a b : ℝ) : List (Piece n m) :=
  (List.finRange n).filterMap
    (fun i => (σ (Sum.inl i)).getRight?.map (fun j => (⟨i, j, a, b⟩ : Piece n m)))

lemma bv_mem_slot {σ : Equiv.Perm (Fin n ⊕ Fin m)} {a b : ℝ} {q : Piece n m}
    (hq : q ∈ bvSlot σ a b) : ∃ i j, σ (Sum.inl i) = Sum.inr j ∧ q = ⟨i, j, a, b⟩ := by
  unfold bvSlot at hq
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hq
  cases hσ : σ (Sum.inl i) with
  | inl i' => simp [hσ] at hi
  | inr j =>
    simp only [hσ, Sum.getRight?_inr, Option.map_some, Option.some.injEq] at hi
    exact ⟨i, j, hσ, hi.symm⟩

lemma bv_slot_pairwise (σ : Equiv.Perm (Fin n ⊕ Fin m)) (a b : ℝ) :
    (bvSlot σ a b).Pairwise
      (fun x y => (x.machine = y.machine ∨ x.job = y.job) → Piece.Disjoint x y) := by
  unfold bvSlot
  refine List.Pairwise.filterMap _ (fun i i' hne x hx y hy => ?_) (List.nodup_finRange n)
  cases hσ : σ (Sum.inl i) with
  | inl _ => simp [hσ] at hx
  | inr j =>
    cases hσ' : σ (Sum.inl i') with
    | inl _ => simp [hσ'] at hy
    | inr j' =>
      simp only [hσ, hσ', Sum.getRight?_inr, Option.map_some, Option.some.injEq] at hx hy
      subst hx hy
      rintro (h | h)
      · exfalso
        have : σ (Sum.inl i) = σ (Sum.inl i') := by rw [hσ, hσ']; simp only at h; rw [h]
        exact hne (Sum.inl_injective (σ.injective this))
      · exact absurd h hne

/-- The schedule: the permutations in a fixed order, the `k`-th one occupying the time slot
`[T w₀ + ⋯ + T w_{k-1}, T w₀ + ⋯ + T w_k)`. -/
noncomputable def bvSched (T : ℝ) (L : List (Equiv.Perm (Fin n ⊕ Fin m)))
    (w : Equiv.Perm (Fin n ⊕ Fin m) → ℝ) : PreemptiveSchedule n m :=
  (List.finRange L.length).flatMap (fun k => bvSlot (L.get k)
    (T * ((L.map w).take k).sum) (T * ((L.map w).take (k + 1)).sum))

lemma bv_slot_value (σ : Equiv.Perm (Fin n ⊕ Fin m)) (a b : ℝ) (s : Fin m → ℝ) (i : Fin n) :
    ((bvSlot σ a b).map (fun q => if q.job = i then s q.machine * (q.stop - q.start) else 0)).sum
      = ∑ j, if σ (Sum.inl i) = Sum.inr j then s j * (b - a) else 0 := by
  unfold bvSlot
  rw [bv_filterMap_sum, sa_finRange_sum, Finset.sum_eq_single i]
  · cases hσ : σ (Sum.inl i) with
    | inl _ => simp [hσ]
    | inr j0 =>
      simp only [Option.map_some, Sum.getRight?_inr, Option.getD_some, if_true, Sum.inr.injEq]
      rw [Finset.sum_ite_eq]
      simp
  · intro i' _ hi'
    cases hσ : σ (Sum.inl i') with
    | inl _ => simp [hσ]
    | inr j0 => simp [hσ, hi']
  · simp

theorem bv_exists (s : Fin m → ℝ) (T : ℝ) (hT : 0 < T) (X : Fin n → Fin m → ℝ)
    (hX0 : ∀ i j, 0 ≤ X i j) (hrow : ∀ i, ∑ j, X i j ≤ T) (hcol : ∀ j, ∑ i, X i j ≤ T) :
    ∃ S : PreemptiveSchedule n m, (∀ q ∈ S, 0 ≤ q.start ∧ q.start ≤ q.stop) ∧
      S.Pairwise (fun a b => (a.machine = b.machine ∨ a.job = b.job) → Piece.Disjoint a b) ∧
      (∀ i, work s S i = ∑ j, s j * X i j) ∧ makespan S ≤ T := by
  obtain ⟨w, hw0, hw1, hwM⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic (bvY_ds T hT X hX0 hrow hcol)
  set L := (Finset.univ : Finset (Equiv.Perm (Fin n ⊕ Fin m))).toList with hL
  have hwsnn : ∀ x ∈ L.map w, 0 ≤ x := by
    intro x hx
    obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx
    exact hw0 σ
  have hwsum : (L.map w).sum = 1 := by rw [hL, Finset.sum_map_toList]; exact hw1
  have hlen : (L.map w).length = L.length := List.length_map _
  have hcw : ∀ k : Fin L.length,
      ((L.map w).take (k + 1)).sum - ((L.map w).take k).sum = w (L.get k) := by
    intro k
    rw [List.sum_take_succ (L.map w) k (by rw [hlen]; exact k.isLt)]
    simp
  have hentry : ∀ i j, ∑ σ, w σ * (if σ (Sum.inl i) = Sum.inr j then 1 else 0) = T⁻¹ * X i j := by
    intro i j
    have h := congrFun (congrFun hwM (Sum.inl i)) (Sum.inr j)
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq] at h
    rw [h]
    rfl
  refine ⟨bvSched T L w, ?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hq
    obtain ⟨i, j, -, rfl⟩ := bv_mem_slot hk
    refine ⟨mul_nonneg hT.le (List.sum_nonneg fun x hx => hwsnn x (List.mem_of_mem_take hx)), ?_⟩
    exact mul_le_mul_of_nonneg_left (bv_take_mono (L.map w) hwsnn (Nat.le_succ _)) hT.le
  · unfold bvSched
    rw [List.pairwise_flatMap]
    refine ⟨fun k _ => bv_slot_pairwise _ _ _, ?_⟩
    refine (List.pairwise_lt_finRange L.length).imp fun {k k'} hkk' x hx y hy _ => ?_
    obtain ⟨i, j, -, rfl⟩ := bv_mem_slot hx
    obtain ⟨i', j', -, rfl⟩ := bv_mem_slot hy
    left
    exact mul_le_mul_of_nonneg_left (bv_take_mono (L.map w) hwsnn (Nat.succ_le_of_lt hkk')) hT.le
  · intro i
    unfold work bvSched
    rw [sa_list_filter_sum, sa_flatMap_sum, sa_finRange_sum]
    simp_rw [bv_slot_value]
    have e1 : ∀ k : Fin L.length, T * ((L.map w).take (k + 1)).sum - T * ((L.map w).take k).sum =
        T * w (L.get k) := by
      intro k; rw [← mul_sub, hcw k]
    simp_rw [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e2 : ∑ k : Fin L.length, (if (L.get k) (Sum.inl i) = Sum.inr j then
        s j * (T * w (L.get k)) else 0) =
        s j * T * ∑ σ, w σ * (if σ (Sum.inl i) = Sum.inr j then 1 else 0) := by
      have : ∑ k : Fin L.length, (if (L.get k) (Sum.inl i) = Sum.inr j then
          s j * (T * w (L.get k)) else 0) =
          (L.map fun σ => if σ (Sum.inl i) = Sum.inr j then s j * (T * w σ) else 0).sum :=
        (sa_list_sum_eq L (fun σ => if σ (Sum.inl i) = Sum.inr j then s j * (T * w σ) else 0)).symm
      rw [this, hL, Finset.sum_map_toList, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      split_ifs <;> ring
    rw [e2, hentry]
    field_simp
  · refine sa_makespan_le _ T hT.le fun q hq => ?_
    obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hq
    obtain ⟨i, j, -, rfl⟩ := bv_mem_slot hk
    show T * ((L.map w).take (k + 1)).sum ≤ T
    have : ((L.map w).take (k + 1)).sum ≤ (L.map w).sum := by
      have := bv_take_mono (L.map w) hwsnn
        (show (k : ℕ) + 1 ≤ (L.map w).length by rw [hlen]; exact k.isLt)
      rwa [List.take_length] at this
    rw [hwsum] at this
    nlinarith

end BV


section QP
variable {m : ℕ}

/-- The speed of an abstract machine that uses real machine `k` a fraction `w k` of the time. -/
def qpSpeed (s : Fin m → ℝ) (w : Fin m → ℝ) : ℝ := ∑ k, w k * s k

/-- Place a job of size `p` on the list of abstract machines: on the first two consecutive
abstract machines `a, b` with `T σ(b) ≤ p ≤ T σ(a)` (or the last one), and merge their leftovers. -/
noncomputable def qpPlace (s : Fin m → ℝ) (T p : ℝ) :
    List (Fin m → ℝ) → (Fin m → ℝ) × List (Fin m → ℝ)
  | [] => (0, [])
  | [a] => ((p / qpSpeed s a) • a, [((T - p / qpSpeed s a) / T) • a])
  | a :: b :: rest =>
      if T * qpSpeed s b ≤ p then
        let α := if qpSpeed s b < qpSpeed s a then
          (p - T * qpSpeed s b) / (qpSpeed s a - qpSpeed s b) else T
        (α • a + (T - α) • b, (((T - α) / T) • a + (α / T) • b) :: rest)
      else ((qpPlace s T p (b :: rest)).1, a :: (qpPlace s T p (b :: rest)).2)

/-- Admissible abstract machines: nonnegative weights summing to at most `1`. -/
def qpOK (w : Fin m → ℝ) : Prop := (∀ k, 0 ≤ w k) ∧ ∑ k, w k ≤ 1

lemma qpSpeed_nonneg (s : Fin m → ℝ) (hs : ∀ k, 0 < s k) {w : Fin m → ℝ} (hw : qpOK w) :
    0 ≤ qpSpeed s w :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hw.1 k) (hs k).le

lemma qpSpeed_smul (s : Fin m → ℝ) (c : ℝ) (w : Fin m → ℝ) :
    qpSpeed s (c • w) = c * qpSpeed s w := by
  unfold qpSpeed; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma qpSpeed_add (s : Fin m → ℝ) (v w : Fin m → ℝ) :
    qpSpeed s (v + w) = qpSpeed s v + qpSpeed s w := by
  unfold qpSpeed; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply]; ring

/-- The properties of one placement. -/
theorem qp_place (s : Fin m → ℝ) (hs : ∀ k, 0 < s k) (T p : ℝ) (hT : 0 < T) (hp : 0 < p) :
    ∀ ms : List (Fin m → ℝ), ms ≠ [] → (∀ c ∈ ms, qpOK c) →
      p ≤ T * qpSpeed s (ms.head!) →
      let r := qpPlace s T p ms
      (∀ k, 0 ≤ r.1 k) ∧ ∑ k, r.1 k ≤ T ∧ qpSpeed s r.1 = p ∧ r.2 ≠ [] ∧
        (∀ c ∈ r.2, qpOK c) ∧
        (∀ k, r.1 k + T * (r.2.map (· k)).sum = T * (ms.map (· k)).sum) ∧
        (∀ K : ℕ, min (K * p) (T * ((ms.map (qpSpeed s)).take (K + 1)).sum - p) ≤
          T * ((r.2.map (qpSpeed s)).take K).sum) := by
  intro ms
  induction ms with
  | nil => intro h; exact absurd rfl h
  | cons a tl ih =>
    intro _ hok hpa
    have hokA : qpOK a := hok a (List.mem_cons_self ..)
    simp only [List.head!_cons] at hpa
    have hσa := qpSpeed_nonneg s hs hokA
    cases tl with
    | nil =>
      -- the last abstract machine
      have hσpos : 0 < qpSpeed s a := by
        by_contra h
        have : qpSpeed s a = 0 := le_antisymm (not_lt.mp h) hσa
        rw [this, mul_zero] at hpa; linarith
      set α := p / qpSpeed s a with hα
      have hα0 : 0 ≤ α := div_nonneg hp.le hσpos.le
      have hαT : α ≤ T := by rw [hα, div_le_iff₀ hσpos]; linarith
      have hαs : α * qpSpeed s a = p := by rw [hα]; field_simp
      simp only [qpPlace]
      refine ⟨fun k => ?_, ?_, ?_, List.cons_ne_nil _ _, ?_, fun k => ?_, fun K => ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hα0 (hokA.1 k)
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [← Finset.mul_sum]
        nlinarith [hokA.2]
      · rw [qpSpeed_smul, hαs]
      · intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        have hc0 : 0 ≤ (T - α) / T := div_nonneg (by linarith) hT.le
        have hc1 : (T - α) / T ≤ 1 := by rw [div_le_one hT]; linarith
        refine ⟨fun k => ?_, ?_⟩
        · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hc0 (hokA.1 k)
        · simp only [Pi.smul_apply, smul_eq_mul]
          rw [← Finset.mul_sum]
          nlinarith [hokA.2, Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => hokA.1 k]
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
      · rcases K with _ | K
        · simp only [Nat.cast_zero, zero_mul, List.take_zero, List.sum_nil, mul_zero]
          exact min_le_left _ _
        · simp only [List.map_cons, List.map_nil, List.take_succ_cons, List.take_nil,
            List.sum_cons, List.sum_nil, add_zero]
          rw [qpSpeed_smul]
          have : T * ((T - α) / T * qpSpeed s a) = T * qpSpeed s a - p := by
            field_simp; rw [← hαs]; ring
          rw [this]
          exact min_le_right _ _
    | cons b rest =>
      have hokB : qpOK b := hok b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hσb := qpSpeed_nonneg s hs hokB
      by_cases hcase : T * qpSpeed s b ≤ p
      · -- merge `a` and `b`
        set α := (if qpSpeed s b < qpSpeed s a then
          (p - T * qpSpeed s b) / (qpSpeed s a - qpSpeed s b) else T) with hα
        have hαbounds : 0 ≤ α ∧ α ≤ T ∧ α * qpSpeed s a + (T - α) * qpSpeed s b = p := by
          rw [hα]
          split_ifs with hlt
          · have hd : 0 < qpSpeed s a - qpSpeed s b := by linarith
            refine ⟨div_nonneg (by linarith) hd.le, ?_, ?_⟩
            · rw [div_le_iff₀ hd]; linarith
            · field_simp; ring
          · refine ⟨hT.le, le_rfl, ?_⟩
            push Not at hlt
            nlinarith
        obtain ⟨hα0, hαT, hwork⟩ := hαbounds
        have hq : qpPlace s T p (a :: b :: rest) =
            (α • a + (T - α) • b, (((T - α) / T) • a + (α / T) • b) :: rest) := by
          simp only [qpPlace, if_pos hcase]
          rw [hα]
        rw [hq]
        have hc0 : 0 ≤ (T - α) / T := div_nonneg (by linarith) hT.le
        have hc0' : 0 ≤ α / T := div_nonneg hα0 hT.le
        refine ⟨fun k => ?_, ?_, ?_, List.cons_ne_nil _ _, ?_, fun k => ?_, fun K => ?_⟩
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          exact add_nonneg (mul_nonneg hα0 (hokA.1 k)) (mul_nonneg (by linarith) (hokB.1 k))
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          nlinarith [hokA.2, hokB.2]
        · rw [qpSpeed_add, qpSpeed_smul, qpSpeed_smul, hwork]
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · refine ⟨fun k => ?_, ?_⟩
            · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              exact add_nonneg (mul_nonneg hc0 (hokA.1 k)) (mul_nonneg hc0' (hokB.1 k))
            · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
              have h1 : (T - α) / T + α / T = 1 := by field_simp; ring
              nlinarith [hokA.2, hokB.2]
          · exact hok c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))
        · simp only [List.map_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          field_simp
          ring
        · rcases K with _ | K
          · simp only [Nat.cast_zero, zero_mul, List.take_zero, List.sum_nil, mul_zero]
            exact min_le_left _ _
          · simp only [List.map_cons, List.take_succ_cons, List.sum_cons]
            rw [qpSpeed_add, qpSpeed_smul, qpSpeed_smul]
            have : T * ((T - α) / T * qpSpeed s a + α / T * qpSpeed s b +
                ((rest.map (qpSpeed s)).take K).sum) =
                T * (qpSpeed s a + (qpSpeed s b + ((rest.map (qpSpeed s)).take K).sum)) - p := by
              field_simp; rw [← hwork]; ring
            rw [this]
            exact min_le_right _ _
      · -- recurse
        push Not at hcase
        have hne : (b :: rest) ≠ [] := List.cons_ne_nil _ _
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih hne
          (fun c hc => hok c (List.mem_cons_of_mem _ hc)) (by simp only [List.head!_cons]; linarith)
        have hq : qpPlace s T p (a :: b :: rest) =
            ((qpPlace s T p (b :: rest)).1, a :: (qpPlace s T p (b :: rest)).2) := by
          simp only [qpPlace, if_neg (not_le.mpr hcase)]
        rw [hq]
        refine ⟨h1, h2, h3, List.cons_ne_nil _ _, ?_, fun k => ?_, fun K => ?_⟩
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hokA
          · exact h5 c hc
        · simp only [List.map_cons, List.sum_cons]
          have := h6 k
          simp only [List.map_cons, List.sum_cons] at this
          linarith
        · rcases K with _ | K
          · simp only [Nat.cast_zero, zero_mul, List.take_zero, List.sum_nil, mul_zero]
            exact min_le_left _ _
          · have hK := h7 K
            simp only [List.map_cons, List.take_succ_cons, List.sum_cons] at hK ⊢
            push_cast
            rcases min_choice ((K : ℝ) * p) (T * (qpSpeed s b +
                ((rest.map (qpSpeed s)).take K).sum) - p) with hm | hm
            · rw [hm] at hK
              have := min_le_left (((K : ℝ) + 1) * p) (T * (qpSpeed s a + (qpSpeed s b +
                ((rest.map (qpSpeed s)).take K).sum)) - p)
              nlinarith
            · rw [hm] at hK
              have := min_le_right (((K : ℝ) + 1) * p) (T * (qpSpeed s a + (qpSpeed s b +
                ((rest.map (qpSpeed s)).take K).sum)) - p)
              nlinarith


/-- Place the jobs one after another. -/
noncomputable def qpBuild (s : Fin m → ℝ) (T : ℝ) :
    List ℝ → List (Fin m → ℝ) → List (Fin m → ℝ)
  | [], _ => []
  | p :: ps, ms => (qpPlace s T p ms).1 :: qpBuild s T ps (qpPlace s T p ms).2

theorem qp_build (s : Fin m → ℝ) (hs : ∀ k, 0 < s k) (T : ℝ) (hT : 0 < T) :
    ∀ (js : List ℝ) (ms : List (Fin m → ℝ)), (∀ x ∈ js, 0 < x) → js.Pairwise (· ≥ ·) →
      ms ≠ [] → (∀ c ∈ ms, qpOK c) →
      (∀ K : ℕ, (js.take K).sum ≤ T * ((ms.map (qpSpeed s)).take K).sum) →
      (∀ r ∈ qpBuild s T js ms, (∀ k, 0 ≤ r k) ∧ ∑ k, r k ≤ T) ∧
      (qpBuild s T js ms).map (qpSpeed s) = js ∧
      (∀ k, ((qpBuild s T js ms).map (· k)).sum ≤ T * (ms.map (· k)).sum) := by
  intro js
  induction js with
  | nil =>
    intro ms _ _ _ hok _
    refine ⟨by simp [qpBuild], by simp [qpBuild], fun k => ?_⟩
    simp only [qpBuild, List.map_nil, List.sum_nil]
    exact mul_nonneg hT.le (List.sum_nonneg fun x hx => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx; exact (hok c hc).1 k)
  | cons p ps ih =>
    intro ms hpos hsorted hne hok hcond
    have hp : 0 < p := hpos p (List.mem_cons_self ..)
    obtain ⟨hle, hps⟩ := List.pairwise_cons.mp hsorted
    have hhead : p ≤ T * qpSpeed s ms.head! := by
      have := hcond 1
      cases ms with
      | nil => exact absurd rfl hne
      | cons c cs => simpa using this
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := qp_place s hs T p hT hp ms hne hok hhead
    have hcond' : ∀ K : ℕ, (ps.take K).sum ≤
        T * (((qpPlace s T p ms).2.map (qpSpeed s)).take K).sum := by
      intro K
      refine le_trans (le_min ?_ ?_) (h7 K)
      · have hb := List.sum_le_card_nsmul (ps.take K) p
          (fun x hx => hle x (List.mem_of_mem_take hx))
        have hlen : ((ps.take K).length : ℝ) ≤ K := by
          exact_mod_cast (List.length_take_le K ps)
        rw [nsmul_eq_mul] at hb
        nlinarith
      · have := hcond (K + 1)
        simp only [List.take_succ_cons, List.sum_cons] at this
        linarith
    obtain ⟨i1, i2, i3⟩ := ih (qpPlace s T p ms).2 (fun x hx => hpos x (List.mem_cons_of_mem _ hx))
      hps h4 h5 hcond'
    refine ⟨?_, ?_, fun k => ?_⟩
    · intro r hr
      simp only [qpBuild, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨h1, h2⟩
      · exact i1 r hr
    · simp only [qpBuild, List.map_cons, h3, i2]
    · simp only [qpBuild, List.map_cons, List.sum_cons]
      have := h6 k
      have := i3 k
      linarith

lemma qp_list_ofFn {α : Type*} {n : ℕ} (l : List α) (h : l.length = n) :
    ∃ g : Fin n → α, l = List.ofFn g := by
  subst h; exact ⟨l.get, (List.ofFn_get l).symm⟩

lemma qp_take_ofFn {n : ℕ} (f : Fin n → ℝ) (K : ℕ) :
    ((List.ofFn f).take K).sum = prefixSum f K := by
  unfold prefixSum
  induction K with
  | zero => simp
  | succ K ih =>
    by_cases hK : K < n
    · rw [List.sum_take_succ _ _ (by simpa using hK), ih]
      have : univ.filter (fun k : Fin n => (k : ℕ) < K + 1)
          = insert ⟨K, hK⟩ (univ.filter (fun k : Fin n => (k : ℕ) < K)) := by
        ext k
        simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
        omega
      rw [this, sum_insert (by simp), add_comm]
      simp
    · push Not at hK
      rw [List.take_of_length_le (by simp; omega)] at *
      rw [ih]
      congr 1
      ext k
      simp only [mem_filter, mem_univ, true_and]
      omega

lemma qpSpeed_single (s : Fin m → ℝ) (k : Fin m) : qpSpeed s (Pi.single k 1) = s k := by
  unfold qpSpeed
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

/-- **Step 1**: a time matrix. -/
theorem qp_matrix {n : ℕ} (hm : 0 < m) (s : Fin m → ℝ) (hs : ∀ k, 0 < s k)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hp' : Antitone p) (T : ℝ) (hT : 0 < T)
    (hcond : ∀ K : ℕ, prefixSum p K ≤ T * prefixSum s K) :
    ∃ X : Fin n → Fin m → ℝ, (∀ i j, 0 ≤ X i j) ∧ (∀ i, ∑ j, X i j ≤ T) ∧
      (∀ j, ∑ i, X i j ≤ T) ∧ ∀ i, ∑ j, s j * X i j = p i := by
  set ms0 : List (Fin m → ℝ) := List.ofFn (fun k : Fin m => Pi.single k (1 : ℝ)) with hms0
  have hne : ms0 ≠ [] := by
    rw [hms0]; intro h
    have := congrArg List.length h
    simp at this; omega
  have hok : ∀ c ∈ ms0, qpOK c := by
    intro c hc
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hc
    refine ⟨fun k' => ?_, ?_⟩
    · simp only [Pi.single_apply]; split_ifs <;> norm_num
    · rw [Finset.sum_pi_single']; simp
  have hσ : ms0.map (qpSpeed s) = List.ofFn s := by
    rw [hms0, List.map_ofFn]
    congr 1
    funext k
    exact qpSpeed_single s k
  have hcol0 : ∀ j, (ms0.map (· j)).sum = 1 := by
    intro j
    rw [hms0, List.map_ofFn, List.sum_ofFn]
    simp [Pi.single_apply]
  obtain ⟨i1, i2, i3⟩ := qp_build s hs T hT (List.ofFn p) ms0
    (fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact hp i)
    (List.pairwise_ofFn.mpr fun i j hij => hp' hij.le) hne hok
    (fun K => by rw [hσ, qp_take_ofFn, qp_take_ofFn]; exact hcond K)
  have hlen : (qpBuild s T (List.ofFn p) ms0).length = n := by
    have := congrArg List.length i2
    simpa using this
  obtain ⟨g, hg⟩ := qp_list_ofFn _ hlen
  rw [hg] at i1 i2 i3
  refine ⟨g, fun i j => (i1 (g i) (List.mem_ofFn.mpr ⟨i, rfl⟩)).1 j,
    fun i => (i1 (g i) (List.mem_ofFn.mpr ⟨i, rfl⟩)).2, fun j => ?_, fun i => ?_⟩
  · have := i3 j
    rw [List.map_ofFn, List.sum_ofFn, hcol0 j, mul_one] at this
    exact this
  · rw [List.map_ofFn] at i2
    have := congrFun (List.ofFn_injective i2) i
    simp only [Function.comp] at this
    rw [← this]
    unfold qpSpeed
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end QP


section UP

lemma up_prefix_mono {k : ℕ} (f : Fin k → ℝ) (hf : ∀ i, 0 ≤ f i) {a b : ℕ} (h : a ≤ b) :
    prefixSum f a ≤ prefixSum f b :=
  sum_le_sum_of_subset_of_nonneg
    (fun i hi => by simp only [mem_filter, mem_univ, true_and] at hi ⊢; omega) (fun i _ _ => hf i)

/-- A feasible schedule within `T` from the prefix conditions. -/
theorem up_construct {n m : ℕ} (hm : 0 < m) (s : Fin m → ℝ) (hs : ∀ j, 0 < s j)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hp' : Antitone p) (T : ℝ) (hT : 0 < T)
    (hcond : ∀ K : ℕ, prefixSum p K ≤ T * prefixSum s K) :
    ∃ S : PreemptiveSchedule n m, IsFeasible s p S ∧ makespan S ≤ T := by
  obtain ⟨X, hX0, hrow, hcol, hwork⟩ := qp_matrix hm s hs p hp hp' T hT hcond
  obtain ⟨S, h1, h2, h3, h4⟩ := bv_exists s T hT X hX0 hrow hcol
  exact ⟨S, ⟨h1, h2, fun i => (h3 i).trans (hwork i)⟩, h4⟩

end UP


theorem up_feasible_iff {n m : ℕ} (hm : 0 < m) (s : Fin m → ℝ) (hs : ∀ j, 0 < s j)
    (hs' : Antitone s) (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hp' : Antitone p)
    (T : ℝ) (hT : 0 ≤ T) :
    (∃ S : PreemptiveSchedule n m, IsFeasible s p S ∧ makespan S ≤ T) ↔
      ∀ A : Finset (Fin n), ∑ i ∈ A, p i ≤ T * speedCapacity s A := by
  have hs0 : ∀ j, 0 ≤ s j := fun j => (hs j).le
  constructor
  · rintro ⟨S, hS, hST⟩ A
    have hw := sa_work_bound s hs0 hs' S hS.1 hS.2.1 A (min A.card m) le_rfl (min_le_right _ _)
    simp_rw [hS.2.2] at hw
    unfold speedCapacity
    have hpre : 0 ≤ prefixSum s (min A.card m) := sum_nonneg fun j _ => hs0 j
    calc ∑ i ∈ A, p i ≤ makespan S * prefixSum s (min A.card m) := hw
      _ ≤ T * prefixSum s (min A.card m) := mul_le_mul_of_nonneg_right hST hpre
  · intro hA
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine ⟨[], ⟨by simp, List.Pairwise.nil, fun i => i.elim0⟩, ?_⟩
      simp [makespan, hT]
    · have hTpos : 0 < T := by
        rcases hT.lt_or_eq with h | h
        · exact h
        · exfalso
          have := hA {⟨0, hn⟩}
          rw [← h, zero_mul, sum_singleton] at this
          linarith [hp ⟨0, hn⟩]
      refine up_construct hm s hs p hp hp' T hTpos fun K => ?_
      have hcard : (univ.filter (fun i : Fin n => (i : ℕ) < K)).card ≤ K := by
        calc (univ.filter (fun i : Fin n => (i : ℕ) < K)).card ≤ (range K).card :=
              card_le_card_of_injOn (fun i => (i : ℕ))
                (fun i hi => mem_range.mpr (mem_filter.mp hi).2)
                (fun i _ j _ h => Fin.ext h)
          _ = K := card_range K
      have h2 : speedCapacity s (univ.filter (fun i : Fin n => (i : ℕ) < K)) ≤ prefixSum s K :=
        up_prefix_mono s hs0 ((min_le_left _ _).trans hcard)
      calc prefixSum p K = ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < K), p i := rfl
        _ ≤ T * speedCapacity s (univ.filter (fun i : Fin n => (i : ℕ) < K)) := hA _
        _ ≤ T * prefixSum s K := mul_le_mul_of_nonneg_left h2 hT

end SchedulingAlgorithms

open SchedulingAlgorithms

theorem solution {n m : ℕ} (hm : 0 < m)
    (s : Fin m → ℝ) (hs : ∀ j, 0 < s j) (hs' : Antitone s)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hp' : Antitone p)
    (T : ℝ) (hT : 0 ≤ T) :
    (∃ S : PreemptiveSchedule n m, IsFeasible s p S ∧ makespan S ≤ T) ↔
      ∀ A : Finset (Fin n), ∑ i ∈ A, p i ≤ T * speedCapacity s A :=
  up_feasible_iff hm s hs hs' p hp hp' T hT
