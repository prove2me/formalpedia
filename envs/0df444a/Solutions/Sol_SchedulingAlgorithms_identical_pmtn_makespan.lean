-- Prove2me | solution 1 for SchedulingAlgorithms.identical_pmtn_makespan
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T23:00:07.429986+00:00
-- url     : https://prove2.me/submissions/bad12a45-4778-47e0-8995-79639e46bdf1

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

section Mc

variable {n m : ℕ}

lemma sa_prefix_succ (p : Fin n → ℝ) (i : Fin n) :
    prefixSum p ((i : ℕ) + 1) = prefixSum p i + p i := by
  unfold prefixSum
  have : univ.filter (fun k : Fin n => (k : ℕ) < (i : ℕ) + 1)
      = insert i (univ.filter (fun k : Fin n => (k : ℕ) < i)) := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · right; exact h
      · left; exact Fin.ext h
    · rintro (rfl | h) <;> omega
  rw [this, sum_insert (by simp), add_comm]

lemma sa_prefix_mono (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) {j j' : ℕ} (h : j ≤ j') :
    prefixSum p j ≤ prefixSum p j' :=
  sum_le_sum_of_subset_of_nonneg (fun k hk => by simp only [mem_filter, mem_univ, true_and] at hk ⊢; omega)
    (fun k _ _ => hp k)

lemma sa_prefix_all (p : Fin n → ℝ) : prefixSum p n = ∑ i, p i := by
  unfold prefixSum; congr 1; ext i; simp

lemma sa_flatMap_sum {α β : Type*} (l : List α) (f : α → List β) (g : β → ℝ) :
    ((l.flatMap f).map g).sum = (l.map (fun a => ((f a).map g).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

lemma sa_finRange_sum (f : Fin n → ℝ) : ((List.finRange n).map f).sum = ∑ i, f i := by
  rw [← List.ofFn_eq_map, List.sum_ofFn]

/-- Machine index `k`, clamped into `Fin m`. -/
def mcMach (hm : 0 < m) (k : ℕ) : Fin m := ⟨min k (m - 1), by omega⟩

/-- McNaughton's wrap-around rule: job `i` occupies `[P_i, P_{i+1})` of the time line
`[0, m B)` cut into `m` machine slices of length `B`. -/
noncomputable def mcPieces (hm : 0 < m) (B : ℝ) (p : Fin n → ℝ) (i : Fin n) : List (Piece n m) :=
  if prefixSum p ((i : ℕ) + 1) ≤ ((⌊prefixSum p i / B⌋₊ : ℕ) + 1) * B then
    [⟨i, mcMach hm ⌊prefixSum p i / B⌋₊, prefixSum p i - (⌊prefixSum p i / B⌋₊ : ℕ) * B,
      prefixSum p ((i : ℕ) + 1) - (⌊prefixSum p i / B⌋₊ : ℕ) * B⟩]
  else
    [⟨i, mcMach hm ⌊prefixSum p i / B⌋₊, prefixSum p i - (⌊prefixSum p i / B⌋₊ : ℕ) * B, B⟩,
     ⟨i, mcMach hm (⌊prefixSum p i / B⌋₊ + 1), 0,
      prefixSum p ((i : ℕ) + 1) - ((⌊prefixSum p i / B⌋₊ : ℕ) + 1) * B⟩]

variable (hm : 0 < m) (B : ℝ) (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hB : 0 < B)
  (hpB : ∀ i, p i ≤ B) (hsum : ∑ i, p i ≤ m * B)
include hp hB hpB hsum

lemma mc_piece_props (i : Fin n) : ∀ x ∈ mcPieces hm B p i,
    x.job = i ∧ 0 ≤ x.start ∧ x.start ≤ x.stop ∧ x.stop ≤ B ∧
      prefixSum p i ≤ (x.machine : ℝ) * B + x.start ∧
      (x.machine : ℝ) * B + x.stop ≤ prefixSum p ((i : ℕ) + 1) := by
  set a := prefixSum p i with ha
  set b := prefixSum p ((i : ℕ) + 1) with hb
  have hba : b = a + p i := sa_prefix_succ p i
  have ha0 : 0 ≤ a := sum_nonneg fun k _ => (hp k).le
  have hdiv0 : 0 ≤ a / B := div_nonneg ha0 hB.le
  set μ := ⌊a / B⌋₊ with hμ
  have F1 : (μ : ℝ) * B ≤ a := by
    have := Nat.floor_le hdiv0; rw [← hμ] at this
    calc (μ : ℝ) * B ≤ a / B * B := mul_le_mul_of_nonneg_right this hB.le
      _ = a := div_mul_cancel₀ a hB.ne'
  have F2 : a < ((μ : ℝ) + 1) * B := by
    have := Nat.lt_floor_add_one (a / B); rw [← hμ] at this
    calc a = a / B * B := (div_mul_cancel₀ a hB.ne').symm
      _ < ((μ : ℝ) + 1) * B := mul_lt_mul_of_pos_right this hB
  have hbmB : b ≤ m * B := by
    calc b ≤ prefixSum p n := sa_prefix_mono p (fun k => (hp k).le) (by omega)
      _ = ∑ k, p k := sa_prefix_all p
      _ ≤ m * B := hsum
  have F4 : μ < m := by
    rw [hμ, Nat.floor_lt hdiv0, div_lt_iff₀ hB]
    linarith [hp i]
  have hmach : ((mcMach hm μ : Fin m) : ℕ) = μ := by simp [mcMach]; omega
  intro x hx
  unfold mcPieces at hx
  rw [← ha, ← hb, ← hμ] at hx
  split_ifs at hx with hsplit
  · rw [List.mem_singleton] at hx; subst hx
    simp only [hmach]
    refine ⟨trivial, by linarith, by linarith [hp i], by linarith, by linarith, by linarith⟩
  · push Not at hsplit
    have F5 : μ + 1 < m := by
      have : ((μ : ℝ) + 1) * B < (m : ℝ) * B := hsplit.trans_le hbmB
      have := lt_of_mul_lt_mul_right this hB.le
      exact_mod_cast this
    have hmach1 : ((mcMach hm (μ + 1) : Fin m) : ℕ) = μ + 1 := by simp [mcMach]; omega
    rcases List.mem_pair.mp hx with rfl | rfl
    · simp only [hmach]
      refine ⟨trivial, by linarith, by linarith, le_rfl, by linarith, by linarith⟩
    · simp only [hmach1]
      push_cast
      refine ⟨trivial, le_rfl, by linarith, by linarith [hpB i], by linarith, by linarith⟩

lemma mc_within (i : Fin n) : (mcPieces hm B p i).Pairwise
    (fun a b => (a.machine = b.machine ∨ a.job = b.job) → Piece.Disjoint a b) := by
  unfold mcPieces
  split_ifs with hsplit
  · exact List.pairwise_singleton _ _
  · rw [List.pairwise_pair]
    intro _
    right
    have hba : prefixSum p ((i : ℕ) + 1) = prefixSum p i + p i := sa_prefix_succ p i
    simp only
    linarith [hpB i]

lemma mc_length_sum (i : Fin n) :
    ((mcPieces hm B p i).map (fun q => (1 : ℝ) * (q.stop - q.start))).sum = p i := by
  have hba : prefixSum p ((i : ℕ) + 1) = prefixSum p i + p i := sa_prefix_succ p i
  unfold mcPieces
  split_ifs <;> simp <;> linarith

/-- McNaughton's schedule. -/
noncomputable def mcSched : PreemptiveSchedule n m := (List.finRange n).flatMap (mcPieces hm B p)

lemma mc_feasible : IsFeasible (fun _ => 1) p (mcSched hm B p) := by
  refine ⟨fun q hq => ?_, ?_, fun i => ?_⟩
  · obtain ⟨i, -, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨-, h1, h2, -⟩ := mc_piece_props hm B p hp hB hpB hsum i q hq
    exact ⟨h1, h2⟩
  · rw [mcSched, List.pairwise_flatMap]
    refine ⟨fun i _ => mc_within hm B p hp hB hpB hsum i, ?_⟩
    refine (List.pairwise_lt_finRange n).imp fun {i i'} hii' x hx y hy hxy => ?_
    obtain ⟨hxj, -, -, -, -, hx2⟩ := mc_piece_props hm B p hp hB hpB hsum i x hx
    obtain ⟨hyj, -, -, -, hy1, -⟩ := mc_piece_props hm B p hp hB hpB hsum i' y hy
    rcases hxy with hm' | hj
    · left
      have hmono : prefixSum p ((i : ℕ) + 1) ≤ prefixSum p i' :=
        sa_prefix_mono p (fun k => (hp k).le) (by rw [Fin.lt_def] at hii'; omega)
      rw [hm'] at hx2
      linarith
    · exact absurd (hxj.symm.trans (hj.trans hyj)) (ne_of_lt hii')
  · unfold work mcSched
    rw [sa_list_filter_sum, sa_flatMap_sum, sa_finRange_sum]
    rw [Finset.sum_eq_single i]
    · have : ∀ q ∈ mcPieces hm B p i, q.job = i := fun q hq =>
        (mc_piece_props hm B p hp hB hpB hsum i q hq).1
      rw [← mc_length_sum hm B p hp hB hpB hsum i]
      congr 1
      exact List.map_congr_left fun q hq => by simp [this q hq]
    · intro i' _ hne
      have : ∀ q ∈ mcPieces hm B p i', q.job ≠ i := fun q hq =>
        (mc_piece_props hm B p hp hB hpB hsum i' q hq).1 ▸ hne
      rw [List.map_congr_left (g := fun _ => (0 : ℝ)) fun q hq => by simp [this q hq]]
      simp
    · simp

end Mc

lemma sa_makespan_le {n m : ℕ} (S : PreemptiveSchedule n m) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ q ∈ S, q.stop ≤ B) : makespan S ≤ B := by
  unfold makespan
  induction S with
  | nil => simpa using hB
  | cons a S ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h a (List.mem_cons_self ..)) (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem mc_main {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) :
    (∀ S : PreemptiveSchedule n m, IsFeasible (fun _ => 1) p S →
        mcNaughtonBound hn p m ≤ makespan S) ∧
      ∃ S : PreemptiveSchedule n m, IsFeasible (fun _ => 1) p S ∧
        makespan S = mcNaughtonBound hn p m := by
  classical
  set B := mcNaughtonBound hn p m with hBdef
  have hsup : ∀ i, p i ≤ univ.sup' ⟨⟨0, hn⟩, mem_univ _⟩ p := fun i => le_sup' p (mem_univ i)
  have hpB : ∀ i, p i ≤ B := fun i => (hsup i).trans (le_max_left _ _)
  have hB : 0 < B := (hp ⟨0, hn⟩).trans_le (hpB _)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum : ∑ i, p i ≤ m * B := by
    have : (∑ i, p i) / m ≤ B := le_max_right _ _
    rw [div_le_iff₀ hmpos] at this; linarith
  have hone : ∀ k, k ≤ m → prefixSum (fun _ : Fin m => (1 : ℝ)) k = k := by
    intro k hk; unfold prefixSum; rw [sum_const, sa_card_fin_lt m k hk]; simp
  refine ⟨fun S hS => ?_, mcSched hm B p, mc_feasible hm B p hp hB hpB hsum, ?_⟩
  · have hwb := fun A k h1 h2 =>
      sa_work_bound (fun _ : Fin m => (1 : ℝ)) (fun _ => zero_le_one) (fun _ _ _ => le_rfl)
        S hS.1 hS.2.1 A k h1 h2
    apply max_le
    · apply sup'_le
      intro i _
      have := hwb {i} 1 (by simp) hm
      rw [sum_singleton, hS.2.2, hone 1 hm] at this
      simpa using this
    · have := hwb univ m (min_le_right _ _) le_rfl
      simp_rw [hS.2.2] at this
      rw [hone m le_rfl] at this
      rw [div_le_iff₀ hmpos]; linarith
  · -- the makespan is exactly `B`
    apply le_antisymm
    · apply sa_makespan_le _ B hB.le
      intro q hq
      obtain ⟨i, -, hq⟩ := List.mem_flatMap.mp hq
      exact (mc_piece_props hm B p hp hB hpB hsum i q hq).2.2.2.1
    · -- some piece ends exactly at `B`
      suffices ∃ q ∈ mcSched hm B p, q.stop = B by
        obtain ⟨q, hq, hqB⟩ := this
        exact hqB.symm.le.trans (sa_stop_le _ q hq)
      rcases le_total (univ.sup' ⟨⟨0, hn⟩, mem_univ _⟩ p) ((∑ i, p i) / m) with hcase | hcase
      · -- `B = (∑ p) / m`: the last job ends exactly at `m B`
        have hBeq : B = (∑ i, p i) / m := max_eq_right hcase
        set i : Fin n := ⟨n - 1, by omega⟩
        have hb : prefixSum p ((i : ℕ) + 1) = m * B := by
          rw [show (i : ℕ) + 1 = n by simp [i]; omega, sa_prefix_all, hBeq]; field_simp
        have ha : prefixSum p i = m * B - p i := by rw [← hb, sa_prefix_succ]; ring
        set μ := ⌊prefixSum p i / B⌋₊ with hμ
        have ha0 : 0 ≤ prefixSum p i / B := div_nonneg (sum_nonneg fun k _ => (hp k).le) hB.le
        have hμm : μ = m - 1 := by
          apply le_antisymm
          · have : μ < m := by
              rw [hμ, Nat.floor_lt ha0, div_lt_iff₀ hB, ha]; linarith [hp i]
            omega
          · have h1 : ((m - 1 : ℕ) : ℝ) ≤ prefixSum p i / B := by
              rw [le_div_iff₀ hB, ha, Nat.cast_sub hm, Nat.cast_one]; linarith [hpB i]
            exact Nat.le_floor h1
        have hμr : ((μ : ℕ) : ℝ) + 1 = m := by rw [hμm, Nat.cast_sub hm]; simp
        refine ⟨⟨i, mcMach hm μ, prefixSum p i - (μ : ℝ) * B, prefixSum p ((i : ℕ) + 1) - (μ : ℝ) * B⟩,
          List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩, ?_⟩
        · unfold mcPieces
          rw [← hμ, if_pos (by rw [hμr, hb])]
          exact List.mem_singleton_self _
        · simp only
          rw [hb, show (μ : ℝ) = m - 1 by linarith]; ring
      · -- `B = max p = p i0`: the first piece of job `i0` ends exactly at `B`
        have hBeq : B = univ.sup' ⟨⟨0, hn⟩, mem_univ _⟩ p := max_eq_left hcase
        obtain ⟨i0, -, hi0⟩ := exists_mem_eq_sup' ⟨⟨0, hn⟩, mem_univ _⟩ p
        have hpi0 : p i0 = B := by rw [hBeq, hi0]
        have hba : prefixSum p ((i0 : ℕ) + 1) = prefixSum p i0 + p i0 := sa_prefix_succ p i0
        set μ := ⌊prefixSum p i0 / B⌋₊ with hμ
        have ha0 : 0 ≤ prefixSum p i0 / B := div_nonneg (sum_nonneg fun k _ => (hp k).le) hB.le
        have F1 : (μ : ℝ) * B ≤ prefixSum p i0 := by
          have := Nat.floor_le ha0; rw [← hμ] at this
          calc (μ : ℝ) * B ≤ prefixSum p i0 / B * B := mul_le_mul_of_nonneg_right this hB.le
            _ = prefixSum p i0 := div_mul_cancel₀ _ hB.ne'
        by_cases hsplit : prefixSum p ((i0 : ℕ) + 1) ≤ ((μ : ℝ) + 1) * B
        · refine ⟨⟨i0, mcMach hm μ, prefixSum p i0 - (μ : ℝ) * B,
            prefixSum p ((i0 : ℕ) + 1) - (μ : ℝ) * B⟩,
            List.mem_flatMap.mpr ⟨i0, List.mem_finRange i0, ?_⟩, ?_⟩
          · unfold mcPieces; rw [← hμ, if_pos hsplit]; exact List.mem_singleton_self _
          · simp only; linarith
        · refine ⟨⟨i0, mcMach hm μ, prefixSum p i0 - (μ : ℝ) * B, B⟩,
            List.mem_flatMap.mpr ⟨i0, List.mem_finRange i0, ?_⟩, rfl⟩
          unfold mcPieces; rw [← hμ, if_neg hsplit]; exact List.mem_cons_self ..

end SchedulingAlgorithms

open SchedulingAlgorithms

theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) :
    (∀ S : PreemptiveSchedule n m, IsFeasible (fun _ => 1) p S →
        mcNaughtonBound hn p m ≤ makespan S) ∧
      ∃ S : PreemptiveSchedule n m, IsFeasible (fun _ => 1) p S ∧
        makespan S = mcNaughtonBound hn p m :=
  mc_main hn hm p hp
