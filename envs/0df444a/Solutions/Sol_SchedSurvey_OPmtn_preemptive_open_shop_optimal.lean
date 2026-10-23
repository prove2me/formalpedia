-- Prove2me | solution 1 for SchedSurvey.OPmtn.preemptive_open_shop_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T15:02:14.059462+00:00
-- url     : https://prove2.me/submissions/49c72214-72a0-465e-8306-a355abb929a3

import Mathlib
import Definitions.Def_SchedSurvey_OPmtn_Model

set_option autoImplicit false

namespace OSAux69

open SchedSurvey.OPmtn

lemma sum_filter_map {α : Type*} (l : List α) (p : α → Bool) (f : α → ℝ) :
    ((l.filter p).map f).sum = (l.map (fun x => if p x then f x else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

lemma sum_split {α : Type*} (l : List α) (p : α → Bool) (f : α → ℝ) :
    (l.map f).sum = ((l.filter p).map f).sum + ((l.filter (fun x => !p x)).map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ih] <;> ring

lemma list_sum_finset_comm {α ι : Type*} [Fintype ι] (l : List α) (g : ι → α → ℝ) :
    ∑ j, (l.map (g j)).sum = (l.map (fun x => ∑ j, g j x)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

/-- Interval packing: pairwise non-overlapping pieces inside `[A, B]` have total length
at most `B - A`. -/
lemma pack {m n : ℕ} : ∀ (k : ℕ) (L : List (Piece m n)) (A B : ℝ), L.length = k → A ≤ B →
    (∀ q ∈ L, A ≤ q.start ∧ q.start ≤ q.stop ∧ q.stop ≤ B) →
    L.Pairwise (fun q q' => q.stop ≤ q'.start ∨ q'.stop ≤ q.start) →
    (L.map (fun q => q.stop - q.start)).sum ≤ B - A := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro L A B hk hAB hin hpw
  cases L with
  | nil => simp; linarith
  | cons q rest =>
    rw [List.pairwise_cons] at hpw
    obtain ⟨hq, hrest⟩ := hpw
    have hqin := hin q (by simp)
    have hsplit := sum_split rest (fun r => decide (r.stop ≤ q.start)) (fun q => q.stop - q.start)
    have hlen : rest.length < k := by simp at hk; omega
    have hL := ih _ (lt_of_le_of_lt (List.length_filter_le _ _) hlen)
      (rest.filter (fun r => decide (r.stop ≤ q.start))) A q.start rfl hqin.1
      (by
        intro r hr
        rw [List.mem_filter] at hr
        have := hin r (by simp [hr.1])
        refine ⟨this.1, this.2.1, by simpa using hr.2⟩)
      (hrest.filter _)
    have hR := ih _ (lt_of_le_of_lt (List.length_filter_le _ _) hlen)
      (rest.filter (fun r => !decide (r.stop ≤ q.start))) q.stop B rfl hqin.2.2
      (by
        intro r hr
        rw [List.mem_filter] at hr
        have h1 := hin r (by simp [hr.1])
        have h2 : ¬ r.stop ≤ q.start := by simpa using hr.2
        have h3 := hq r hr.1
        refine ⟨?_, h1.2.1, h1.2.2⟩
        rcases h3 with h3 | h3
        · exact h3
        · exact absurd h3 h2)
      (hrest.filter _)
    simp only [List.map_cons, List.sum_cons]
    linarith

/-- One time slot `[t, t')` driven by a permutation of the padded index set. -/
noncomputable def slot {m n : ℕ} (σ : Equiv.Perm (Fin m ⊕ Fin n)) (t t' : ℝ) :
    List (Piece m n) :=
  ((Finset.univ : Finset (Fin m × Fin n)).toList.filter
      (fun x => decide (σ (Sum.inl x.1) = Sum.inr x.2))).map
    (fun x => (⟨x.1, x.2, t, t'⟩ : Piece m n))

/-- Consecutive slots, one per permutation in the list, with lengths given by `w`. -/
noncomputable def build {m n : ℕ} (w : Equiv.Perm (Fin m ⊕ Fin n) → ℝ) :
    List (Equiv.Perm (Fin m ⊕ Fin n)) → ℝ → List (Piece m n)
  | [], _ => []
  | σ :: rest, t => slot σ t (t + w σ) ++ build w rest (t + w σ)

lemma mem_slot {m n : ℕ} {σ : Equiv.Perm (Fin m ⊕ Fin n)} {t t' : ℝ} {q : Piece m n}
    (h : q ∈ slot σ t t') : q.start = t ∧ q.stop = t' := by
  unfold slot at h
  rw [List.mem_map] at h
  obtain ⟨x, _, rfl⟩ := h
  exact ⟨rfl, rfl⟩

lemma build_bounds {m n : ℕ} (w : Equiv.Perm (Fin m ⊕ Fin n) → ℝ) (hw : ∀ σ, 0 ≤ w σ) :
    ∀ (L : List (Equiv.Perm (Fin m ⊕ Fin n))) (t : ℝ), ∀ q ∈ build w L t,
      t ≤ q.start ∧ q.start ≤ q.stop ∧ q.stop ≤ t + (L.map w).sum := by
  intro L
  induction L with
  | nil => intro t q hq; simp [build] at hq
  | cons σ rest ih =>
    intro t q hq
    simp only [build, List.mem_append] at hq
    have hrest : 0 ≤ (rest.map w).sum :=
      List.sum_nonneg (by intro x hx; rw [List.mem_map] at hx; obtain ⟨s, _, rfl⟩ := hx; exact hw s)
    have hσ := hw σ
    rcases hq with hq | hq
    · obtain ⟨h1, h2⟩ := mem_slot hq
      simp only [List.map_cons, List.sum_cons]
      refine ⟨by rw [h1], by rw [h1, h2]; linarith, by rw [h2]; linarith⟩
    · have := ih (t + w σ) q hq
      simp only [List.map_cons, List.sum_cons]
      refine ⟨by linarith [this.1], this.2.1, by linarith [this.2.2]⟩

lemma slot_pairwise {m n : ℕ} (σ : Equiv.Perm (Fin m ⊕ Fin n)) (t t' : ℝ) :
    (slot σ t t').Pairwise (fun q q' => (q.mach = q'.mach ∨ q.job = q'.job) →
      q.stop ≤ q'.start ∨ q'.stop ≤ q.start) := by
  unfold slot
  rw [List.pairwise_map, List.pairwise_filter]
  refine (Finset.nodup_toList _).imp ?_
  intro x y hxy hx hy hc
  exfalso
  apply hxy
  simp only [decide_eq_true_eq] at hx hy
  rcases hc with hc | hc
  · have h1 : x.1 = y.1 := hc
    have : (Sum.inr x.2 : Fin m ⊕ Fin n) = Sum.inr y.2 := by rw [← hx, ← hy, h1]
    exact Prod.ext h1 (Sum.inr_injective this)
  · have h2 : x.2 = y.2 := hc
    have : σ (Sum.inl x.1) = σ (Sum.inl y.1) := by rw [hx, hy, h2]
    exact Prod.ext (Sum.inl_injective (σ.injective this)) h2

lemma build_pairwise {m n : ℕ} (w : Equiv.Perm (Fin m ⊕ Fin n) → ℝ) (hw : ∀ σ, 0 ≤ w σ) :
    ∀ (L : List (Equiv.Perm (Fin m ⊕ Fin n))) (t : ℝ),
      (build w L t).Pairwise (fun q q' => (q.mach = q'.mach ∨ q.job = q'.job) →
        q.stop ≤ q'.start ∨ q'.stop ≤ q.start) := by
  intro L
  induction L with
  | nil => intro t; simp [build]
  | cons σ rest ih =>
    intro t
    simp only [build]
    rw [List.pairwise_append]
    refine ⟨slot_pairwise σ _ _, ih _, ?_⟩
    intro a ha b hb _
    left
    have h1 := (mem_slot ha).2
    have h2 := (build_bounds w hw rest (t + w σ) b hb).1
    rw [h1]; exact h2

lemma slot_sum {m n : ℕ} (σ : Equiv.Perm (Fin m ⊕ Fin n)) (t t' : ℝ) (i : Fin m) (j : Fin n) :
    (((slot σ t t').filter (fun q => decide (q.mach = i ∧ q.job = j))).map
      (fun q => q.stop - q.start)).sum =
      if σ (Sum.inl i) = Sum.inr j then t' - t else 0 := by
  unfold slot
  rw [List.filter_map, List.map_map, sum_filter_map, sum_filter_map, Finset.sum_map_toList,
    Finset.sum_eq_single (i, j)]
  · by_cases h : σ (Sum.inl i) = Sum.inr j <;> simp [h]
  · intro b _ hb
    have : ¬ (b.1 = i ∧ b.2 = j) := fun h => hb (Prod.ext h.1 h.2)
    simp [this]
  · simp

lemma build_sum {m n : ℕ} (w : Equiv.Perm (Fin m ⊕ Fin n) → ℝ) (i : Fin m) (j : Fin n) :
    ∀ (L : List (Equiv.Perm (Fin m ⊕ Fin n))) (t : ℝ),
      (((build w L t).filter (fun q => decide (q.mach = i ∧ q.job = j))).map
        (fun q => q.stop - q.start)).sum =
        (L.map (fun σ => if σ (Sum.inl i) = Sum.inr j then w σ else 0)).sum := by
  intro L
  induction L with
  | nil => intro t; simp [build]
  | cons σ rest ih =>
    intro t
    simp only [build, List.filter_append, List.map_append, List.sum_append, ih, slot_sum,
      List.map_cons, List.sum_cons]
    congr 1
    split_ifs <;> ring

/-- The padded square matrix with all row and column sums equal to `T`. -/
noncomputable def padQ {m n : ℕ} (P : Fin m → Fin n → ℝ) (T : ℝ) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal (fun i => T - rowSum P i)) (Matrix.of P)
    (Matrix.of (fun j i => P i j)) (Matrix.diagonal (fun j => T - colSum P j))

lemma padQ_nonneg {m n : ℕ} (P : Fin m → Fin n → ℝ) (hP : ∀ i j, 0 ≤ P i j) (T : ℝ)
    (hr : ∀ i, rowSum P i ≤ T) (hc : ∀ j, colSum P j ≤ T) :
    ∀ r c, 0 ≤ padQ P T r c := by
  intro r c
  rcases r with i | j <;> rcases c with i' | j'
  · simp only [padQ, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply]
    split_ifs
    · linarith [hr i]
    · exact le_refl 0
  · simp only [padQ, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]; exact hP i j'
  · simp only [padQ, Matrix.fromBlocks_apply₂₁, Matrix.of_apply]; exact hP i' j
  · simp only [padQ, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply]
    split_ifs
    · linarith [hc j]
    · exact le_refl 0

lemma padQ_row {m n : ℕ} (P : Fin m → Fin n → ℝ) (T : ℝ) :
    ∀ r, ∑ c, padQ P T r c = T := by
  intro r
  rcases r with i | j
  · simp only [padQ, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.diagonal_apply, Matrix.of_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    unfold rowSum; ring
  · simp only [padQ, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.diagonal_apply, Matrix.of_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    unfold colSum; ring

lemma padQ_col {m n : ℕ} (P : Fin m → Fin n → ℝ) (T : ℝ) :
    ∀ c, ∑ r, padQ P T r c = T := by
  intro c
  rcases c with i | j
  · simp only [padQ, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
      Matrix.diagonal_apply, Matrix.of_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    unfold rowSum; ring
  · simp only [padQ, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂,
      Matrix.diagonal_apply, Matrix.of_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    unfold colSum; ring

lemma forward {m n : ℕ} (P : Fin m → Fin n → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (S : List (Piece m n)) (hS : IsFeasible P S) (hC : CompletesBy S T) :
    (∀ i, rowSum P i ≤ T) ∧ ∀ j, colSum P j ≤ T := by
  obtain ⟨h1, h2, h3⟩ := hS
  -- generic bound for a set of pieces that pairwise conflict
  have key : ∀ g : Piece m n → Bool,
      (∀ q q', g q = true → g q' = true → (q.mach = q'.mach ∨ q.job = q'.job)) →
      ((S.filter g).map (fun q => q.stop - q.start)).sum ≤ T := by
    intro g hg
    have := pack _ (S.filter g) 0 T rfl hT
      (by
        intro q hq
        rw [List.mem_filter] at hq
        exact ⟨(h1 q hq.1).1, (h1 q hq.1).2, hC q hq.1⟩)
      (by
        rw [List.pairwise_filter]
        exact h2.imp (fun hxy hx hy => hxy (hg _ _ hx hy)))
    linarith
  constructor
  · intro i
    have e : rowSum P i = ((S.filter (fun q => decide (q.mach = i))).map
        (fun q => q.stop - q.start)).sum := by
      unfold rowSum
      simp only [← h3, sum_filter_map]
      rw [list_sum_finset_comm]
      congr 1
      apply List.map_congr_left
      intro q _
      by_cases hq : q.mach = i
      · simp [hq]
      · simp [hq]
    rw [e]
    exact key _ (fun q q' hq hq' => Or.inl (by simp at hq hq'; rw [hq, hq']))
  · intro j
    have e : colSum P j = ((S.filter (fun q => decide (q.job = j))).map
        (fun q => q.stop - q.start)).sum := by
      unfold colSum
      simp only [← h3, sum_filter_map]
      rw [list_sum_finset_comm]
      congr 1
      apply List.map_congr_left
      intro q _
      by_cases hq : q.job = j
      · simp [hq]
      · simp [hq]
    rw [e]
    exact key _ (fun q q' hq hq' => Or.inr (by simp at hq hq'; rw [hq, hq']))

lemma backward {m n : ℕ} (P : Fin m → Fin n → ℝ) (hP : ∀ i j, 0 ≤ P i j) (T : ℝ)
    (hT : 0 ≤ T) (hr : ∀ i, rowSum P i ≤ T) (hc : ∀ j, colSum P j ≤ T) :
    ∃ S : List (Piece m n), IsFeasible P S ∧ CompletesBy S T := by
  rcases hT.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨[], ⟨by simp, by simp, ?_⟩, by simp [CompletesBy]⟩
    intro i j
    have h := Finset.single_le_sum (fun j _ => hP i j) (Finset.mem_univ j)
    have := hr i
    unfold rowSum at this
    simp
    linarith [hP i j]
  · set Q := padQ P T with hQ
    have hM : T⁻¹ • Q ∈ doublyStochastic ℝ (Fin m ⊕ Fin n) := by
      rw [mem_doublyStochastic_iff_sum]
      refine ⟨?_, ?_, ?_⟩
      · intro r c
        simp only [Matrix.smul_apply, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.mpr hpos.le) (padQ_nonneg P hP T hr hc r c)
      · intro r
        simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hQ, padQ_row]
        field_simp
      · intro c
        simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hQ, padQ_col]
        field_simp
    obtain ⟨w, hw0, hw1, hwM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
    let v : Equiv.Perm (Fin m ⊕ Fin n) → ℝ := fun σ => T * w σ
    have hv : ∀ σ, 0 ≤ v σ := fun σ => mul_nonneg hpos.le (hw0 σ)
    have hentry : ∀ i j, P i j =
        ∑ σ, (if σ (Sum.inl i) = Sum.inr j then v σ else 0) := by
      intro i j
      have e1 : Q (Sum.inl i) (Sum.inr j) = P i j := by
        simp [hQ, padQ]
      have e2 := congrArg (fun A => A (Sum.inl i) (Sum.inr j)) hwM
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at e2
      have e3 : T * (T⁻¹ * Q (Sum.inl i) (Sum.inr j)) = Q (Sum.inl i) (Sum.inr j) := by
        field_simp
      rw [← e1, ← e3, ← e2, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      by_cases h : σ (Sum.inl i) = Sum.inr j
      · simp [h, v, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
      · have h' : ¬ (Sum.inr j : Fin m ⊕ Fin n) = σ (Sum.inl i) := fun e => h e.symm
        simp [h, v, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    have htot : ((Finset.univ : Finset (Equiv.Perm (Fin m ⊕ Fin n))).toList.map v).sum = T := by
      rw [Finset.sum_map_toList]
      simp only [v, ← Finset.mul_sum, hw1, mul_one]
    refine ⟨build v (Finset.univ : Finset (Equiv.Perm (Fin m ⊕ Fin n))).toList 0, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro q hq
      have := build_bounds v hv _ 0 q hq
      exact ⟨this.1, this.2.1⟩
    · exact build_pairwise v hv _ 0
    · intro i j
      rw [build_sum, Finset.sum_map_toList, hentry]
    · intro q hq
      have := build_bounds v hv _ 0 q hq
      linarith [this.2.2]

end OSAux69

open SchedSurvey.OPmtn in
theorem solution {m n : ℕ} (P : Fin m → Fin n → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (T : ℝ) (hT : 0 ≤ T) :
    (∃ S : List (Piece m n), IsFeasible P S ∧ CompletesBy S T) ↔
      ((∀ i, rowSum P i ≤ T) ∧ ∀ j, colSum P j ≤ T) := by
  constructor
  · rintro ⟨S, hS, hC⟩
    exact OSAux69.forward P T hT S hS hC
  · rintro ⟨hr, hc⟩
    exact OSAux69.backward P hP T hT hr hc
