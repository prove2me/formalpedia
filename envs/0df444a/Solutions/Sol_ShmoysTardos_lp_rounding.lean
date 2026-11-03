-- Prove2me | solution 1 for ShmoysTardos.lp_rounding
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:13:22.57269+00:00
-- url     : https://prove2.me/submissions/da6eddae-3974-493c-a7c4-e20284278103

import Mathlib

open Finset

/-- Length of the overlap of `[a, b)` with the unit slot `[t, t + 1)`. -/
noncomputable def stOv (a b t : ℝ) : ℝ := max 0 (min b (t + 1) - max a t)

lemma stOv_nonneg (a b t : ℝ) : 0 ≤ stOv a b t := le_max_left _ _

lemma stOv_range (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ K : ℕ, ∑ t ∈ range K, stOv a b t = min b K - min a K := by
  intro K
  induction K with
  | zero => simp [min_eq_right ha, min_eq_right (ha.trans hab)]
  | succ K ih =>
    rw [sum_range_succ, ih]
    push_cast
    unfold stOv
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
    rcases le_total b K with h1 | h1 <;> rcases le_total a K with h2 | h2 <;>
      rcases le_total b (K+1) with h3 | h3 <;> rcases le_total a (K+1) with h4 | h4 <;>
      simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, *] <;>
      first
      | (rw [max_eq_left (by linarith)]; linarith)
      | (rw [max_eq_right (by linarith)]; linarith)
      | linarith
      | skip

lemma stOv_add (a b t : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 ≤ t) :
    stOv 0 a t + stOv a b t = stOv 0 b t := by
  unfold stOv
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma stOv_le_one (c t : ℝ) (ht : 0 ≤ t) : stOv 0 c t ≤ 1 := by
  unfold stOv
  apply max_le zero_le_one
  have := min_le_right c (t+1)
  have := le_max_right 0 t
  linarith

lemma stOv_pos {a b t : ℝ} (h : 0 < stOv a b t) : t < b ∧ a < t + 1 := by
  unfold stOv at h
  simp only [max_def, min_def] at h
  split_ifs at h <;> constructor <;> linarith

lemma stOv_eq_one (c t : ℝ) (ht : 0 ≤ t) (hc : t + 1 ≤ c) : stOv 0 c t = 1 := by
  unfold stOv
  rw [min_eq_right hc, max_eq_right ht]
  norm_num

lemma stOv_telescope (S : ℕ → ℝ) (hS0 : S 0 = 0) (hSm : Monotone S) (hSnn : ∀ u, 0 ≤ S u)
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ N : ℕ, ∑ u ∈ range N, stOv (S u) (S (u + 1)) t = stOv 0 (S N) t := by
  intro N
  induction N with
  | zero =>
    simp only [range_zero, sum_empty, hS0]
    unfold stOv
    rw [min_eq_left (by linarith), max_eq_right ht]
    simp [ht]
  | succ N ih =>
    rw [sum_range_succ, ih, stOv_add _ _ _ (hSnn N) (hSm (Nat.le_succ N)) ht]

/-- Shmoys–Tardos slots for one machine: the jobs, sorted by nonincreasing processing time, are
poured fractionally into unit slots `0, 1, …, n - 1`. -/
lemma st_slots {n : ℕ} (y p : Fin n → ℝ) (hy0 : ∀ j, 0 ≤ y j) (hyle : ∑ j, y j ≤ n) :
    ∃ x : Fin n → Fin n → ℝ, (∀ j t, 0 ≤ x j t) ∧ (∀ j, ∑ t, x j t = y j) ∧
      (∀ t, ∑ j, x j t ≤ 1) ∧
      ∀ (j : Fin n) (t t' : Fin n), (t : ℕ) = t' + 1 → 0 < x j t →
        p j ≤ ∑ j', x j' t' * p j' := by
  classical
  set e : Equiv.Perm (Fin n) := Tuple.sort (fun j => -p j) with he
  have hmono : Monotone ((fun j => -p j) ∘ e) := Tuple.monotone_sort _
  have hanti : ∀ u v : Fin n, u ≤ v → p (e v) ≤ p (e u) := by
    intro u v huv; have := hmono huv; simp only [Function.comp] at this; linarith
  let yy : ℕ → ℝ := fun v => if h : v < n then y (e ⟨v, h⟩) else 0
  let S : ℕ → ℝ := fun u => ∑ v ∈ range u, yy v
  have hyy0 : ∀ v, 0 ≤ yy v := by
    intro v; simp only [yy]; split_ifs
    · exact hy0 _
    · exact le_rfl
  have hSmono : Monotone S := by
    intro u v huv; exact sum_le_sum_of_subset_of_nonneg (range_mono huv) (fun i _ _ => hyy0 i)
  have hS0' : S 0 = 0 := by simp [S]
  have hSnn : ∀ u, 0 ≤ S u := fun u => sum_nonneg (fun i _ => hyy0 i)
  have hSsucc : ∀ u, S (u+1) = S u + yy u := fun u => sum_range_succ _ _
  have hSn : S n = ∑ j, y j := by
    simp only [S, yy]
    rw [← Fin.sum_univ_eq_sum_range (fun v => if h : v < n then y (e ⟨v, h⟩) else 0)]
    simp only [Fin.is_lt, dif_pos, Fin.eta]
    exact Equiv.sum_comp e y
  have hSle : ∀ u, u ≤ n → S u ≤ n := fun u hu => (hSmono hu).trans (hSn ▸ hyle)
  let x : Fin n → Fin n → ℝ := fun j t =>
    stOv (S (e.symm j)) (S ((e.symm j : ℕ) + 1)) ((t : ℕ) : ℝ)
  have hcol : ∀ t : Fin n, ∑ j, x j t = stOv 0 (S n) ((t : ℕ) : ℝ) := by
    intro t
    have h1 : ∑ j, x j t = ∑ u : Fin n, stOv (S u) (S ((u : ℕ) + 1)) ((t : ℕ) : ℝ) := by
      simp only [x]
      exact Equiv.sum_comp e.symm (fun u : Fin n => stOv (S u) (S ((u : ℕ) + 1)) ((t : ℕ) : ℝ))
    rw [h1, Fin.sum_univ_eq_sum_range (fun u => stOv (S u) (S (u + 1)) ((t : ℕ) : ℝ))]
    exact stOv_telescope S hS0' hSmono hSnn _ (Nat.cast_nonneg _) n
  refine ⟨x, fun j t => stOv_nonneg _ _ _, ?_, ?_, ?_⟩
  · intro j
    have hu := (e.symm j).isLt
    simp only [x]
    rw [Fin.sum_univ_eq_sum_range (fun t => stOv (S (e.symm j)) (S ((e.symm j : ℕ) + 1)) (t : ℝ)),
      stOv_range _ _ (hSnn _) (hSmono (Nat.le_succ _)) n,
      min_eq_left (hSle _ (by omega)), min_eq_left (hSle _ (by omega)), hSsucc]
    simp only [yy, dif_pos hu, Fin.eta, Equiv.apply_symm_apply]
    ring
  · intro t
    rw [hcol]
    exact stOv_le_one _ _ (Nat.cast_nonneg _)
  · intro j t t' htt hpos
    set u := e.symm j with hu
    have hpos' : 0 < stOv (S u) (S ((u : ℕ) + 1)) ((t' : ℕ) + 1 : ℝ) := by
      have : ((t : ℕ) : ℝ) = ((t' : ℕ) : ℝ) + 1 := by rw [htt]; push_cast; ring
      simpa [x, this] using hpos
    have hb := (stOv_pos hpos').1
    have hsum1 : ∑ j', x j' t' = 1 := by
      rw [hcol]
      apply stOv_eq_one _ _ (Nat.cast_nonneg _)
      have := hSmono (show (u : ℕ) + 1 ≤ n by omega)
      linarith
    have hpj : ∀ j', 0 < x j' t' → p j ≤ p j' := by
      intro j' hj'
      set v := e.symm j' with hv
      have ha := (stOv_pos (show 0 < stOv (S v) (S ((v : ℕ) + 1)) ((t' : ℕ) : ℝ) from hj')).2
      have hvu : v ≤ u := by
        by_contra hlt
        push Not at hlt
        have := hSmono (show (u : ℕ) + 1 ≤ v by omega)
        linarith
      have := hanti v u hvu
      simpa [hu, hv] using this
    calc p j = ∑ j', x j' t' * p j := by rw [← sum_mul, hsum1, one_mul]
      _ ≤ ∑ j', x j' t' * p j' := by
        apply sum_le_sum
        intro j' _
        rcases (stOv_nonneg _ _ _ : 0 ≤ x j' t').lt_or_eq with h | h
        · exact mul_le_mul_of_nonneg_left (hpj j' h) h.le
        · have hx0 : x j' t' = 0 := h.symm
          rw [hx0]; simp

lemma st_permMatrix_apply {T : Type} [Fintype T] [DecidableEq T] (π : Equiv.Perm T) (a b : T) :
    π.permMatrix ℝ a b = if π a = b then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

/-- A fractional assignment of jobs to slots (each job fully assigned, each slot at most once)
can be replaced by an injective integral one inside its support, of no larger cost
(Birkhoff–von Neumann). -/
lemma st_matching {n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (x : Fin n → S → ℝ) (hx0 : ∀ j s, 0 ≤ x j s) (hrow : ∀ j, ∑ s, x j s = 1)
    (hcol : ∀ s, ∑ j, x j s ≤ 1) (cs : Fin n → S → ℝ) :
    ∃ f : Fin n → S, Function.Injective f ∧ (∀ j, 0 < x j (f j)) ∧
      ∑ j, cs j (f j) ≤ ∑ j, ∑ s, cs j s * x j s := by
  classical
  let D : Matrix (Fin n ⊕ S) (Fin n ⊕ S) ℝ := fun a b =>
    match a, b with
    | Sum.inl _, Sum.inl _ => 0
    | Sum.inl j, Sum.inr s => x j s
    | Sum.inr s, Sum.inl j => x j s
    | Sum.inr s, Sum.inr s' => if s = s' then 1 - ∑ j, x j s else 0
  have hD : D ∈ doublyStochastic ℝ (Fin n ⊕ S) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨?_, ?_, ?_⟩
    · rintro (j | s) (j' | s')
      · exact le_rfl
      · exact hx0 j s'
      · exact hx0 j' s
      · show 0 ≤ (if s = s' then 1 - ∑ j, x j s else 0)
        split_ifs
        · linarith [hcol s]
        · exact le_rfl
    · rintro (j | s)
      · rw [Fintype.sum_sum_type]
        show ∑ _j' : Fin n, (0:ℝ) + ∑ s, x j s = 1
        simp [hrow j]
      · rw [Fintype.sum_sum_type]
        show ∑ j, x j s + ∑ s', (if s = s' then 1 - ∑ j, x j s else 0) = 1
        rw [sum_ite_eq]
        simp
    · rintro (j | s)
      · rw [Fintype.sum_sum_type]
        show ∑ _j' : Fin n, (0:ℝ) + ∑ s, x j s = 1
        simp [hrow j]
      · rw [Fintype.sum_sum_type]
        show ∑ j, x j s + ∑ s', (if s' = s then 1 - ∑ j, x j s' else 0) = 1
        rw [sum_ite_eq']
        simp
  obtain ⟨w, hw0, hw1, hwD⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hD
  have hentry : ∀ a b, D a b = ∑ π, w π * (if π a = b then 1 else 0) := by
    intro a b
    rw [← hwD]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, st_permMatrix_apply]
  -- the cost functional
  let F : Equiv.Perm (Fin n ⊕ S) → ℝ := fun π =>
    ∑ j, ∑ s, cs j s * (if π (Sum.inl j) = Sum.inr s then 1 else 0)
  have hV : ∑ j, ∑ s, cs j s * x j s = ∑ π, w π * F π := by
    have h1 : ∀ j s, cs j s * x j s = ∑ π, w π * (cs j s *
        (if π (Sum.inl j) = Sum.inr s then 1 else 0)) := by
      intro j s
      have := hentry (Sum.inl j) (Sum.inr s)
      change x j s = _ at this
      rw [this, mul_sum]
      exact sum_congr rfl (fun π _ => by ring)
    calc ∑ j, ∑ s, cs j s * x j s
        = ∑ j, ∑ s, ∑ π, w π * (cs j s *
            (if π (Sum.inl j) = Sum.inr s then 1 else 0)) :=
          sum_congr rfl (fun j _ => sum_congr rfl (fun s _ => h1 j s))
      _ = ∑ j, ∑ π, ∑ s, w π * (cs j s *
            (if π (Sum.inl j) = Sum.inr s then 1 else 0)) :=
          sum_congr rfl (fun j _ => sum_comm)
      _ = ∑ π, ∑ j, ∑ s, w π * (cs j s *
            (if π (Sum.inl j) = Sum.inr s then 1 else 0)) := sum_comm
      _ = ∑ π, w π * F π := sum_congr rfl (fun π _ => by simp only [F, mul_sum])
  have hex : ∃ π, 0 < w π ∧ F π ≤ ∑ j, ∑ s, cs j s * x j s := by
    by_contra hno
    push Not at hno
    have hpos : ∃ π, 0 < w π := by
      by_contra h
      push Not at h
      have : ∑ π, w π ≤ 0 := sum_nonpos (fun π _ => h π)
      linarith
    obtain ⟨π₀, hπ₀⟩ := hpos
    have hlt : ∑ π, w π * (∑ j, ∑ s, cs j s * x j s) < ∑ π, w π * F π := by
      apply sum_lt_sum
      · intro π _
        rcases (hw0 π).lt_or_eq with h | h
        · exact (mul_lt_mul_of_pos_left (hno π h) h).le
        · rw [← h]; simp
      · exact ⟨π₀, mem_univ _, mul_lt_mul_of_pos_left (hno π₀ hπ₀) hπ₀⟩
    rw [← sum_mul, hw1, one_mul, ← hV] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨π, hwπ, hFπ⟩ := hex
  have hDpos : ∀ a, 0 < D a (π a) := by
    intro a
    rw [hentry]
    have : w π * (if π a = π a then (1:ℝ) else 0) ≤
        ∑ π', w π' * (if π' a = π a then 1 else 0) :=
      single_le_sum (f := fun π' => w π' * (if π' a = π a then (1:ℝ) else 0))
        (fun π' _ => mul_nonneg (hw0 π') (by split_ifs <;> norm_num)) (mem_univ π)
    simp only [if_true, mul_one] at this
    linarith
  have hinr : ∀ j, ∃ s, π (Sum.inl j) = Sum.inr s := by
    intro j
    have h := hDpos (Sum.inl j)
    rcases hπ : π (Sum.inl j) with j' | s
    · rw [hπ] at h
      exact absurd h (lt_irrefl 0)
    · exact ⟨s, rfl⟩
  choose f hf using hinr
  refine ⟨f, ?_, ?_, ?_⟩
  · intro j j' hjj
    have : π (Sum.inl j) = π (Sum.inl j') := by rw [hf, hf, hjj]
    exact Sum.inl_injective (π.injective this)
  · intro j
    have h := hDpos (Sum.inl j)
    rw [hf j] at h
    exact h
  · refine le_trans (le_of_eq ?_) hFπ
    simp only [F, hf, Sum.inr.injEq]
    refine sum_congr rfl (fun j _ => ?_)
    simp

theorem solution {m n : ℕ} (p c : Fin m → Fin n → ℝ) (b pmax : ℝ)
    (hp : ∀ i j, 0 ≤ p i j) (y : Fin m → Fin n → ℝ) (hy0 : ∀ i j, 0 ≤ y i j)
    (hy1 : ∀ j, ∑ i, y i j = 1) (hload : ∀ i, ∑ j, p i j * y i j ≤ b)
    (hpmax0 : 0 ≤ pmax) (hpmax : ∀ i j, 0 < y i j → p i j ≤ pmax) :
    ∃ σ : Fin n → Fin m, (∀ j, 0 < y (σ j) j) ∧
      ∑ j, c (σ j) j ≤ ∑ i, ∑ j, c i j * y i j ∧
      ∀ i, ∑ j ∈ Finset.univ.filter (fun j => σ j = i), p i j ≤ b + pmax := by
  classical
  have hyle1 : ∀ i j, y i j ≤ 1 := fun i j => by
    rw [← hy1 j]; exact single_le_sum (f := fun i => y i j) (fun i _ => hy0 i j) (mem_univ i)
  have hsumle : ∀ i, ∑ j, y i j ≤ n := fun i => by
    calc ∑ j, y i j ≤ ∑ _j : Fin n, (1:ℝ) := sum_le_sum (fun j _ => hyle1 i j)
      _ = n := by simp
  have hslots := fun i => st_slots (y i) (p i) (hy0 i) (hsumle i)
  choose x hx0 hxrow hxcol hxsort using hslots
  let X : Fin n → Fin m × Fin n → ℝ := fun j st => x st.1 j st.2
  have hX0 : ∀ j st, 0 ≤ X j st := fun j st => hx0 _ _ _
  have hXrow : ∀ j, ∑ st, X j st = 1 := by
    intro j
    rw [Fintype.sum_prod_type]
    simp only [X, hxrow]
    exact hy1 j
  have hXcol : ∀ st, ∑ j, X j st ≤ 1 := fun st => hxcol st.1 st.2
  obtain ⟨f, hfinj, hfpos, hfcost⟩ := st_matching X hX0 hXrow hXcol (fun j st => c st.1 j)
  have hxy : ∀ i j t, x i j t ≤ y i j := by
    intro i j t
    rw [← hxrow i j]
    exact single_le_sum (f := fun t => x i j t) (fun t _ => hx0 _ _ _) (mem_univ _)
  have hσpos : ∀ j, 0 < y (f j).1 j := fun j => lt_of_lt_of_le (hfpos j) (hxy _ _ _)
  refine ⟨fun j => (f j).1, hσpos, ?_, ?_⟩
  · refine hfcost.trans (le_of_eq ?_)
    calc ∑ j, ∑ st, c st.1 j * X j st = ∑ j, ∑ i, c i j * y i j := by
          refine sum_congr rfl (fun j _ => ?_)
          rw [Fintype.sum_prod_type]
          refine sum_congr rfl (fun i _ => ?_)
          simp only [X]
          rw [← mul_sum, hxrow]
      _ = ∑ i, ∑ j, c i j * y i j := sum_comm
  · intro i
    set J := univ.filter (fun j => (f j).1 = i) with hJ
    have hJi : ∀ j ∈ J, (f j).1 = i := fun j hj => (mem_filter.mp hj).2
    have hTinj : ∀ j ∈ J, ∀ j' ∈ J, (f j).2 = (f j').2 → j = j' := by
      intro j hj j' hj' h
      apply hfinj
      exact Prod.ext (by rw [hJi j hj, hJi j' hj']) h
    rw [← sum_filter_add_sum_filter_not J (fun j => ((f j).2 : ℕ) = 0)]
    set A := J.filter (fun j => ((f j).2 : ℕ) = 0) with hA
    set B := J.filter (fun j => ¬ ((f j).2 : ℕ) = 0) with hB
    have hAle : ∑ j ∈ A, p i j ≤ pmax := by
      have hcard : A.card ≤ 1 := by
        rw [card_le_one]
        intro a ha a' ha'
        have ha1 := mem_filter.mp ha
        have ha2 := mem_filter.mp ha'
        exact hTinj a ha1.1 a' ha2.1 (Fin.ext (by rw [ha1.2, ha2.2]))
      have h1 : ∑ j ∈ A, p i j ≤ A.card • pmax := by
        apply sum_le_card_nsmul
        intro j hj
        have hjJ := (mem_filter.mp hj).1
        have := hσpos j
        rw [hJi j hjJ] at this
        exact hpmax i j this
      rw [nsmul_eq_mul] at h1
      have : (A.card : ℝ) * pmax ≤ 1 * pmax :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hpmax0
      linarith
    let prev : Fin n → Fin n := fun t => ⟨(t : ℕ) - 1, by omega⟩
    let g : Fin n → ℝ := fun t => ∑ j', x i j' t * p i j'
    have hg0 : ∀ t, 0 ≤ g t := fun t => sum_nonneg (fun j' _ => mul_nonneg (hx0 _ _ _) (hp _ _))
    have hBle : ∑ j ∈ B, p i j ≤ b := by
      have h1 : ∀ j ∈ B, p i j ≤ g (prev (f j).2) := by
        intro j hj
        have hj' := mem_filter.mp hj
        have hpos := hfpos j
        simp only [X] at hpos
        rw [hJi j hj'.1] at hpos
        exact hxsort i j (f j).2 (prev (f j).2) (by simp only [prev]; omega) hpos
      have hinj : Set.InjOn (fun j => prev (f j).2) (B : Set (Fin n)) := by
        intro j hj j' hj' h
        have hj1 := mem_filter.mp hj
        have hj2 := mem_filter.mp hj'
        apply hTinj j hj1.1 j' hj2.1
        apply Fin.ext
        have := congrArg Fin.val h
        simp only [prev] at this
        omega
      calc ∑ j ∈ B, p i j ≤ ∑ j ∈ B, g (prev (f j).2) := sum_le_sum h1
        _ = ∑ t ∈ B.image (fun j => prev (f j).2), g t := (sum_image hinj).symm
        _ ≤ ∑ t, g t := sum_le_univ_sum_of_nonneg hg0
        _ = ∑ j', p i j' * y i j' := by
          simp only [g]
          rw [sum_comm]
          refine sum_congr rfl (fun j' _ => ?_)
          rw [← sum_mul, hxrow, mul_comm]
        _ ≤ b := hload i
    linarith
