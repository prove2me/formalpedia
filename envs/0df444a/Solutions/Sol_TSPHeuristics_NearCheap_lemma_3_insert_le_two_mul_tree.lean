-- Prove2me | solution 1 for TSPHeuristics.NearCheap.lemma_3_insert_le_two_mul_tree
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:36:07.125572+00:00
-- url     : https://prove2.me/submissions/0a4c56ae-6546-4403-b3dc-b875c3b23f30

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion
import Definitions.Def_TSPHeuristics_NearCheap_SpanningTree

open Classical


namespace TSPHeuristics.NearCheap

open TSPHeuristics.Shared

/-- path sum from x through L to y -/
def PS {n : ℕ} (d : Fin n → Fin n → ℝ) (x : Fin n) (L : List (Fin n)) (y : Fin n) : ℝ :=
  (List.zipWith d (x :: L) (L ++ [y])).sum

lemma PS_nil {n : ℕ} (d : Fin n → Fin n → ℝ) (x y : Fin n) : PS d x [] y = d x y := by
  simp [PS]

lemma PS_cons {n : ℕ} (d : Fin n → Fin n → ℝ) (x h y : Fin n) (L : List (Fin n)) :
    PS d x (h :: L) y = d x h + PS d h L y := by
  simp [PS]

lemma PS_append {n : ℕ} (d : Fin n → Fin n → ℝ) (L1 : List (Fin n)) :
    ∀ (x z y : Fin n) (L2 : List (Fin n)), PS d x (L1 ++ z :: L2) y = PS d x L1 z + PS d z L2 y := by
  induction L1 with
  | nil => intro x z y L2; simp [PS_cons, PS_nil]
  | cons h L ih => intro x z y L2; rw [List.cons_append, PS_cons, PS_cons, ih]; ring

lemma cycle_cons {n : ℕ} (d : Fin n → Fin n → ℝ) (x : Fin n) (L : List (Fin n)) :
    cycleLength d (x :: L) = PS d x L x := by
  simp [cycleLength, PS]

lemma cycle_swap {n : ℕ} (d : Fin n → Fin n → ℝ) (A B : List (Fin n)) :
    cycleLength d (A ++ B) = cycleLength d (B ++ A) := by
  rcases A with _ | ⟨x, A'⟩
  · simp
  rcases B with _ | ⟨z, B'⟩
  · simp
  rw [List.cons_append, List.cons_append, cycle_cons, cycle_cons, PS_append, PS_append]
  ring

lemma PS_le {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) (k j : Fin n) (B : List (Fin n)) :
    PS d k B j ≤ d k j + PS d j B j := by
  rcases B with _ | ⟨h, B'⟩
  · simp [PS_nil, hd.diag]
  · rw [PS_cons, PS_cons]; linarith [hd.triangle k j h]

lemma insertIdx_split {α : Type*} (A B : List α) (j k : α) :
    (A ++ j :: B).insertIdx (A.length + 1) k = A ++ j :: k :: B := by
  induction A with
  | nil => simp
  | cons x A ih => simp [List.insertIdx_succ_cons, ih]

lemma lemma2_core {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d)
    (T : List (Fin n)) (k j : Fin n) (hj : j ∈ T) :
    insCost d T k ≤ 2 * d k j := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hj
  unfold insCost
  have hmem : A.length + 1 ∈ Finset.range ((A ++ j :: B).length + 1) := by
    simp
  have h1 := Finset.inf'_le (fun pos => cycleLength d ((A ++ j :: B).insertIdx pos k)) hmem
  rw [insertIdx_split] at h1
  have e1 : cycleLength d (A ++ j :: k :: B) = d j k + PS d k (B ++ A) j := by
    rw [cycle_swap, List.cons_append, List.cons_append, cycle_cons, PS_cons]
  have e2 : cycleLength d (A ++ j :: B) = PS d j (B ++ A) j := by
    rw [cycle_swap, List.cons_append, cycle_cons]
  have := PS_le d hd k j (B ++ A)
  rw [hd.symm j k] at e1
  linarith

theorem insertion_cost_eq {n : ℕ} (d : Fin n → Fin n → ℝ) (T : List (Fin n)) (k : Fin n)
    (T' : List (Fin n)) (h : IsInsertion d T k T') :
    insCost d T k = cycleLength d T' - cycleLength d T := by
  obtain ⟨_, pos, hpos, rfl, hmin⟩ := h
  unfold insCost
  congr 1
  apply le_antisymm
  · exact Finset.inf'_le (fun pos => cycleLength d (T.insertIdx pos k))
      (Finset.mem_range.mpr (by omega))
  · apply Finset.le_inf'
    intro p hp
    exact hmin p (by simpa [Nat.lt_succ_iff] using hp)

theorem eq37_core {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : IsTSPDist d) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    cycleLength d (T n) = ∑ i ∈ Finset.Ico 1 n, insCost d (T i) (a i) := by
  have key : ∀ m, 1 ≤ m → m ≤ n → cycleLength d (T m) = ∑ i ∈ Finset.Ico 1 m, insCost d (T i) (a i) := by
    intro m hm1 hmn
    induction m with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0; rw [hrun.1]; simp [cycleLength, hd.diag]
      · rw [Finset.sum_Ico_succ_top hpos, ← ih hpos (by omega),
          insertion_cost_eq d _ _ _ (hrun.2 m hpos (by omega))]
        ring
  exact key n hn le_rfl

theorem nearest_core {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d)
    (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a)
    (hrule : IsNearestRule d T a) :
    ∀ i, 1 ≤ i → i < n → ∀ p ∈ T i, ∀ q, q ∉ T i →
      insCost d (T i) (a i) ≤ 2 * d p q := by
  intro i hi hin p hp q hq
  have hne : (T i).toFinset.Nonempty := ⟨p, by simpa using hp⟩
  obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_inf (T i).toFinset hne (fun x => ((d x (a i) : ℝ) : WithTop ℝ))
  have h1 := hrule i hi hin q hq
  unfold distToTour at h1
  rw [hxe] at h1
  have h2 : (T i).toFinset.inf (fun x => ((d x q : ℝ) : WithTop ℝ)) ≤ ((d p q : ℝ) : WithTop ℝ) :=
    Finset.inf_le (f := fun x => ((d x q : ℝ) : WithTop ℝ)) (by simpa using hp)
  have h3 : d x (a i) ≤ d p q := WithTop.coe_le_coe.mp (h1.trans h2)
  have h4 := lemma2_core d hd (T i) (a i) x (by simpa using hx)
  rw [hd.symm] at h4
  linarith

theorem cheapest_core {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d)
    (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a)
    (hrule : IsCheapestRule d T a) :
    ∀ i, 1 ≤ i → i < n → ∀ p ∈ T i, ∀ q, q ∉ T i →
      insCost d (T i) (a i) ≤ 2 * d p q := by
  intro i hi hin p hp q hq
  have h1 := hrule i hi hin q hq
  have h2 := lemma2_core d hd (T i) q p hp
  rw [hd.symm] at h2
  linarith

lemma edgeLen_mk {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) (x y : Fin n) :
    edgeLen d s(x, y) = d x y := by
  simp [edgeLen, hd.symm y x]

lemma edgeLen_nonneg {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) (e : Sym2 (Fin n)) :
    0 ≤ edgeLen d e := by
  induction e using Sym2.ind with
  | h x y => rw [edgeLen_mk d hd]; exact hd.nonneg x y

lemma run_mem {n : ℕ} (d : Fin n → Fin n → ℝ) (T : ℕ → List (Fin n)) (a : ℕ → Fin n)
    (hrun : IsInsertionRun d T a) :
    ∀ j, 1 ≤ j → j ≤ n → ∀ x, x ∈ T j ↔ ∃ i < j, a i = x := by
  intro j hj hjn
  induction j with
  | zero => omega
  | succ j ih =>
    intro x
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; rw [hrun.1]; simp [eq_comm]
    · obtain ⟨_, pos, hpos', hT, _⟩ := hrun.2 j hpos (by omega)
      rw [hT, List.mem_insertIdx hpos', ih hpos (by omega)]
      constructor
      · rintro (h | ⟨i, hi, rfl⟩)
        · exact ⟨j, by omega, h.symm⟩
        · exact ⟨i, by omega, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact Or.inr ⟨i, h, rfl⟩
        · exact Or.inl (by rw [h])

lemma run_mem_iff {n : ℕ} (d : Fin n → Fin n → ℝ) (T : ℕ → List (Fin n)) (a : ℕ → Fin n)
    (hrun : IsInsertionRun d T a) :
    ∀ j, 1 ≤ j → j ≤ n → ∀ i, i < n → (a i ∈ T j ↔ i < j) := by
  intro j hj hjn i hi
  rw [run_mem d T a hrun j hj hjn]
  constructor
  · rintro ⟨i', hi', he⟩
    by_contra hij
    have h1 : 1 ≤ i := by omega
    have hnot := (hrun.2 i h1 hi).1
    apply hnot
    rw [run_mem d T a hrun i h1 hi.le]
    exact ⟨i', by omega, he⟩
  · intro h; exact ⟨i, h, rfl⟩

theorem lemma3_core {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : IsTSPDist d) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a)
    (h45 : ∀ i, 1 ≤ i → i < n → ∀ p ∈ T i, ∀ q, q ∉ T i →
      insCost d (T i) (a i) ≤ 2 * d p q)
    (M : SimpleGraph (Fin n)) (hM : M.IsTree) :
    cycleLength d (T n) ≤ 2 * treeWeight d M := by
  let t : (Finset.Ico 1 n) → Finset (Sym2 (Fin n)) := fun i =>
    M.edgeFinset.filter (fun e => ∃ p q, e = s(p, q) ∧ p ∈ T i.1 ∧ q ∉ T i.1)
  have hall : ∀ s : Finset (Finset.Ico 1 n), s.card ≤ (s.biUnion t).card := by
    intro s
    let ℓ : Fin n → ℕ := fun v => (s.filter (fun i => v ∉ T i.1)).card
    let W : Finset ℕ := Finset.univ.image ℓ
    let f : Fin n → W := fun v => ⟨ℓ v, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    let Q : SimpleGraph W :=
      { Adj := fun x y => x ≠ y ∧ ∃ u v, M.Adj u v ∧ f u = x ∧ f v = y
        symm := ⟨fun x y ⟨hxy, u, v, huv, hu, hv⟩ => ⟨hxy.symm, v, u, huv.symm, hv, hu⟩⟩
        loopless := ⟨fun x h => h.1 rfl⟩ }
    have hwalk : ∀ u v (p : M.Walk u v), Q.Reachable (f u) (f v) := by
      intro u v p
      induction p with
      | nil => rfl
      | cons h p ih =>
        rename_i u' w' _
        refine SimpleGraph.Reachable.trans ?_ ih
        by_cases hfe : f u' = f w'
        · rw [hfe]
        · exact SimpleGraph.Adj.reachable ⟨hfe, _, _, h, rfl, rfl⟩
    have hQconn : Q.Connected := by
      rw [SimpleGraph.connected_iff]
      constructor
      · rintro ⟨x, hx⟩ ⟨y, hy⟩
        obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨p⟩ := hM.connected.preconnected u v
        exact hwalk u v p
      · exact ⟨f (a 0)⟩
    have h1 := hQconn.card_vert_le_card_edgeSet_add_one
    -- lower bound on W
    have hℓ0 : ℓ (a 0) = 0 := by
      simp only [ℓ, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i hi hnot
      apply hnot
      have hi' := Finset.mem_Ico.mp i.2
      exact (run_mem_iff d T a hrun i.1 hi'.1 hi'.2.le 0 (by omega)).mpr (by omega)
    have hℓi : ∀ i ∈ s, ∀ i' ∈ s, i.1 ≤ i'.1 → (s.filter (fun j : (Finset.Ico 1 n) => a i.1 ∉ T j.1)) ⊆
        (s.filter (fun j : (Finset.Ico 1 n) => a i'.1 ∉ T j.1)) := by
      intro i hi i' hi' hle j hj
      simp only [Finset.mem_filter] at hj ⊢
      refine ⟨hj.1, ?_⟩
      have hj' := Finset.mem_Ico.mp j.2
      have hi2 := Finset.mem_Ico.mp i.2
      have hi2' := Finset.mem_Ico.mp i'.2
      rw [run_mem_iff d T a hrun j.1 hj'.1 hj'.2.le _ hi2.2] at hj
      rw [run_mem_iff d T a hrun j.1 hj'.1 hj'.2.le _ hi2'.2]
      omega
    have hself : ∀ i ∈ s, i ∈ s.filter (fun j : (Finset.Ico 1 n) => a i.1 ∉ T j.1) := by
      intro i hi
      simp only [Finset.mem_filter]
      refine ⟨hi, ?_⟩
      have hi2 := Finset.mem_Ico.mp i.2
      rw [run_mem_iff d T a hrun i.1 hi2.1 hi2.2.le _ hi2.2]
      omega
    have hstrict : ∀ i ∈ s, ∀ i' ∈ s, i.1 < i'.1 → ℓ (a i.1) < ℓ (a i'.1) := by
      intro i hi i' hi' hlt
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (hℓi i hi i' hi' hlt.le)]
      refine ⟨i', hself i' hi', ?_⟩
      simp only [Finset.mem_filter, not_and, not_not]
      intro _
      have hj' := Finset.mem_Ico.mp i'.2
      have hi2 := Finset.mem_Ico.mp i.2
      rw [run_mem_iff d T a hrun i'.1 hj'.1 hj'.2.le _ hi2.2]
      exact hlt
    have hpos : ∀ i ∈ s, 0 < ℓ (a i.1) :=
      fun i hi => Finset.card_pos.mpr ⟨i, hself i hi⟩
    have hinj : Set.InjOn (fun i : (Finset.Ico 1 n) => ℓ (a i.1)) s := by
      intro i hi i' hi' h
      simp only at h
      rcases lt_trichotomy i.1 i'.1 with hlt | heq | hgt
      · exact absurd h (hstrict i hi i' hi' hlt).ne
      · exact Subtype.ext heq
      · exact absurd h (hstrict i' hi' i hi hgt).ne'
    have hWcard : s.card + 1 ≤ W.card := by
      have hsub : insert 0 (s.image (fun i : (Finset.Ico 1 n) => ℓ (a i.1))) ⊆ W := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · rw [← hℓ0]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem, Finset.card_image_of_injOn hinj] at this
      · exact this
      · intro h0
        obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h0
        exact (hpos i hi).ne' he
    -- edges of Q come from crossing edges
    have hQE : Q.edgeSet ⊆ ((s.biUnion t).image (Sym2.map f) : Set (Sym2 W)) := by
      intro e he
      induction e using Sym2.ind with
      | h x y =>
        obtain ⟨hxy, u, v, huv, rfl, rfl⟩ := he
        have hne : ℓ u ≠ ℓ v := fun h => hxy (Subtype.ext h)
        have : ∃ i ∈ s, ¬ (u ∈ T i.1 ↔ v ∈ T i.1) := by
          by_contra hcon
          push_neg at hcon
          apply hne
          simp only [ℓ]
          congr 1
          apply Finset.filter_congr
          intro i hi
          rw [hcon i hi]
        obtain ⟨i, hi, hiff⟩ := this
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_biUnion]
        refine ⟨s(u, v), ⟨i, hi, ?_⟩, by simp⟩
        simp only [t, Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        refine ⟨huv, ?_⟩
        by_cases hu : u ∈ T i.1
        · exact ⟨u, v, rfl, hu, fun hv => hiff ⟨fun _ => hv, fun _ => hu⟩⟩
        · have hv : v ∈ T i.1 := by
            by_contra hv; exact hiff ⟨fun h => absurd h hu, fun h => absurd h hv⟩
          exact ⟨v, u, Sym2.eq_swap, hv, hu⟩
    have h2 : Nat.card Q.edgeSet ≤ (s.biUnion t).card := by
      rw [Nat.card_coe_set_eq]
      calc Q.edgeSet.ncard ≤ (((s.biUnion t).image (Sym2.map f) : Finset (Sym2 W)) : Set (Sym2 W)).ncard :=
            Set.ncard_le_ncard hQE (Finset.finite_toSet _)
        _ = ((s.biUnion t).image (Sym2.map f)).card := Set.ncard_coe_finset _
        _ ≤ (s.biUnion t).card := Finset.card_image_le
    have h3 : Nat.card W = W.card := Nat.card_eq_finsetCard W
    omega
  obtain ⟨g, hg, hgt⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  rw [eq37_core hn d hd T a hrun]
  have hstep : ∀ i : (Finset.Ico 1 n), insCost d (T i.1) (a i.1) ≤ 2 * edgeLen d (g i) := by
    intro i
    have := hgt i
    simp only [t, Finset.mem_filter] at this
    obtain ⟨-, p, q, he, hp, hq⟩ := this
    have hi := Finset.mem_Ico.mp i.2
    rw [he, edgeLen_mk d hd]
    exact h45 i.1 hi.1 hi.2 p hp q hq
  have hsubE : Finset.univ.image g ⊆ M.edgeFinset := by
    intro e he
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp (hgt i)).1
  calc ∑ i ∈ Finset.Ico 1 n, insCost d (T i) (a i)
      = ∑ i : (Finset.Ico 1 n), insCost d (T i.1) (a i.1) := (Finset.sum_coe_sort _ _).symm
    _ ≤ ∑ i : (Finset.Ico 1 n), 2 * edgeLen d (g i) := Finset.sum_le_sum (fun i _ => hstep i)
    _ = 2 * ∑ e ∈ Finset.univ.image g, edgeLen d e := by
        rw [Finset.sum_image (fun x _ y _ h => hg h), Finset.mul_sum]
    _ ≤ 2 * ∑ e ∈ M.edgeFinset, edgeLen d e := by
        gcongr
        exact fun e _ _ => edgeLen_nonneg d hd e
    _ = 2 * treeWeight d M := by
        unfold treeWeight
        congr 1

end TSPHeuristics.NearCheap

open TSPHeuristics.NearCheap


theorem solution {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : TSPHeuristics.Shared.IsInsertionRun d T a)
    (h45 : ∀ i, 1 ≤ i → i < n → ∀ p ∈ T i, ∀ q, q ∉ T i →
      TSPHeuristics.Shared.insCost d (T i) (a i) ≤ 2 * d p q)
    (M : SimpleGraph (Fin n)) (hM : M.IsTree) :
    TSPHeuristics.Shared.cycleLength d (T n) ≤ 2 * treeWeight d M := by
  exact lemma3_core hn d hd T a hrun h45 M hM
