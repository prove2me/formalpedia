-- Prove2me | solution 1 for SupplyChainTheory.nearest_insertion_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T21:22:34.687614+00:00
-- url     : https://prove2.me/submissions/e62ad1d6-a2d9-4e35-9dd5-55ffabad8af7

import Mathlib
import Definitions.Def_SupplyChainTheory_tsp

open Classical SupplyChainTheory

private lemma rot_eq {m : ℕ} (k : Fin (m + 1)) : finRotate (m + 1) k = k + 1 := finRotate_apply k

/-- `z*` is the length of some tour. -/
private lemma exists_opt_tour {n : ℕ} (c : Fin n → Fin n → ℝ) :
    ∃ τ : Equiv.Perm (Fin n), tourLength c τ = optTourLength c := by
  obtain ⟨τ, hτ⟩ := (Set.range_nonempty (tourLength c)).csInf_mem (Set.finite_range _)
  exact ⟨τ, hτ⟩

/-! ### Majorization: threshold counts control sums -/

/-- If at every threshold `x` at most as many `a`-values as `b`-values reach `x`, and the
`b`-values are nonnegative, then `∑ a ≤ ∑ b`. -/
private lemma sum_le_of_count_le {α β : Type*} (a : α → ℝ) (b : β → ℝ) :
    ∀ (s : Finset α) (t : Finset β), (∀ j ∈ t, 0 ≤ b j) →
      (∀ x : ℝ, (s.filter (fun i => x ≤ a i)).card ≤ (t.filter (fun j => x ≤ b j)).card) →
      ∑ i ∈ s, a i ≤ ∑ j ∈ t, b j := by
  classical
  intro s
  induction hs : s.card generalizing s with
  | zero =>
    intro t hb _
    rw [Finset.card_eq_zero.mp hs, Finset.sum_empty]
    exact Finset.sum_nonneg hb
  | succ N ih =>
    intro t hb hcount
    have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
    -- The largest `a`-value is matched with the largest `b`-value.
    obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image a hsne
    have hpos : 0 < (t.filter (fun j => a i₀ ≤ b j)).card :=
      lt_of_lt_of_le (Finset.card_pos.mpr ⟨i₀, by simp [hi₀]⟩) (hcount (a i₀))
    obtain ⟨j₀, hj₀⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hj₀
    obtain ⟨j₁, hj₁, hbmax⟩ := t.exists_max_image b ⟨j₀, hj₀.1⟩
    have hj₁a : a i₀ ≤ b j₁ := hj₀.2.trans (hbmax j₀ hj₀.1)
    rw [← Finset.add_sum_erase s a hi₀, ← Finset.add_sum_erase t b hj₁]
    have hrest : ∑ i ∈ s.erase i₀, a i ≤ ∑ j ∈ t.erase j₁, b j := by
      refine ih (s.erase i₀) (by rw [Finset.card_erase_of_mem hi₀]; omega) (t.erase j₁)
        (fun j hj => hb j (Finset.mem_of_mem_erase hj)) (fun x => ?_)
      by_cases hx : x ≤ a i₀
      · have h1 : ((s.erase i₀).filter (fun i => x ≤ a i)).card + 1
            = (s.filter (fun i => x ≤ a i)).card := by
          rw [Finset.filter_erase, Finset.card_erase_add_one (by simp [hi₀, hx])]
        have h2 : ((t.erase j₁).filter (fun j => x ≤ b j)).card + 1
            = (t.filter (fun j => x ≤ b j)).card := by
          rw [Finset.filter_erase, Finset.card_erase_add_one (by simp [hj₁, hx.trans hj₁a])]
        have := hcount x
        omega
      · have : (s.erase i₀).filter (fun i => x ≤ a i) = ∅ := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.notMem_empty, iff_false]
          rintro ⟨⟨-, hi⟩, hxi⟩
          exact hx (hxi.trans (hmax i hi))
        rw [this, Finset.card_empty]; exact Nat.zero_le _
    linarith
/-! ### Closed tours given as lists -/

/-- The last element of `h :: t`. -/
private def lastD {α : Type*} : α → List α → α
  | h, [] => h
  | _, b :: t => lastD b t

/-- The length of the open path through a list. -/
private def pathLen {n : ℕ} (c : Fin n → Fin n → ℝ) : List (Fin n) → ℝ
  | a :: b :: l => c a b + pathLen c (b :: l)
  | _ => 0

private lemma zipWith_append_sum {n : ℕ} (c : Fin n → Fin n → ℝ) (e : Fin n) :
    ∀ (h : Fin n) (t : List (Fin n)),
      (List.zipWith c (h :: t) (t ++ [e])).sum = pathLen c (h :: t) + c (lastD h t) e
  | h, [] => by simp [pathLen, lastD]
  | h, b :: t => by
    rw [List.cons_append, List.zipWith_cons_cons, List.sum_cons, zipWith_append_sum c e b t]
    simp only [pathLen, lastD]; ring

/-- A closed tour is its open path plus the closing edge. -/
private lemma cycleLength_cons {n : ℕ} (c : Fin n → Fin n → ℝ) (h : Fin n) (t : List (Fin n)) :
    cycleLength c (h :: t) = pathLen c (h :: t) + c (lastD h t) h := by
  rw [cycleLength, List.rotate_cons_succ, List.rotate_zero, zipWith_append_sum]

private lemma pathLen_append {n : ℕ} (c : Fin n → Fin n → ℝ) (e : Fin n) :
    ∀ (h : Fin n) (t : List (Fin n)), pathLen c (h :: (t ++ [e])) = pathLen c (h :: t) + c (lastD h t) e
  | h, [] => by simp [pathLen, lastD]
  | h, b :: t => by
    rw [List.cons_append]
    simp only [pathLen, lastD]
    rw [pathLen_append c e b t]; ring

private lemma lastD_append {α : Type*} (e : α) : ∀ (h : α) (t : List α), lastD h (t ++ [e]) = e
  | _, [] => rfl
  | _, b :: t => lastD_append e b t

/-- Rotating a closed tour does not change its length. -/
private lemma cycleLength_rotate_one {n : ℕ} (c : Fin n → Fin n → ℝ) (L : List (Fin n)) :
    cycleLength c (L.rotate 1) = cycleLength c L := by
  rcases L with _ | ⟨a, l⟩
  · rfl
  rw [List.rotate_cons_succ, List.rotate_zero]
  rcases l with _ | ⟨b, l⟩
  · rfl
  rw [List.cons_append, cycleLength_cons, cycleLength_cons, pathLen_append, lastD_append]
  simp only [pathLen, lastD]; ring

private lemma cycleLength_rotate {n : ℕ} (c : Fin n → Fin n → ℝ) (L : List (Fin n)) (r : ℕ) :
    cycleLength c (L.rotate r) = cycleLength c L := by
  induction r with
  | zero => rw [List.rotate_zero]
  | succ r ih => rw [← List.rotate_rotate, cycleLength_rotate_one, ih]

private lemma insertIdx_eq_take_drop {α : Type*} (x : α) :
    ∀ (i : ℕ) (l : List α), i ≤ l.length → l.insertIdx i x = l.take i ++ x :: l.drop i
  | 0, l, _ => by simp
  | i + 1, [], h => by simp at h
  | i + 1, a :: l, h => by
    rw [List.insertIdx_succ_cons, insertIdx_eq_take_drop x i l (by simpa using h)]
    simp

/-- **Insertion cost.** Inserting `x` right after the node `m = L[i]` lengthens a closed tour by
at most `2 c(m, x)`. -/
private lemma cycleLength_insert_le {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c)
    (L : List (Fin n)) (i : ℕ) (hi : i < L.length) (x : Fin n) :
    cycleLength c (L.insertIdx (i + 1) x) ≤ cycleLength c L + 2 * c L[i] x := by
  -- Rotate so that `m = L[i]` comes first: `L ~ m :: t` and the insertion `~ m :: x :: t`.
  set A := L.take i with hA
  set t := L.drop (i + 1) ++ A with ht
  have hAlen : A.length = i := by rw [hA, List.length_take]; omega
  have hL : L = A ++ (L[i] :: L.drop (i + 1)) := by
    rw [hA, ← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hins : L.insertIdx (i + 1) x = A ++ ([L[i]] ++ x :: L.drop (i + 1)) := by
    rw [insertIdx_eq_take_drop x (i + 1) L (by omega), List.take_add_one, List.getElem?_eq_getElem hi]
    simp only [Option.toList_some, List.append_assoc, List.cons_append, hA, List.nil_append]
  have h1 : cycleLength c L = cycleLength c (L[i] :: t) := by
    conv_lhs => rw [hL, ← cycleLength_rotate c _ A.length, List.rotate_append_length_eq]
    simp only [List.cons_append, ht]
  have h2 : cycleLength c (L.insertIdx (i + 1) x) = cycleLength c (L[i] :: x :: t) := by
    rw [hins, ← cycleLength_rotate c _ A.length, List.rotate_append_length_eq]
    simp only [List.cons_append, List.nil_append, ht]
  rw [h1, h2]
  -- Compare the two closed tours through `m`.
  rcases t with _ | ⟨h, t'⟩
  · rw [cycleLength_cons, cycleLength_cons]
    simp only [pathLen, lastD]
    rw [hc.symm x L[i], hc.refl]; ring_nf; rfl
  · rw [cycleLength_cons, cycleLength_cons]
    simp only [pathLen, lastD]
    have := hc.triangle x h L[i]
    rw [hc.symm x L[i]] at this
    linarith

/-- The distance to a nonempty partial tour is attained, and bounded by every tour node. -/
private lemma distToTour_spec {n : ℕ} (c : Fin n → Fin n → ℝ) (S : List (Fin n)) (hS : S ≠ [])
    (y : Fin n) : (∃ a ∈ S, distToTour c S y = c a y) ∧ ∀ a ∈ S, distToTour c S y ≤ c a y := by
  have hfin : ((fun m => c m y) '' {m | m ∈ S}).Finite := (List.finite_toSet S).image _
  obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil hS
  have hne : ((fun m => c m y) '' {m | m ∈ h :: t}).Nonempty := ⟨c h y, h, by simp, rfl⟩
  refine ⟨?_, fun a ha => csInf_le hfin.bddBelow ⟨a, ha, rfl⟩⟩
  obtain ⟨a, ha, hay⟩ := hne.csInf_mem hfin
  exact ⟨a, ha, hay.symm⟩

theorem solution {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 1 ≤ n)
    (L : ℕ → List (Fin n)) (hL : IsNearestInsertionRun c L) :
    cycleLength c (L (n - 1)) ≤ 2 * optTourLength c := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨⟨i₀, hL0⟩, hstep⟩ := hL
  choose! x pos hx hnear hpos hLsucc hbest using hstep
  -- Invariants of the run: partial tours are nonempty and grow by the inserted node.
  have hmem : ∀ k, k < m → ∀ y, y ∈ L (k + 1) ↔ y = x k ∨ y ∈ L k := by
    intro k hk y; rw [hLsucc k (by omega), List.mem_insertIdx (hpos k (by omega))]
  have hne : ∀ k, k ≤ m → L k ≠ [] := by
    intro k hk
    induction k with
    | zero => rw [hL0]; simp
    | succ k ih =>
      intro h
      have := (hmem k (by omega) (x k)).mpr (Or.inl rfl)
      rw [h] at this; simp at this
  set d : ℕ → ℝ := fun k => distToTour c (L k) (x k) with hd
  -- Each insertion costs at most `2 d k`.
  have hcost : ∀ k, k < m → cycleLength c (L (k + 1)) ≤ cycleLength c (L k) + 2 * d k := by
    intro k hk
    obtain ⟨a, ha, hda⟩ := (distToTour_spec c (L k) (hne k (by omega)) (x k)).1
    set i := (L k).idxOf a with hi
    have hilt : i < (L k).length := List.idxOf_lt_length_of_mem ha
    have hget : (L k)[i] = a := List.getElem_idxOf hilt
    have := hbest k (by omega) (i + 1) hilt
    have hins := cycleLength_insert_le c hc (L k) i hilt (x k)
    rw [hget] at hins
    simp only [hd, hda]
    linarith
  have htotal : ∀ K, K ≤ m → cycleLength c (L K) ≤ 2 * ∑ k ∈ Finset.range K, d k := by
    intro K hK
    induction K with
    | zero => rw [hL0, cycleLength_cons]; simp [pathLen, lastD, hc.refl]
    | succ K ih =>
      rw [Finset.sum_range_succ]
      linarith [hcost K (by omega), ih (by omega)]
  -- The inserted distances are at most the optimal tour length.
  obtain ⟨τ, hτ⟩ := exists_opt_tour c
  set h : ℕ → Fin (m + 1) := fun j => τ ⟨j % (m + 1), Nat.mod_lt _ (by omega)⟩ with hh
  set w : ℕ → ℝ := fun j => c (h j) (h (j + 1)) with hw
  have hpath : ∑ j ∈ Finset.range m, w j ≤ optTourLength c := by
    have htour : ∑ j ∈ Finset.range (m + 1), w j = tourLength c τ := by
      rw [tourLength, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hw, hh, rot_eq]
      congr 2
      · ext; simp [Nat.mod_eq_of_lt i.isLt]
      · ext; simp [Fin.val_add, Nat.add_mod_mod]
    rw [← hτ, ← htour, Finset.sum_range_succ]
    linarith [hc.nonneg (h m) (h (m + 1))]
  have hd_le : ∑ k ∈ Finset.range m, d k ≤ ∑ j ∈ Finset.range m, w j := by
    refine sum_le_of_count_le d w _ _ (fun j _ => hc.nonneg _ _) (fun t => ?_)
    -- Segment ids along the optimal tour's path: number of heavy edges before a node.
    set p : Fin (m + 1) → ℕ := fun v => (τ.symm v).val with hp
    set seg : Fin (m + 1) → ℕ := fun v => ((Finset.range (p v)).filter (fun j => t ≤ w j)).card
      with hseg
    have hhp : ∀ v, h (p v) = v := by
      intro v; simp only [hh, hp, Nat.mod_eq_of_lt (τ.symm v).isLt, Fin.eta, Equiv.apply_symm_apply]
    have hseg_le : ∀ v, seg v ≤ ((Finset.range m).filter (fun j => t ≤ w j)).card := by
      intro v
      refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
      intro j; simp only [Finset.mem_range]; have := (τ.symm v).isLt; simp only [hp]; omega
    -- Sets that no light edge leaves are unions of segments.
    have hclosed : ∀ T : Finset (Fin (m + 1)), (∀ a ∈ T, ∀ y ∉ T, t ≤ c a y) →
        ∀ u v, seg u = seg v → (u ∈ T ↔ v ∈ T) := by
      intro T hT
      have hlight : ∀ j, w j < t → (h j ∈ T ↔ h (j + 1) ∈ T) := by
        intro j hj
        constructor
        · intro h1; by_contra h2; exact absurd (hT _ h1 _ h2) (not_le.mpr hj)
        · intro h2; by_contra h1
          have := hT _ h2 _ h1
          rw [hc.symm] at this; exact absurd this (not_le.mpr hj)
      have key : ∀ u v, p u ≤ p v → seg u = seg v → (u ∈ T ↔ v ∈ T) := by
        intro u v huv hs
        have hnone : ∀ j, p u ≤ j → j < p v → w j < t := by
          intro j hj1 hj2
          by_contra hjt
          push Not at hjt
          have hsplit := Finset.sum_range_add_sum_Ico (fun j => if t ≤ w j then 1 else 0) huv
          simp only [← Finset.card_filter] at hsplit
          have hpos : 0 < ((Finset.Ico (p u) (p v)).filter (fun j => t ≤ w j)).card :=
            Finset.card_pos.mpr ⟨j, by simp [hj1, hj2, hjt]⟩
          simp only [hseg] at hs
          omega
        have hchain : ∀ k, p u + k ≤ p v → (u ∈ T ↔ h (p u + k) ∈ T) := by
          intro k
          induction k with
          | zero => intro _; show u ∈ T ↔ h (p u) ∈ T; rw [hhp]
          | succ k ih =>
            intro hk
            rw [ih (by omega), ← Nat.add_assoc]
            exact hlight _ (hnone _ (by omega) (by omega))
        have := hchain (p v - p u) (by omega)
        rwa [Nat.add_sub_cancel' huv, hhp] at this
      intro u v hs
      rcases le_total (p u) (p v) with huv | hvu
      · exact key u v huv hs
      · exact (key v u hvu hs.symm).symm
    -- Every heavy insertion enters a new segment.
    have hgrow : ∀ K, K ≤ m → ((Finset.range K).filter (fun k => t ≤ d k)).card + 1
        ≤ ((L K).toFinset.image seg).card := by
      intro K hK
      induction K with
      | zero => rw [hL0]; simp
      | succ K ih =>
        have hset : (L (K + 1)).toFinset = insert (x K) (L K).toFinset := by
          ext y; simp only [List.mem_toFinset, Finset.mem_insert]; exact hmem K (by omega) y
        rw [hset, Finset.image_insert, Finset.range_add_one, Finset.filter_insert]
        have ih' := ih (by omega)
        by_cases hK' : t ≤ d K
        · rw [if_pos hK']
          have hnotin : seg (x K) ∉ (L K).toFinset.image seg := by
            rw [Finset.mem_image]
            rintro ⟨a, ha, hsa⟩
            have hTc : ∀ a ∈ (L K).toFinset, ∀ y ∉ (L K).toFinset, t ≤ c a y := by
              intro a ha y hy
              rw [List.mem_toFinset] at ha hy
              have h1 := hnear K (by omega) y hy
              have h2 := (distToTour_spec c (L K) (hne K (by omega)) y).2 a ha
              simp only [hd] at hK'
              linarith
            have := (hclosed _ hTc a (x K) hsa).mp ha
            rw [List.mem_toFinset] at this
            exact hx K (by omega) this
          rw [Finset.card_insert_of_notMem hnotin,
            Finset.card_insert_of_notMem (by simp)]
          omega
        · rw [if_neg hK']
          exact ih'.trans (Finset.card_le_card (Finset.subset_insert _ _))
    have hfinal := hgrow m le_rfl
    have hbound : ((L m).toFinset.image seg).card
        ≤ ((Finset.range m).filter (fun j => t ≤ w j)).card + 1 := by
      calc ((L m).toFinset.image seg).card
          ≤ (Finset.range (((Finset.range m).filter (fun j => t ≤ w j)).card + 1)).card := by
            refine Finset.card_le_card (fun s hs => ?_)
            rw [Finset.mem_image] at hs
            obtain ⟨v, _, rfl⟩ := hs
            rw [Finset.mem_range]; exact Nat.lt_succ_of_le (hseg_le v)
        _ = _ := Finset.card_range _
    omega
  linarith [htotal m le_rfl]
