-- Prove2me | solution 1 for ReadOnceParityBP.LowerBound.matching_bijection
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-23T23:58:45.802099+00:00
-- url     : https://prove2.me/submissions/b1c9cb1d-a7fb-4ceb-94a4-f5118d01cd75

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_CanonicalMatching

set_option autoImplicit false

open ReadOnceParityBP.LowerBound

/-- Along a chain starting at a point satisfying P and containing a later point violating P,
some consecutive pair passes from P to not P. -/
theorem solM_lin {α : Type} (P : α → Prop) : ∀ (c : List α) (a : α), P a →
    (∃ y ∈ c, ¬ P y) → ∃ q ∈ (a :: c).zip c, P q.1 ∧ ¬ P q.2 := by
  intro c
  induction c with
  | nil =>
    intro a _ h
    obtain ⟨y, hy, -⟩ := h
    simp at hy
  | cons y c ih =>
    intro a ha h
    by_cases hy : P y
    · obtain ⟨z, hz, hPz⟩ := h
      have hz' : z ∈ c := by
        rcases List.mem_cons.mp hz with rfl | hz
        · exact absurd hy hPz
        · exact hz
      obtain ⟨q, hq, h1, h2⟩ := ih y hy ⟨z, hz', hPz⟩
      exact ⟨q, by simp [List.zip_cons_cons, hq], h1, h2⟩
    · exact ⟨(a, y), by simp [List.zip_cons_cons], ha, hy⟩

theorem solM_zip_app {α : Type} : ∀ (l m r : List α), l.length = m.length →
    (l ++ r).zip m = l.zip m := by
  intro l
  induction l with
  | nil =>
    intro m r h
    cases m with
    | nil => simp
    | cons y m => simp at h
  | cons x l ih =>
    intro m r h
    cases m with
    | nil => simp at h
    | cons y m =>
      simp only [List.cons_append, List.zip_cons_cons, List.length_cons] at h ⊢
      rw [ih m r (by omega)]

/-- On a cyclic list containing points with and without P, some cyclically consecutive pair
passes from P to not P. -/
theorem solM_adj {α : Type} (P : α → Prop) (l : List α) (h1 : ∃ x ∈ l, P x)
    (h2 : ∃ y ∈ l, ¬ P y) : ∃ q ∈ l.zip (l.rotate 1), P q.1 ∧ ¬ P q.2 := by
  cases l with
  | nil =>
    obtain ⟨x, hx, -⟩ := h1
    simp at hx
  | cons x rest =>
    have hrot : (x :: rest).rotate 1 = rest ++ [x] := by simp
    rw [hrot]
    by_cases hx : P x
    · obtain ⟨z, hz, hPz⟩ := h2
      have hz' : z ∈ rest ++ [x] := by
        rcases List.mem_cons.mp hz with rfl | hz
        · exact absurd hx hPz
        · simp [hz]
      obtain ⟨q, hq, hq1, hq2⟩ := solM_lin P (rest ++ [x]) x hx ⟨z, hz', hPz⟩
      rw [show x :: (rest ++ [x]) = (x :: rest) ++ [x] by simp,
        solM_zip_app (x :: rest) (rest ++ [x]) [x] (by simp)] at hq
      exact ⟨q, hq, hq1, hq2⟩
    · obtain ⟨y, hy, hPy⟩ := h1
      have hy' : y ∈ rest := by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact absurd hPy hx
        · exact hy
      obtain ⟨r1, r2, rfl⟩ := List.append_of_mem hy'
      obtain ⟨q, hq, hq1, hq2⟩ := solM_lin P (r2 ++ [x]) y hPy ⟨x, by simp, hx⟩
      refine ⟨q, ?_, hq1, hq2⟩
      have e1 : x :: (r1 ++ y :: r2) = (x :: r1) ++ (y :: r2) := by simp
      have e2 : r1 ++ y :: r2 ++ [x] = (r1 ++ [y]) ++ (r2 ++ [x]) := by simp
      rw [e1, e2, List.zip_append (by simp)]
      rw [show y :: (r2 ++ [x]) = (y :: r2) ++ [x] by simp,
        solM_zip_app (y :: r2) (r2 ++ [x]) [x] (by simp)] at hq
      exact List.mem_append_right _ hq

theorem solM_len_remove {α : Type} [DecidableEq α] (a : α) : ∀ l : List α, l.Nodup → a ∈ l →
    (l.filter (fun v => v != a)).length + 1 = l.length := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons x l ih =>
    intro hnd ha
    rw [List.nodup_cons] at hnd
    by_cases hxa : x = a
    · subst hxa
      have hself : l.filter (fun v => v != x) = l := List.filter_eq_self.mpr (fun v hv => by
        simp only [bne_iff_ne, ne_eq]
        rintro rfl
        exact hnd.1 hv)
      rw [List.filter_cons_of_neg (by simp), hself, List.length_cons]
    · have ha' : a ∈ l := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hxa
        · exact h
      have := ih hnd.2 ha'
      rw [List.filter_cons_of_pos (by simpa using hxa), List.length_cons, List.length_cons]
      omega

theorem solM_greedy {n : ℕ} (B : Finset (Fin n)) : ∀ (fuel : ℕ) (l : List (Fin n)),
    l.Nodup → 2 * (l.filter (fun v => decide (v ∈ B))).length = l.length →
    l.length ≤ 2 * fuel →
    (∀ p ∈ greedyPairs B fuel l, p.1 ∈ l ∧ p.1 ∈ B ∧ p.2 ∈ l ∧ p.2 ∉ B) ∧
    ((greedyPairs B fuel l).map Prod.fst).Nodup ∧
    ((greedyPairs B fuel l).map Prod.snd).Nodup ∧
    (∀ j ∈ l, j ∈ B → j ∈ (greedyPairs B fuel l).map Prod.fst) := by
  intro fuel
  induction fuel with
  | zero =>
    intro l _ _ hlen
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [greedyPairs]
  | succ fuel ih =>
    intro l hnd hbal hlen
    cases hf : (l.zip (l.rotate 1)).find? (fun q => decide (q.1 ∈ B ∧ q.2 ∉ B)) with
    | none =>
      have hg : greedyPairs B (fuel + 1) l = [] := by simp only [greedyPairs, hf]
      rw [hg]
      refine ⟨by simp, by simp, by simp, ?_⟩
      intro j hj hjB
      exfalso
      have hex : ∃ y ∈ l, ¬ (y ∈ B) := by
        by_contra hcon
        push_neg at hcon
        have hfe : l.filter (fun v => decide (v ∈ B)) = l :=
          List.filter_eq_self.mpr (fun v hv => by simpa using hcon v hv)
        rw [hfe] at hbal
        have h0 : l.length = 0 := by omega
        rw [List.length_eq_zero_iff] at h0
        subst h0
        simp at hj
      obtain ⟨q, hq, h1, h2⟩ := solM_adj (fun v => v ∈ B) l ⟨j, hj, hjB⟩ hex
      rw [List.find?_eq_none] at hf
      exact hf q hq (by simp [h1, h2])
    | some q =>
      obtain ⟨a, b⟩ := q
      have hg : greedyPairs B (fuel + 1) l =
          (a, b) :: greedyPairs B fuel (l.filter fun v => v != a && v != b) := by
        simp only [greedyPairs, hf]
      have hP := List.find?_some hf
      simp only [decide_eq_true_eq] at hP
      obtain ⟨haB, hbB⟩ := hP
      have hmem := List.of_mem_zip (List.mem_of_find?_eq_some hf)
      have ha : a ∈ l := hmem.1
      have hb : b ∈ l := List.mem_rotate.mp hmem.2
      have hab : a ≠ b := fun h => hbB (h ▸ haB)
      set l' := l.filter fun v => v != a && v != b with hl'
      have hmem' : ∀ v, v ∈ l' ↔ v ∈ l ∧ v ≠ a ∧ v ≠ b := by
        intro v
        simp [hl', List.mem_filter]
      have hnd' : l'.Nodup := hnd.filter _
      -- lengths
      have hsplit : l' = (l.filter fun v => v != a).filter fun v => v != b := by
        rw [List.filter_filter, hl']
        apply List.filter_congr
        intro v _
        rw [Bool.and_comm]
      have hlenA := solM_len_remove a l hnd ha
      have hb2 : b ∈ l.filter (fun v => v != a) := by
        rw [List.mem_filter]
        exact ⟨hb, by simpa using hab.symm⟩
      have hlenB := solM_len_remove b (l.filter fun v => v != a) (hnd.filter _) hb2
      have hlen' : l'.length + 2 = l.length := by rw [hsplit]; omega
      have hBsplit : l'.filter (fun v => decide (v ∈ B)) =
          (l.filter (fun v => decide (v ∈ B))).filter (fun v => v != a) := by
        rw [hl', List.filter_filter, List.filter_filter]
        apply List.filter_congr
        intro v _
        rw [Bool.eq_iff_iff]
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨h1, h2, -⟩
          exact ⟨h2, h1⟩
        · rintro ⟨h2, h1⟩
          exact ⟨h1, h2, fun h => hbB (h ▸ h1)⟩
      have haB' : a ∈ l.filter (fun v => decide (v ∈ B)) := by
        rw [List.mem_filter]
        exact ⟨ha, by simpa using haB⟩
      have hlenC := solM_len_remove a (l.filter fun v => decide (v ∈ B)) (hnd.filter _) haB'
      have hbal' : 2 * (l'.filter (fun v => decide (v ∈ B))).length = l'.length := by
        rw [hBsplit]
        omega
      obtain ⟨hA, hN1, hN2, hC⟩ := ih l' hnd' hbal' (by omega)
      rw [hg]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨ha, haB, hb, hbB⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hA p hp
          exact ⟨((hmem' _).mp h1).1, h2, ((hmem' _).mp h3).1, h4⟩
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, hN1⟩
        intro hin
        obtain ⟨p, hp, hpa⟩ := List.mem_map.mp hin
        exact ((hmem' _).mp (hA p hp).1).2.1 hpa
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, hN2⟩
        intro hin
        obtain ⟨p, hp, hpb⟩ := List.mem_map.mp hin
        exact ((hmem' _).mp (hA p hp).2.2.1).2.2 hpb
      · intro j hj hjB
        rw [List.map_cons, List.mem_cons]
        by_cases hja : j = a
        · exact Or.inl hja
        · right
          have hjb : j ≠ b := fun h => hbB (h ▸ hjB)
          exact hC j ((hmem' j).mpr ⟨hj, hja, hjb⟩) hjB

theorem solM_lookup {n : ℕ} : ∀ (ps : List (Fin n × Fin n)) (j k : Fin n), (j, k) ∈ ps →
    (ps.map Prod.fst).Nodup → ps.lookup j = some k := by
  intro ps
  induction ps with
  | nil => intro j k h; simp at h
  | cons p ps ih =>
    intro j k h hnd
    obtain ⟨a, b⟩ := p
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h with h0 | h1
    · cases h0
      simp
    · have hja : j ≠ a := by
        rintro rfl
        exact hnd.1 (List.mem_map.mpr ⟨(j, k), h1, rfl⟩)
      have hbeq : (j == a) = false := by simpa using hja
      rw [List.lookup_cons, hbeq]
      exact ih j k h1 hnd.2

theorem solution (n : ℕ) (hn : Even n) (B : Finset (Fin n))
    (hB : B.card = n / 2) :
    Set.BijOn (sigma B) (B : Set (Fin n)) ((B : Set (Fin n))ᶜ) := by
  classical
  have hndf : ((List.finRange n).filter (fun v => decide (v ∈ B))).Nodup :=
    (List.nodup_finRange n).filter _
  have hcnt : ((List.finRange n).filter (fun v => decide (v ∈ B))).length = B.card := by
    rw [← List.toFinset_card_of_nodup hndf]
    congr 1
    ext v
    simp
  obtain ⟨r, hr⟩ := hn
  have hbal : 2 * ((List.finRange n).filter (fun v => decide (v ∈ B))).length =
      (List.finRange n).length := by
    rw [hcnt, List.length_finRange, hB]
    omega
  obtain ⟨hA, hN1, -, hC⟩ :=
    solM_greedy B n (List.finRange n) (List.nodup_finRange n) hbal
      (by rw [List.length_finRange]; omega)
  have hN2 := (solM_greedy B n (List.finRange n) (List.nodup_finRange n) hbal
      (by rw [List.length_finRange]; omega)).2.2.1
  have hsig : ∀ j ∈ B, ∃ p ∈ greedyPairs B n (List.finRange n),
      p.1 = j ∧ sigma B j = p.2 := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (hC j (List.mem_finRange j) hj)
    refine ⟨p, hp, rfl, ?_⟩
    unfold sigma matchPairs
    rw [solM_lookup _ p.1 p.2 (by simpa using hp) hN1]
    rfl
  have hmaps : Set.MapsTo (sigma B) (B : Set (Fin n)) ((B : Set (Fin n))ᶜ) := by
    intro j hj
    obtain ⟨p, hp, -, h2⟩ := hsig j hj
    rw [Set.mem_compl_iff, Finset.mem_coe, h2]
    exact (hA p hp).2.2.2
  have hinj : Set.InjOn (sigma B) (B : Set (Fin n)) := by
    intro j1 hj1 j2 hj2 heq
    obtain ⟨p1, hp1, h11, h12⟩ := hsig j1 hj1
    obtain ⟨p2, hp2, h21, h22⟩ := hsig j2 hj2
    have hp : p1 = p2 := List.inj_on_of_nodup_map hN2 hp1 hp2 (by rw [← h12, ← h22]; exact heq)
    rw [← h11, ← h21, hp]
  refine ⟨hmaps, hinj, ?_⟩
  intro b hb
  have hb' : b ∉ B := hb
  have himg : B.image (sigma B) = Bᶜ := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      have := hmaps (Finset.mem_coe.mpr hj)
      exact Finset.mem_compl.mpr this
    · rw [Finset.card_image_of_injOn hinj, Finset.card_compl, Fintype.card_fin, hB]
      omega
  have hbi : b ∈ B.image (sigma B) := by
    rw [himg]
    exact Finset.mem_compl.mpr hb'
  obtain ⟨j, hj, hjb⟩ := Finset.mem_image.mp hbi
  exact ⟨j, Finset.mem_coe.mpr hj, hjb⟩
