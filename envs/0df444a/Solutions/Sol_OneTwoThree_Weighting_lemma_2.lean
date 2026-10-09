-- Prove2me | solution 1 for OneTwoThree.Weighting.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @yammering
-- created : 2026-10-09T02:26:39.761699+00:00
-- url     : https://prove2.me/submissions/3ac22ca9-133f-4b74-a019-60cd705547a5

import Mathlib

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Shortest-walk toolkit -/

/-- Vertices of a shortest walk are pairwise distinct: splicing `take i` with `drop j`
would otherwise give a strictly shorter `v`–`w` walk. -/
lemma lemma2_getVert_inj (G : SimpleGraph V) {v w : V} (p : G.Walk v w)
    (hp : p.length = G.dist v w) {i j : ℕ} (hi : i ≤ p.length)
    (hj : j ≤ p.length) (hij : i < j) : p.getVert i ≠ p.getVert j := by
  intro heq
  have htake : (p.take i).length = i := by
    rw [Walk.take_length]
    omega
  have hdrop : (p.drop j).length = p.length - j := Walk.drop_length _ _
  have hle := G.dist_le ((p.take i).append ((p.drop j).copy heq.symm rfl))
  rw [Walk.length_append, htake, Walk.length_copy, hdrop] at hle
  omega

/-- A shortest walk has no chords: an edge skipping ahead would give a strictly
shorter `v`–`w` walk. -/
lemma lemma2_nochord (G : SimpleGraph V) {v w : V} (p : G.Walk v w)
    (hp : p.length = G.dist v w) {i j : ℕ} (hi : i ≤ p.length)
    (hj : j ≤ p.length) (hij : i + 1 < j) :
    ¬ G.Adj (p.getVert i) (p.getVert j) := by
  intro hadj
  have htake : (p.take i).length = i := by
    rw [Walk.take_length]
    omega
  have hdrop : (p.drop j).length = p.length - j := Walk.drop_length _ _
  have hle := G.dist_le ((p.take i).append (hadj.toWalk.append (p.drop j)))
  rw [Walk.length_append, Walk.length_append, htake, hadj.length_toWalk, hdrop] at hle
  omega

/-! ## The parity predicate and the initial set `R₀` -/

/-- Parity flips between consecutive indices. -/
lemma lemma2_parity_flip (b : Bool) (k : ℕ) :
    (decide (k % 2 = 0) = b) ↔ ¬ (decide ((k + 1) % 2 = 0) = b) := by
  have h : ((k + 1) % 2 = 0) ↔ ¬ (k % 2 = 0) := by omega
  have hdec : decide ((k + 1) % 2 = 0) = !(decide (k % 2 = 0)) := by
    by_cases hk : k % 2 = 0
    · have hnk : ¬ ((k + 1) % 2 = 0) := fun hh => h.mp hh hk
      simp [hk, hnk]
    · have hpk : (k + 1) % 2 = 0 := h.mpr hk
      simp [hk, hpk]
  rw [hdec]
  cases b <;> cases decide (k % 2 = 0) <;> simp

/-- `R₀`: every second vertex of the shortest path, starting with `v` iff `b`. -/
def lemma2_R0 (G : SimpleGraph V) {v w : V} (p : G.Walk v w) (b : Bool) :
    Finset V :=
  ((Finset.range (p.length + 1)).filter (fun i => decide (i % 2 = 0) = b)).image
    p.getVert

/-- Membership in `R₀` is exactly the parity condition. -/
lemma lemma2_mem_R0 (G : SimpleGraph V) {v w : V} (p : G.Walk v w)
    (hp : p.length = G.dist v w) (b : Bool) {k : ℕ} (hk : k ≤ p.length) :
    p.getVert k ∈ lemma2_R0 G p b ↔ decide (k % 2 = 0) = b := by
  constructor
  · intro h
    simp only [lemma2_R0, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range] at h
    obtain ⟨i, ⟨hi, hQi⟩, hgi⟩ := h
    have hi' : i ≤ p.length := by omega
    have hik : i = k := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact lemma2_getVert_inj G p hp hi' hk hlt hgi
      · exact lemma2_getVert_inj G p hp hk hi' hgt hgi.symm
    subst hik
    exact hQi
  · intro hQ
    simp only [lemma2_R0, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨k, ⟨by omega, hQ⟩, rfl⟩

/-- The vertices of the path. -/
def lemma2_pathVerts (G : SimpleGraph V) {v w : V} (p : G.Walk v w) : Finset V :=
  (Finset.range (p.length + 1)).image p.getVert

lemma lemma2_mem_pathVerts (G : SimpleGraph V) {v w : V} (p : G.Walk v w)
    {k : ℕ} (hk : k ≤ p.length) : p.getVert k ∈ lemma2_pathVerts G p := by
  simp only [lemma2_pathVerts, Finset.mem_image, Finset.mem_range]
  exact ⟨k, by omega, rfl⟩

lemma lemma2_R0_subset_pathVerts (G : SimpleGraph V) {v w : V} (p : G.Walk v w)
    (b : Bool) : lemma2_R0 G p b ⊆ lemma2_pathVerts G p := by
  rw [lemma2_R0, lemma2_pathVerts]
  exact Finset.image_subset_image (Finset.filter_subset _ _)

/-- `R₀` is independent: same-parity path vertices are non-adjacent since the
walk is shortest (hence chordless). -/
lemma lemma2_R0_indep (G : SimpleGraph V) {v w : V} (p : G.Walk v w)
    (hp : p.length = G.dist v w) (b : Bool) :
    G.IsIndepSet (↑(lemma2_R0 G p b) : Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hne
  simp only [Finset.mem_coe, lemma2_R0, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range] at hx hy
  obtain ⟨i, ⟨hi, hQi⟩, rfl⟩ := hx
  obtain ⟨j, ⟨hj, hQj⟩, rfl⟩ := hy
  have hi' : i ≤ p.length := by omega
  have hj' : j ≤ p.length := by omega
  have hij : i ≠ j := fun h => hne (by rw [h])
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · by_cases hconsec : j = i + 1
    · subst hconsec
      have hcon := (lemma2_parity_flip b i).mp hQi
      exact absurd hQj hcon
    · have h2 : i + 1 < j := by omega
      exact lemma2_nochord G p hp hi' hj' h2
  · by_cases hconsec : i = j + 1
    · subst hconsec
      have hcon := (lemma2_parity_flip b j).mp hQj
      exact absurd hQi hcon
    · have h2 : j + 1 < i := by omega
      exact fun h => lemma2_nochord G p hp hj' hi' h2 h.symm

/-! ## Connectivity within a processed set -/

/-- `ConnIn H S`: any two vertices of `S` are joined by a walk of `H` whose
support stays inside `S`. -/
def lemma2_ConnIn (H : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∃ w : H.Walk x y, ∀ z ∈ w.support, z ∈ S

/-- Consecutive path vertices are adjacent in the `R₀`-between graph. -/
lemma lemma2_base_step (G : SimpleGraph V) {v w : V} (p : G.Walk v w)
    (hp : p.length = G.dist v w) (b : Bool) {k : ℕ} (hk : k < p.length) :
    (G.between (↑(lemma2_R0 G p b) : Set V)
      (↑(lemma2_R0 G p b) : Set V)ᶜ).Adj (p.getVert k) (p.getVert (k + 1)) := by
  rw [SimpleGraph.between_adj]
  refine ⟨p.adj_getVert_succ hk, ?_⟩
  have hk' : k ≤ p.length := le_of_lt hk
  have e1 : p.getVert k ∈ lemma2_R0 G p b ↔ decide (k % 2 = 0) = b :=
    lemma2_mem_R0 G p hp b hk'
  have e2 : p.getVert (k + 1) ∈ lemma2_R0 G p b ↔
      decide ((k + 1) % 2 = 0) = b :=
    lemma2_mem_R0 G p hp b hk
  have hpar := lemma2_parity_flip b k
  rw [← e1, ← e2] at hpar
  simp only [Finset.mem_coe, Set.mem_compl_iff]
  tauto

/-- Every path vertex is reachable from `getVert 0` inside the path vertices. -/
lemma lemma2_base_reach0 (G : SimpleGraph V) {v w : V} (p : G.Walk v w)
    (hp : p.length = G.dist v w) (b : Bool) {k : ℕ} (hk : k ≤ p.length) :
    ∃ w : (G.between (↑(lemma2_R0 G p b) : Set V)
      (↑(lemma2_R0 G p b) : Set V)ᶜ).Walk (p.getVert 0) (p.getVert k),
      ∀ z ∈ w.support, z ∈ lemma2_pathVerts G p := by
  revert hk
  induction k with
  | zero =>
    intro _
    refine ⟨Walk.nil, ?_⟩
    intro z hz
    rw [Walk.mem_support_nil_iff] at hz
    subst hz
    exact lemma2_mem_pathVerts G p (Nat.zero_le _)
  | succ k ih =>
    intro hk
    have hk' : k < p.length := by omega
    have hk'' : k ≤ p.length := le_of_lt hk'
    obtain ⟨w, hw⟩ := ih hk''
    refine ⟨w.append (lemma2_base_step G p hp b hk').toWalk, ?_⟩
    intro z hz
    rw [Walk.support_append] at hz
    rcases List.mem_append.mp hz with h1 | h1
    · exact hw z h1
    · have h2 : z ∈ (lemma2_base_step G p hp b hk').toWalk.support :=
        List.mem_of_mem_tail h1
      rw [SimpleGraph.Adj.support_toWalk] at h2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with rfl | rfl
      · exact lemma2_mem_pathVerts G p hk''
      · exact lemma2_mem_pathVerts G p hk

/-- Base connectivity: path vertices are mutually reachable in the
`R₀`-between graph, staying inside the path vertices. -/
lemma lemma2_base_conn (G : SimpleGraph V) {v w : V} (p : G.Walk v w)
    (hp : p.length = G.dist v w) (b : Bool) : lemma2_ConnIn
    (G.between (↑(lemma2_R0 G p b) : Set V)
      (↑(lemma2_R0 G p b) : Set V)ᶜ)
    (lemma2_pathVerts G p) := by
  intro x hx y hy
  simp only [lemma2_pathVerts, Finset.mem_image, Finset.mem_range] at hx hy
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨j, hj, rfl⟩ := hy
  have hi' : i ≤ p.length := by omega
  have hj' : j ≤ p.length := by omega
  obtain ⟨w1, hw1⟩ := lemma2_base_reach0 G p hp b hi'
  obtain ⟨w2, hw2⟩ := lemma2_base_reach0 G p hp b hj'
  refine ⟨w1.reverse.append w2, ?_⟩
  intro z hz
  rw [Walk.support_append] at hz
  rcases List.mem_append.mp hz with h1 | h1
  · rw [Walk.support_reverse, List.mem_reverse] at h1
    exact hw1 z h1
  · exact hw2 z (List.mem_of_mem_tail h1)

/-! ## The extension invariant -/

/-- The invariant for processed set `S` and red set `R`. -/
def lemma2_Inv (G : SimpleGraph V) {v w : V} (p : G.Walk v w) (b : Bool)
    (R S : Finset V) : Prop :=
  lemma2_R0 G p b ⊆ R ∧ (↑R : Set V) ⊆ ↑S ∧ G.IsIndepSet (↑R : Set V) ∧
    lemma2_ConnIn (G.between (↑R : Set V) (↑R : Set V)ᶜ) S ∧
      (∀ k ≤ p.length, (p.getVert k ∈ R ↔ p.getVert k ∈ lemma2_R0 G p b)) ∧
        lemma2_pathVerts G p ⊆ S

lemma lemma2_base_Inv (G : SimpleGraph V) {v w : V} (p : G.Walk v w)
    (hp : p.length = G.dist v w) (b : Bool) :
    lemma2_Inv G p b (lemma2_R0 G p b) (lemma2_pathVerts G p) := by
  refine ⟨Finset.Subset.rfl, ?_, lemma2_R0_indep G p hp b,
    lemma2_base_conn G p hp b, fun k _ => Iff.rfl, Finset.Subset.rfl⟩
  intro x hx
  have hx' : x ∈ lemma2_R0 G p b := Finset.mem_coe.mp hx
  exact Finset.mem_coe.mpr (lemma2_R0_subset_pathVerts G p b hx')

/-- Transfer a walk across graphs when all edges on its support persist. -/
lemma lemma2_walk_transfer (S : Finset V) {H H' : SimpleGraph V}
    (hle : ∀ a ∈ S, ∀ b ∈ S, H.Adj a b → H'.Adj a b)
    {x y : V} (w : H.Walk x y) (hsup : ∀ z ∈ w.support, z ∈ S) :
    ∃ w' : H'.Walk x y, w'.support = w.support := by
  revert hsup
  induction w with
  | nil => intro hsup; exact ⟨Walk.nil, rfl⟩
  | cons h t ih =>
    intro hsup
    have hsup' : ∀ z ∈ t.support, z ∈ S := fun z hz =>
      hsup z (by simp [Walk.support_cons, hz])
    obtain ⟨t', ht'⟩ := ih hsup'
    have hu : _ ∈ S := hsup _ (Walk.start_mem_support (Walk.cons h t))
    have hv : _ ∈ S := hsup' _ t.start_mem_support
    exact ⟨Walk.cons (hle _ hu _ hv h) t', by simp [Walk.support_cons, ht']⟩

/-- Cons case of `lemma2_aux_adj`, with the middle vertex named explicitly. -/
lemma lemma2_aux_adj_step (G : SimpleGraph V) {S : Finset V} {x mid y : V}
    (h : G.Adj x mid) (t : G.Walk mid y) (hx : x ∈ S) (hy : y ∉ S)
    (ih : mid ∈ S → y ∉ S → ∃ z, z ∉ S ∧ ∃ u, u ∈ S ∧ G.Adj u z) :
    ∃ z, z ∉ S ∧ ∃ u, u ∈ S ∧ G.Adj u z := by
  by_cases hx' : mid ∈ S
  · exact ih hx' hy
  · exact ⟨_, hx', _, hx, h⟩

/-- From a walk leaving `S`, extract an edge crossing out of `S`. -/
lemma lemma2_aux_adj (G : SimpleGraph V) {S : Finset V} {x y : V}
    (q : G.Walk x y) (hx : x ∈ S) (hy : y ∉ S) :
    ∃ z, z ∉ S ∧ ∃ u, u ∈ S ∧ G.Adj u z := by
  revert hx hy
  induction q with
  | nil => intro hx hy; exact (hy hx).elim
  | cons h t ih =>
    intro hx hy
    exact lemma2_aux_adj_step G h t hx hy ih

/-! ## The extension step -/

/-- Extend the invariant from `S` to `insert z S`, where `z ∉ S` has a
neighbor `u ∈ S`: keep `R` if `z` already sees red, else add `z`.
This is the paper's induction step. -/
lemma lemma2_step (G : SimpleGraph V) {v w : V} (p : G.Walk v w) (b : Bool)
    (S R : Finset V) (hInv : lemma2_Inv G p b R S)
    {z : V} (hzS : z ∉ S) {u : V} (huS : u ∈ S) (hadj : G.Adj u z) :
    ∃ R1, lemma2_Inv G p b R1 (insert z S) ∧ R ⊆ R1 := by
  obtain ⟨hR0, hRS, hindep, hconn, hpath, hPS⟩ := hInv
  by_cases h : ∃ a ∈ R, G.Adj z a
  · -- `z` already has a red neighbor: keep `R`.
    refine ⟨R, ⟨hR0, ?_, hindep, ?_, hpath, ?_⟩, Finset.Subset.rfl⟩
    · intro x hx
      exact Finset.mem_coe.mpr
        (Finset.mem_insert_of_mem (Finset.mem_coe.mp (hRS hx)))
    · intro x hx y hy
      rw [Finset.mem_insert] at hx hy
      have hzR : z ∉ R :=
        fun hh => hzS (Finset.mem_coe.mp (hRS (Finset.mem_coe.mpr hh)))
      obtain ⟨a, haR, hadjza⟩ := h
      have haS : a ∈ S := Finset.mem_coe.mp (hRS (Finset.mem_coe.mpr haR))
      have hadj' : (G.between (↑R : Set V) (↑R : Set V)ᶜ).Adj a z := by
        rw [SimpleGraph.between_adj]
        refine ⟨hadjza.symm, Or.inl ⟨Finset.mem_coe.mpr haR, ?_⟩⟩
        rw [Set.mem_compl_iff]
        exact Finset.mem_coe.not.mpr hzR
      rcases hx with heqx | hx <;> rcases hy with heqy | hy
      · rw [heqx, heqy]
        refine ⟨Walk.nil, ?_⟩
        intro q hq
        rw [Walk.mem_support_nil_iff] at hq
        rw [hq]
        exact Finset.mem_insert_self z S
      · rw [heqx]
        obtain ⟨wxy, hwxy⟩ := hconn a haS y hy
        refine ⟨hadj'.toWalk.reverse.append wxy, ?_⟩
        intro q hq
        rw [Walk.support_append] at hq
        rcases List.mem_append.mp hq with h1 | h1
        · rw [Walk.support_reverse, List.mem_reverse,
            SimpleGraph.Adj.support_toWalk] at h1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
          rcases h1 with heq | heq <;> rw [heq]
          · exact Finset.mem_insert_of_mem haS
          · exact Finset.mem_insert_self z S
        · exact Finset.mem_insert_of_mem (hwxy q (List.mem_of_mem_tail h1))
      · rw [heqy]
        obtain ⟨wxy, hwxy⟩ := hconn x hx a haS
        refine ⟨wxy.append hadj'.toWalk, ?_⟩
        intro q hq
        rw [Walk.support_append] at hq
        rcases List.mem_append.mp hq with h1 | h1
        · exact Finset.mem_insert_of_mem (hwxy q h1)
        · have h2 : q ∈ hadj'.toWalk.support := List.mem_of_mem_tail h1
          rw [SimpleGraph.Adj.support_toWalk] at h2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
          rcases h2 with heq | heq <;> rw [heq]
          · exact Finset.mem_insert_of_mem haS
          · exact Finset.mem_insert_self z S
      · obtain ⟨wxy, hwxy⟩ := hconn x hx y hy
        exact ⟨wxy, fun q hq => Finset.mem_insert_of_mem (hwxy q hq)⟩
    · exact hPS.trans (Finset.subset_insert z S)
  · -- `z` has no red neighbor: add it.
    have hindep_pair := (SimpleGraph.isIndepSet_iff G).mp hindep
    refine ⟨insert z R, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Finset.subset_insert z R⟩
    · exact hR0.trans (Finset.subset_insert z R)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (Finset.mem_coe.mp (hRS (Finset.mem_coe.mpr hx)))
    · rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hne
      simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact (hne rfl).elim
      · intro hadjzb
        exact h ⟨b, hb, hadjzb⟩
      · intro hadjbz
        exact h ⟨a, ha, hadjbz.symm⟩
      · exact hindep_pair (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb)
          hne
    · have hnez : ∀ t ∈ S, t ≠ z := fun t ht heq => hzS (heq ▸ ht)
      have hside : ∀ t ∈ S, (t ∈ insert z R ↔ t ∈ R) := by
        intro t ht
        constructor
        · intro hh
          rcases Finset.mem_insert.mp hh with heq | hh
          · exact absurd heq (hnez t ht)
          · exact hh
        · exact Finset.mem_insert_of_mem
      have hle : ∀ a ∈ S, ∀ b ∈ S,
          (G.between (↑R : Set V) (↑R : Set V)ᶜ).Adj a b →
          (G.between (↑(insert z R) : Set V)
            (↑(insert z R) : Set V)ᶜ).Adj a b := by
        intro a ha b hb hadj
        rw [SimpleGraph.between_adj] at hadj ⊢
        obtain ⟨hg, hs⟩ := hadj
        refine ⟨hg, ?_⟩
        simp only [Finset.mem_coe, Set.mem_compl_iff] at hs ⊢
        rcases hs with ⟨haR, hbR⟩ | ⟨haR, hbR⟩
        · exact Or.inl ⟨Finset.mem_insert_of_mem haR,
            fun hh => hbR ((hside b hb).mp hh)⟩
        · exact Or.inr ⟨fun hh => haR ((hside a ha).mp hh),
            Finset.mem_insert_of_mem hbR⟩
      have huR1 : u ∈ (↑(insert z R) : Set V)ᶜ := by
        rw [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_insert]
        intro hh
        rcases hh with rfl | hh
        · exact hzS huS
        · exact h ⟨u, hh, hadj.symm⟩
      have hadj' : (G.between (↑(insert z R) : Set V)
          (↑(insert z R) : Set V)ᶜ).Adj z u := by
        rw [SimpleGraph.between_adj]
        exact ⟨hadj.symm, Or.inl ⟨Finset.mem_coe.mpr
          (Finset.mem_insert_self z R), huR1⟩⟩
      intro x hx y hy
      rw [Finset.mem_insert] at hx hy
      rcases hx with heqx | hx <;> rcases hy with heqy | hy
      · rw [heqx, heqy]
        refine ⟨Walk.nil, ?_⟩
        intro q hq
        rw [Walk.mem_support_nil_iff] at hq
        rw [hq]
        exact Finset.mem_insert_self z S
      · rw [heqx]
        obtain ⟨wold, hwold⟩ := hconn u huS y hy
        obtain ⟨wnew, hsup⟩ := lemma2_walk_transfer S hle wold hwold
        refine ⟨hadj'.toWalk.append wnew, ?_⟩
        intro q hq
        rw [Walk.support_append] at hq
        rcases List.mem_append.mp hq with h1 | h1
        · rw [SimpleGraph.Adj.support_toWalk] at h1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
          rcases h1 with heq | heq <;> rw [heq]
          · exact Finset.mem_insert_self z S
          · exact Finset.mem_insert_of_mem huS
        · rw [hsup] at h1
          exact Finset.mem_insert_of_mem (hwold q (List.mem_of_mem_tail h1))
      · rw [heqy]
        obtain ⟨wold, hwold⟩ := hconn x hx u huS
        obtain ⟨wnew, hsup⟩ := lemma2_walk_transfer S hle wold hwold
        refine ⟨wnew.append hadj'.toWalk.reverse, ?_⟩
        intro q hq
        rw [Walk.support_append] at hq
        rcases List.mem_append.mp hq with h1 | h1
        · rw [hsup] at h1
          exact Finset.mem_insert_of_mem (hwold q h1)
        · have h2 : q ∈ hadj'.toWalk.reverse.support :=
            List.mem_of_mem_tail h1
          rw [Walk.support_reverse, List.mem_reverse,
            SimpleGraph.Adj.support_toWalk] at h2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
          rcases h2 with heq | heq <;> rw [heq]
          · exact Finset.mem_insert_self z S
          · exact Finset.mem_insert_of_mem huS
      · obtain ⟨wold, hwold⟩ := hconn x hx y hy
        obtain ⟨wnew, hsup⟩ := lemma2_walk_transfer S hle wold hwold
        exact ⟨wnew, fun q hq => Finset.mem_insert_of_mem (hwold q (hsup ▸ hq))⟩
    · intro k hk
      have hmem : p.getVert k ∈ S := hPS (lemma2_mem_pathVerts G p hk)
      have hne : p.getVert k ≠ z := fun heq => hzS (heq ▸ hmem)
      rw [Finset.mem_insert]
      constructor
      · intro hh
        rcases hh with hcon | hh
        · exact absurd hcon hne
        · exact (hpath k hk).mp hh
      · intro hh
        exact Or.inr ((hpath k hk).mpr hh)
    · exact hPS.trans (Finset.subset_insert z S)

/-! ## Fuel induction to cover all vertices -/

/-- Extend the invariant all the way to `univ`, adding one adjacent vertex
at a time (possible by connectedness). -/
lemma lemma2_extend_aux (G : SimpleGraph V) {v w : V} (p : G.Walk v w)
    (hp : p.length = G.dist v w) (b : Bool) (hG : G.Connected) :
    ∀ (fuel : ℕ) (S R : Finset V), lemma2_Inv G p b R S →
      (Finset.univ \ S).card ≤ fuel →
      ∃ R1, lemma2_Inv G p b R1 Finset.univ ∧ R ⊆ R1
  | 0, S, R, hInv, hcard => by
    have hcard0 : (Finset.univ \ S).card = 0 := by omega
    have hempty : Finset.univ \ S = ∅ := Finset.card_eq_zero.mp hcard0
    have hSeq : S = Finset.univ := by
      ext x
      simp only [Finset.mem_univ, iff_true]
      by_contra hxS
      have hmem : x ∈ Finset.univ \ S :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxS⟩
      rw [hempty] at hmem
      exact Finset.notMem_empty x hmem
    subst hSeq
    exact ⟨R, hInv, Finset.Subset.rfl⟩
  | fuel + 1, S, R, hInv, hcard => by
    by_cases hS : S = Finset.univ
    · subst hS
      exact ⟨R, hInv, Finset.Subset.rfl⟩
    · have hPS : lemma2_pathVerts G p ⊆ S := hInv.2.2.2.2.2
      have hex : ∃ y, y ∉ S := by
        by_contra hcon
        apply hS
        ext y
        simp only [Finset.mem_univ, iff_true]
        by_contra hyS
        exact hcon ⟨y, hyS⟩
      obtain ⟨y, hyS⟩ := hex
      have hv0 : p.getVert 0 ∈ lemma2_pathVerts G p :=
        lemma2_mem_pathVerts G p (Nat.zero_le _)
      rw [p.getVert_zero] at hv0
      have hvS : v ∈ S := hPS hv0
      obtain ⟨q⟩ := hG v y
      obtain ⟨z, hzS, u, huS, hadj⟩ := lemma2_aux_adj G q hvS hyS
      obtain ⟨R1, hInv1, hsub1⟩ := lemma2_step G p b S R hInv hzS huS hadj
      have hlt : (Finset.univ \ insert z S).card < (Finset.univ \ S).card := by
        have hmem : z ∈ Finset.univ \ S :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzS⟩
        have hsub : Finset.univ \ insert z S ⊂ Finset.univ \ S := by
          rw [Finset.ssubset_iff_subset_ne]
          constructor
          · intro x hx
            rw [Finset.mem_sdiff] at hx ⊢
            exact ⟨hx.1, fun hh => hx.2 (Finset.mem_insert_of_mem hh)⟩
          · intro heq
            rw [← heq] at hmem
            rw [Finset.mem_sdiff, Finset.mem_insert] at hmem
            exact hmem.2 (Or.inl rfl)
        exact Finset.card_lt_card hsub
      have hcard' : (Finset.univ \ insert z S).card ≤ fuel := by omega
      obtain ⟨R2, hInv2, hsub2⟩ :=
        lemma2_extend_aux G p hp b hG fuel (insert z S) R1 hInv1 hcard'
      exact ⟨R2, hInv2, hsub1.trans hsub2⟩

/-! ## Main theorem -/

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) {v w : V} (p : G.Walk v w)
    (hp : p.length = G.dist v w) (b : Bool) :
    ∃ R : Finset V, G.IsIndepSet (R : Set V) ∧
      (G.between (R : Set V) (R : Set V)ᶜ).Connected ∧
      (∀ i < p.length, (p.getVert i ∈ R ↔ p.getVert (i + 1) ∉ R)) ∧
      (v ∈ R ↔ b = true) := by
  obtain ⟨R, hInv, -⟩ := lemma2_extend_aux G p hp b hG
    (Finset.univ \ lemma2_pathVerts G p).card (lemma2_pathVerts G p)
    (lemma2_R0 G p b) (lemma2_base_Inv G p hp b) le_rfl
  obtain ⟨hR0, hRS, hindep, hconn, hpath, hPS⟩ := hInv
  refine ⟨R, hindep, ?_, ?_, ?_⟩
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨v, fun y => ?_⟩
    obtain ⟨ww, -⟩ := hconn v (Finset.mem_univ v) y (Finset.mem_univ y)
    exact ⟨ww⟩
  · intro i hi
    have hi' : i ≤ p.length := le_of_lt hi
    rw [(hpath i hi'), (hpath (i + 1) hi)]
    rw [lemma2_mem_R0 G p hp b hi', lemma2_mem_R0 G p hp b hi]
    exact lemma2_parity_flip b i
  · have h0 : (0 : ℕ) ≤ p.length := Nat.zero_le _
    have e := hpath 0 h0
    rw [p.getVert_zero] at e
    rw [e]
    have m0 := lemma2_mem_R0 G p hp b h0
    rw [p.getVert_zero] at m0
    rw [m0]
    have h00 : decide ((0 : ℕ) % 2 = 0) = true := by decide
    rw [h00]
    cases b <;> simp
