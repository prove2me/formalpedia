-- Prove2me | solution 1 for StrongPerfectGraph.LineGraph.rung_parity
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T12:21:28.621984+00:00
-- url     : https://prove2.me/submissions/cf8c0592-d19e-4acb-b251-edec5691683a

/-
Chudnovsky–Robertson–Seymour–Thomas, 8.1: in a Berge graph, for a `J`-strip system with `J`
3-connected, all `uv`-rungs have lengths of the same parity.

Proof (as in the paper). Since `J` is 3-connected, the edge `uv` lies on a cycle of `J` with at
least four vertices. Fix one (special) rung for every other edge of that cycle. For any `uv`-rung
`R`, the union of `R` and the fixed rungs induces a cycle of `G` with at least four vertices,
which is a hole and hence even. So the length of `R` has the parity forced by the fixed rungs.
-/
import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_IsInducedPath
import Definitions.Def_StrongPerfectGraph_LineGraph_IsStripSystem
import Definitions.Def_StrongPerfectGraph_LineGraph_IsSubdivision

set_option autoImplicit false

namespace SPGTLib

open StrongPerfectGraph.Main

section Toolkit
variable {V : Type*}

theorem isInducedPath_iff {G : SimpleGraph V} {p : List V} :
    IsInducedPath G p ↔ p ≠ [] ∧ p.Nodup ∧ ∀ (i j : ℕ) (hi : i < p.length) (hj : j < p.length),
      G.Adj p[i] p[j] ↔ (i + 1 = j ∨ j + 1 = i) := by
  unfold IsInducedPath
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun i j hi hj => by simpa using h3 ⟨i, hi⟩ ⟨j, hj⟩⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun i j => by simpa using h3 i.1 j.1 i.2 j.2⟩

theorem isHole_iff {G : SimpleGraph V} {L : List V} :
    IsHole G L ↔ 4 ≤ L.length ∧ L.Nodup ∧ ∀ (i j : ℕ) (hi : i < L.length) (hj : j < L.length),
      G.Adj L[i] L[j] ↔ ((i + 1) % L.length = j ∨ (j + 1) % L.length = i) := by
  unfold IsHole
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun i j hi hj => by simpa using h3 ⟨i, hi⟩ ⟨j, hj⟩⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun i j => by simpa using h3 i.1 j.1 i.2 j.2⟩

theorem succ_mod_eq {n x : ℕ} (hx : x < n) :
    (x + 1) % n = if x + 1 = n then 0 else x + 1 := by
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

theorem getElem_head {P : List V} {p0 : V} (h : P.head? = some p0) (hl : 0 < P.length) :
    P[0] = p0 := by
  cases P with
  | nil => simp at hl
  | cons a t => simpa using h

theorem getElem_last {P : List V} {p1 : V} (h : P.getLast? = some p1) (hl : 0 < P.length) :
    P[P.length - 1] = p1 := by
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
  exact Option.some.inj h

theorem isInducedPath_reverse {G : SimpleGraph V} {p : List V} (h : IsInducedPath G p) :
    IsInducedPath G p.reverse := by
  rw [isInducedPath_iff] at h ⊢
  obtain ⟨hne, hnd, hadj⟩ := h
  refine ⟨by simpa using hne, by simpa using hnd, ?_⟩
  intro i j hi hj
  have hi2 : i < p.length := by simpa using hi
  have hj2 : j < p.length := by simpa using hj
  have hi' : p.length - 1 - i < p.length := by omega
  have hj' : p.length - 1 - j < p.length := by omega
  rw [List.getElem_reverse, List.getElem_reverse, hadj _ _ hi' hj']
  omega

/-- Two induced paths, joined by the two end edges only, form a hole. -/
theorem isHole_append (G : SimpleGraph V) (P Q : List V) (p0 p1 q0 q1 : V)
    (hP : IsInducedPath G P) (hQ : IsInducedPath G Q)
    (hPl : 1 ≤ P.length) (hQl : 1 ≤ Q.length) (h4 : 4 ≤ P.length + Q.length)
    (hP0 : P.head? = some p0) (hP1 : P.getLast? = some p1)
    (hQ0 : Q.head? = some q0) (hQ1 : Q.getLast? = some q1)
    (hdisj : ∀ v ∈ P, v ∉ Q)
    (hcross : ∀ u ∈ P, ∀ v ∈ Q, G.Adj u v ↔ (u = p0 ∧ v = q1) ∨ (u = p1 ∧ v = q0)) :
    IsHole G (P ++ Q) := by
  rw [isHole_iff]
  rw [isInducedPath_iff] at hP hQ
  obtain ⟨_, hPnd, hPadj⟩ := hP
  obtain ⟨_, hQnd, hQadj⟩ := hQ
  have hp0 : P[0]'(by omega) = p0 := getElem_head hP0 (by omega)
  have hp1 : P[P.length - 1]'(by omega) = p1 := getElem_last hP1 (by omega)
  have hq0 : Q[0]'(by omega) = q0 := getElem_head hQ0 (by omega)
  have hq1 : Q[Q.length - 1]'(by omega) = q1 := getElem_last hQ1 (by omega)
  refine ⟨by simp; omega, ?_, ?_⟩
  · rw [List.nodup_append]
    exact ⟨hPnd, hQnd, fun a ha b hb hab => hdisj a ha (hab ▸ hb)⟩
  · intro i j hi hj
    simp only [List.length_append] at hi hj ⊢
    have hPi : ∀ (s : ℕ) (hs : s < P.length), (P[s] = p0 ↔ s = 0) := by
      intro s hs
      rw [← hp0]
      exact hPnd.getElem_inj_iff
    have hPj : ∀ (s : ℕ) (hs : s < P.length), (P[s] = p1 ↔ s = P.length - 1) := by
      intro s hs
      rw [← hp1]
      exact hPnd.getElem_inj_iff
    have hQi : ∀ (s : ℕ) (hs : s < Q.length), (Q[s] = q0 ↔ s = 0) := by
      intro s hs
      rw [← hq0]
      exact hQnd.getElem_inj_iff
    have hQj : ∀ (s : ℕ) (hs : s < Q.length), (Q[s] = q1 ↔ s = Q.length - 1) := by
      intro s hs
      rw [← hq1]
      exact hQnd.getElem_inj_iff
    by_cases hi' : i < P.length <;> by_cases hj' : j < P.length
    · rw [List.getElem_append_left hi', List.getElem_append_left hj', hPadj i j hi' hj',
        succ_mod_eq hi, succ_mod_eq hj]
      split_ifs <;> omega
    · have hj'' : j - P.length < Q.length := by omega
      rw [List.getElem_append_left hi', List.getElem_append_right (by omega : P.length ≤ j),
        hcross _ (List.getElem_mem hi') _ (List.getElem_mem hj''), hPi, hPj, hQi, hQj,
        succ_mod_eq hi, succ_mod_eq hj]
      split_ifs <;> omega
    · have hi'' : i - P.length < Q.length := by omega
      rw [List.getElem_append_right (by omega : P.length ≤ i), List.getElem_append_left hj',
        SimpleGraph.adj_comm,
        hcross _ (List.getElem_mem hj') _ (List.getElem_mem hi''), hPi, hPj, hQi, hQj,
        succ_mod_eq hi, succ_mod_eq hj]
      split_ifs <;> omega
    · have hi'' : i - P.length < Q.length := by omega
      have hj'' : j - P.length < Q.length := by omega
      rw [List.getElem_append_right (by omega : P.length ≤ i),
        List.getElem_append_right (by omega : P.length ≤ j),
        hQadj _ _ hi'' hj'', succ_mod_eq hi, succ_mod_eq hj]
      split_ifs <;> omega

/-- Two induced paths joined by exactly one edge, from the end of `P` to the start of `Q`,
concatenate to an induced path. -/
theorem isInducedPath_append (G : SimpleGraph V) (P Q : List V) (p1 q0 : V)
    (hP : IsInducedPath G P) (hQ : IsInducedPath G Q)
    (hP1 : P.getLast? = some p1) (hQ0 : Q.head? = some q0)
    (hdisj : ∀ v ∈ P, v ∉ Q)
    (hcross : ∀ u ∈ P, ∀ v ∈ Q, G.Adj u v ↔ (u = p1 ∧ v = q0)) :
    IsInducedPath G (P ++ Q) := by
  rw [isInducedPath_iff] at hP hQ ⊢
  obtain ⟨hPne, hPnd, hPadj⟩ := hP
  obtain ⟨hQne, hQnd, hQadj⟩ := hQ
  have hPpos : 0 < P.length := List.length_pos_iff.mpr hPne
  have hQpos : 0 < Q.length := List.length_pos_iff.mpr hQne
  have hp1 : P[P.length - 1]'(by omega) = p1 := getElem_last hP1 hPpos
  have hq0 : Q[0]'(by omega) = q0 := getElem_head hQ0 hQpos
  refine ⟨by simp [hPne], ?_, ?_⟩
  · rw [List.nodup_append]
    exact ⟨hPnd, hQnd, fun a ha b hb hab => hdisj a ha (hab ▸ hb)⟩
  · intro i j hi hj
    simp only [List.length_append] at hi hj
    have hPj : ∀ (s : ℕ) (hs : s < P.length), (P[s] = p1 ↔ s = P.length - 1) := by
      intro s hs
      rw [← hp1]
      exact hPnd.getElem_inj_iff
    have hQi : ∀ (s : ℕ) (hs : s < Q.length), (Q[s] = q0 ↔ s = 0) := by
      intro s hs
      rw [← hq0]
      exact hQnd.getElem_inj_iff
    by_cases hi' : i < P.length <;> by_cases hj' : j < P.length
    · rw [List.getElem_append_left hi', List.getElem_append_left hj', hPadj i j hi' hj']
    · have hj'' : j - P.length < Q.length := by omega
      rw [List.getElem_append_left hi', List.getElem_append_right (by omega : P.length ≤ j),
        hcross _ (List.getElem_mem hi') _ (List.getElem_mem hj''), hPj, hQi]
      omega
    · have hi'' : i - P.length < Q.length := by omega
      rw [List.getElem_append_right (by omega : P.length ≤ i), List.getElem_append_left hj',
        SimpleGraph.adj_comm,
        hcross _ (List.getElem_mem hj') _ (List.getElem_mem hi''), hPj, hQi]
      omega
    · have hi'' : i - P.length < Q.length := by omega
      have hj'' : j - P.length < Q.length := by omega
      rw [List.getElem_append_right (by omega : P.length ≤ i),
        List.getElem_append_right (by omega : P.length ≤ j), hQadj _ _ hi'' hj'']
      omega

end Toolkit

section Strips
variable {W V : Type*}

/-- Concatenation of the first `j` blocks `R0 (c 0) (c 1), …, R0 (c (j-1)) (c j)`. -/
def blocks (R0 : W → W → List V) (c : ℕ → W) : ℕ → List V
  | 0 => []
  | j + 1 => blocks R0 c j ++ R0 (c j) (c (j + 1))

@[simp] theorem blocks_zero (R0 : W → W → List V) (c : ℕ → W) : blocks R0 c 0 = [] := rfl

theorem blocks_succ (R0 : W → W → List V) (c : ℕ → W) (j : ℕ) :
    blocks R0 c (j + 1) = blocks R0 c j ++ R0 (c j) (c (j + 1)) := rfl

/-- The data of a closed chain of strips along a path `c 0, …, c k` of `J`. -/
structure Setup (J : SimpleGraph W) (G : SimpleGraph V) (S : W → W → Set V) (N : W → Set V)
    (R0 : W → W → List V) (c : ℕ → W) (k : ℕ) : Prop where
  symm : ∀ u v, J.Adj u v → S u v = S v u
  disj : ∀ u v w x, J.Adj u v → J.Adj w x → s(u, v) ≠ s(w, x) → Disjoint (S u v) (S w x)
  far : ∀ u v w x, J.Adj u v → J.Adj w x → u ≠ w → u ≠ x → v ≠ w → v ≠ x →
    ∀ a ∈ S u v, ∀ b ∈ S w x, ¬ G.Adj a b
  share : ∀ u v w, J.Adj u v → J.Adj u w → v ≠ w →
    ∀ a ∈ S u v, ∀ b ∈ S u w, (G.Adj a b ↔ a ∈ N u ∧ b ∈ N u)
  rung : ∀ x y, J.Adj x y → StrongPerfectGraph.LineGraph.IsRung G S N x y (R0 x y)
  inj : ∀ i j, i ≤ k → j ≤ k → c i = c j → i = j
  step : ∀ i, i < k → J.Adj (c i) (c (i + 1))

variable {J : SimpleGraph W} {G : SimpleGraph V} {S : W → W → Set V} {N : W → Set V}
  {R0 : W → W → List V} {c : ℕ → W} {k : ℕ}

namespace Setup

theorem block_ne_nil (h : Setup J G S N R0 c k) {i : ℕ} (hi : i < k) :
    R0 (c i) (c (i + 1)) ≠ [] := (h.rung _ _ (h.step i hi)).1.1

theorem block_mem (h : Setup J G S N R0 c k) {i : ℕ} (hi : i < k) {z : V}
    (hz : z ∈ R0 (c i) (c (i + 1))) : z ∈ S (c i) (c (i + 1)) :=
  (h.rung _ _ (h.step i hi)).2.1 z hz

theorem edge_ne (h : Setup J G S N R0 c k) {i j : ℕ} (hi : i ≤ k) (hi' : i + 1 ≤ k) (hj : j ≤ k)
    (hj' : j + 1 ≤ k) (hij : i ≠ j) : s(c i, c (i + 1)) ≠ s(c j, c (j + 1)) := by
  intro heq
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hij (h.inj _ _ hi hj h1)
  · have := h.inj _ _ hi hj' h1
    have := h.inj _ _ hi' hj h2
    omega

theorem block_disjoint (h : Setup J G S N R0 c k) {i j : ℕ} (hi : i < k) (hj : j < k) (hij : i ≠ j)
    {z : V} (hzi : z ∈ R0 (c i) (c (i + 1))) (hzj : z ∈ R0 (c j) (c (j + 1))) : False := by
  have hne := h.edge_ne (by omega) (by omega) (by omega) (by omega) hij
  exact Set.disjoint_left.mp (h.disj _ _ _ _ (h.step i hi) (h.step j hj) hne)
    (h.block_mem hi hzi) (h.block_mem hj hzj)

/-- Adjacency between two different blocks of the path. -/
theorem adj_blocks (h : Setup J G S N R0 c k) {i j : ℕ} (hi : i < k) (hj : j < k) (hij : i ≠ j)
    {z z' : V} (hz : z ∈ R0 (c i) (c (i + 1))) (hz' : z' ∈ R0 (c j) (c (j + 1))) :
    G.Adj z z' ↔
      (j = i + 1 ∧ z ∈ N (c j) ∧ z' ∈ N (c j)) ∨ (i = j + 1 ∧ z ∈ N (c i) ∧ z' ∈ N (c i)) := by
  have hzS := h.block_mem hi hz
  have hzS' := h.block_mem hj hz'
  by_cases hji : j = i + 1
  · subst hji
    have hadj : J.Adj (c (i + 1)) (c i) := (h.step i hi).symm
    have := h.share (c (i + 1)) (c i) (c (i + 1 + 1)) hadj (h.step _ hj)
      (fun heq => by have := h.inj _ _ (by omega) (by omega) heq; omega) z
      (by rw [h.symm _ _ (h.step i hi)] at hzS; exact hzS) z' hzS'
    rw [this]
    constructor
    · intro hh; exact Or.inl ⟨rfl, hh⟩
    · rintro (⟨_, hh⟩ | ⟨hh, _⟩)
      · exact hh
      · omega
  by_cases hij' : i = j + 1
  · subst hij'
    have hadj : J.Adj (c (j + 1)) (c j) := (h.step j hj).symm
    have := h.share (c (j + 1)) (c j) (c (j + 1 + 1)) hadj (h.step _ hi)
      (fun heq => by have := h.inj _ _ (by omega) (by omega) heq; omega) z'
      (by rw [h.symm _ _ (h.step j hj)] at hzS'; exact hzS') z hzS
    rw [SimpleGraph.adj_comm, this]
    constructor
    · intro hh; exact Or.inr ⟨rfl, hh.2, hh.1⟩
    · rintro (⟨hh, _⟩ | ⟨_, hh1, hh2⟩)
      · omega
      · exact ⟨hh2, hh1⟩
  · have hfar := h.far (c i) (c (i + 1)) (c j) (c (j + 1)) (h.step i hi) (h.step j hj)
      (fun heq => hij (h.inj _ _ (by omega) (by omega) heq))
      (fun heq => hij' (h.inj _ _ (by omega) (by omega) heq))
      (fun heq => hji (by have := h.inj _ _ (by omega) (by omega) heq; omega))
      (fun heq => hij (by have := h.inj _ _ (by omega) (by omega) heq; omega)) z hzS z' hzS'
    constructor
    · intro hh; exact absurd hh hfar
    · rintro (⟨hh, _⟩ | ⟨hh, _⟩)
      · exact absurd hh hji
      · exact absurd hh hij'


end Setup


namespace Setup

theorem blocks_spec (h : Setup J G S N R0 c k) :
    ∀ j, j + 1 ≤ k →
      IsInducedPath G (blocks R0 c (j + 1)) ∧
      (blocks R0 c (j + 1)).head? = (R0 (c 0) (c 1)).head? ∧
      (blocks R0 c (j + 1)).getLast? = (R0 (c j) (c (j + 1))).getLast? ∧
      ∀ z ∈ blocks R0 c (j + 1), ∃ i, i < j + 1 ∧ z ∈ R0 (c i) (c (i + 1)) := by
  intro j
  induction j with
  | zero =>
    intro hj
    have hrung := h.rung _ _ (h.step 0 (by omega))
    have hb : blocks R0 c (0 + 1) = R0 (c 0) (c (0 + 1)) := by simp [blocks_succ]
    rw [hb]
    exact ⟨hrung.1, rfl, rfl, fun z hz => ⟨0, by omega, hz⟩⟩
  | succ j ih =>
    intro hj
    obtain ⟨hpath, hhead, hlast, hmem⟩ := ih (by omega)
    have hrung := h.rung _ _ (h.step (j + 1) (by omega))
    have hrungj := h.rung _ _ (h.step j (by omega))
    have hBne := h.block_ne_nil (i := j + 1) (by omega)
    have hBjne := h.block_ne_nil (i := j) (by omega)
    obtain ⟨p1, hp1⟩ : ∃ p1, (R0 (c j) (c (j + 1))).getLast? = some p1 :=
      ⟨_, List.getLast?_eq_some_getLast hBjne⟩
    obtain ⟨q0, hq0⟩ : ∃ q0, (R0 (c (j + 1)) (c (j + 1 + 1))).head? = some q0 := by
      cases hB : R0 (c (j + 1)) (c (j + 1 + 1)) with
      | nil => exact absurd hB hBne
      | cons a t => exact ⟨a, rfl⟩
    have hp1mem : p1 ∈ R0 (c j) (c (j + 1)) := List.mem_of_getLast? hp1
    have hq0mem : q0 ∈ R0 (c (j + 1)) (c (j + 1 + 1)) := List.mem_of_mem_head? hq0
    have hdisj : ∀ v ∈ blocks R0 c (j + 1), v ∉ R0 (c (j + 1)) (c (j + 1 + 1)) := by
      intro v hv hv'
      obtain ⟨i, hi, hvi⟩ := hmem v hv
      exact h.block_disjoint (i := i) (j := j + 1) (by omega) (by omega) (by omega) hvi hv'
    have hcross : ∀ u ∈ blocks R0 c (j + 1), ∀ v ∈ R0 (c (j + 1)) (c (j + 1 + 1)),
        G.Adj u v ↔ (u = p1 ∧ v = q0) := by
      intro u hu v hv
      obtain ⟨i, hi, hui⟩ := hmem u hu
      by_cases hij : i = j
      · subst hij
        rw [h.adj_blocks (i := i) (j := i + 1) (by omega) (by omega) (by omega) hui hv]
        have e1 : u ∈ N (c (i + 1)) ↔ u = p1 := by
          rw [hrungj.2.2.2 u hui, hp1]; simp [eq_comm]
        have e2 : v ∈ N (c (i + 1)) ↔ v = q0 := by
          rw [hrung.2.2.1 v hv, hq0]; simp [eq_comm]
        constructor
        · rintro (⟨_, a, b⟩ | ⟨hh, _⟩)
          · exact ⟨e1.mp a, e2.mp b⟩
          · omega
        · rintro ⟨a, b⟩
          exact Or.inl ⟨rfl, e1.mpr a, e2.mpr b⟩
      · have hne : ¬ G.Adj u v := by
          rw [h.adj_blocks (i := i) (j := j + 1) (by omega) (by omega) (by omega) hui hv]
          rintro (⟨hh, _⟩ | ⟨hh, _⟩) <;> omega
        constructor
        · intro hh; exact absurd hh hne
        · rintro ⟨rfl, _⟩
          exact absurd (h.block_disjoint (i := i) (j := j) (by omega) (by omega) hij hui hp1mem)
            id
    have hpath' := isInducedPath_append G (blocks R0 c (j + 1)) (R0 (c (j + 1)) (c (j + 1 + 1)))
      p1 q0 hpath hrung.1 (hlast.trans hp1) hq0 hdisj hcross
    have hne1 : blocks R0 c (j + 1) ≠ [] := hpath.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [blocks_succ _ _ (j + 1)]; exact hpath'
    · rw [blocks_succ _ _ (j + 1), List.head?_append_of_ne_nil _ hne1, hhead]
    · rw [blocks_succ _ _ (j + 1), List.getLast?_append_of_ne_nil _ hBne]
    · intro z hz
      rw [blocks_succ _ _ (j + 1), List.mem_append] at hz
      rcases hz with hz | hz
      · obtain ⟨i, hi, hzi⟩ := hmem z hz
        exact ⟨i, by omega, hzi⟩
      · exact ⟨j + 1, by omega, hz⟩

theorem length_blocks_ge (h : Setup J G S N R0 c k) : ∀ j, j ≤ k → j ≤ (blocks R0 c j).length := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have hne := h.block_ne_nil (i := j) (by omega)
    have h2 : 0 < (R0 (c j) (c (j + 1))).length := List.length_pos_iff.mpr hne
    rw [blocks_succ, List.length_append]
    omega

/-- The closing strip's rung together with the chain of blocks forms a hole. -/
theorem hole_closure (hG : IsBerge G) (h : Setup J G S N R0 c k) (hk : 3 ≤ k)
    (hclose : J.Adj (c k) (c 0)) (R : List V)
    (hR : StrongPerfectGraph.LineGraph.IsRung G S N (c k) (c 0) R) :
    Even (R.length + (blocks R0 c k).length) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hpath, hhead, hlast, hmem⟩ := h.blocks_spec m (le_refl _)
  have hrung0 := h.rung _ _ (h.step 0 (by omega))
  have hrungm := h.rung _ _ (h.step m (by omega))
  have hB0ne : R0 (c 0) (c 1) ≠ [] := h.block_ne_nil (i := 0) (by omega)
  have hBmne := h.block_ne_nil (i := m) (by omega)
  have hRne : R ≠ [] := hR.1.1
  obtain ⟨p0, hp0⟩ : ∃ p0, R.head? = some p0 := by
    rcases hRR : R with _ | ⟨a, t⟩
    · exact absurd hRR hRne
    · exact ⟨a, rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ p1, R.getLast? = some p1 := ⟨_, List.getLast?_eq_some_getLast hRne⟩
  obtain ⟨q0, hq0⟩ : ∃ q0, (R0 (c 0) (c 1)).head? = some q0 := by
    rcases hB : R0 (c 0) (c 1) with _ | ⟨a, t⟩
    · exact absurd hB hB0ne
    · exact ⟨a, rfl⟩
  obtain ⟨q1, hq1⟩ : ∃ q1, (R0 (c m) (c (m + 1))).getLast? = some q1 :=
    ⟨_, List.getLast?_eq_some_getLast hBmne⟩
  have hq0mem : q0 ∈ R0 (c 0) (c 1) := List.mem_of_mem_head? hq0
  have hq1mem : q1 ∈ R0 (c m) (c (m + 1)) := List.mem_of_getLast? hq1
  have hThead : (blocks R0 c (m + 1)).head? = some q0 := hhead.trans hq0
  have hTlast : (blocks R0 c (m + 1)).getLast? = some q1 := hlast.trans hq1
  have hzS0 : ∀ z ∈ R, z ∈ S (c (m + 1)) (c 0) := fun z hz => hR.2.1 z hz
  have e0 : ∀ z ∈ R, (z ∈ N (c 0) ↔ z = p1) := fun z hz => by
    rw [hR.2.2.2 z hz, hp1]; simp [eq_comm]
  have e1 : ∀ z ∈ R, (z ∈ N (c (m + 1)) ↔ z = p0) := fun z hz => by
    rw [hR.2.2.1 z hz, hp0]; simp [eq_comm]
  have f0 : ∀ z' ∈ R0 (c 0) (c 1), (z' ∈ N (c 0) ↔ z' = q0) := fun z' hz' => by
    rw [hrung0.2.2.1 z' hz', hq0]; simp [eq_comm]
  have fm : ∀ z' ∈ R0 (c m) (c (m + 1)), (z' ∈ N (c (m + 1)) ↔ z' = q1) := fun z' hz' => by
    rw [hrungm.2.2.2 z' hz', hq1]; simp [eq_comm]
  have hdisj : ∀ z ∈ R, z ∉ blocks R0 c (m + 1) := by
    intro z hz hzT
    obtain ⟨i, hi, hzi⟩ := hmem z hzT
    have hne : s(c (m + 1), c 0) ≠ s(c i, c (i + 1)) := by
      intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := h.inj _ _ (le_refl _) (by omega) h1; omega
      · have := h.inj _ _ (le_refl _) (by omega) h1
        have := h.inj _ _ (by omega) (by omega) h2
        omega
    exact Set.disjoint_left.mp (h.disj _ _ _ _ hclose (h.step i hi) hne) (hzS0 z hz)
      (h.block_mem hi hzi)
  have hcross : ∀ z ∈ R, ∀ z' ∈ blocks R0 c (m + 1),
      G.Adj z z' ↔ (z = p0 ∧ z' = q1) ∨ (z = p1 ∧ z' = q0) := by
    intro z hz z' hz'
    obtain ⟨i, hi, hzi⟩ := hmem z' hz'
    have hzS := hzS0 z hz
    have hz'S := h.block_mem hi hzi
    by_cases hi0 : i = 0
    · subst hi0
      have hsh := h.share (c 0) (c (m + 1)) (c (0 + 1)) hclose.symm (h.step 0 (by omega))
        (fun heq => by have := h.inj _ _ (le_refl _) (by omega) heq; omega) z
        (by rw [h.symm _ _ hclose] at hzS; exact hzS) z' hz'S
      rw [hsh, e0 z hz, f0 z' hzi]
      constructor
      · rintro ⟨a, b⟩; exact Or.inr ⟨a, b⟩
      · rintro (⟨_, hh⟩ | ⟨a, b⟩)
        · exfalso
          have hz'm : z' ∈ R0 (c m) (c (m + 1)) := by rw [hh]; exact hq1mem
          exact h.block_disjoint (i := 0) (j := m) (by omega) (by omega) (by omega) hzi hz'm
        · exact ⟨a, b⟩
    · by_cases him : i = m
      · subst him
        have hsh := h.share (c (i + 1)) (c 0) (c i) hclose (h.step i (by omega)).symm
          (fun heq => by have := h.inj _ _ (by omega) (by omega) heq; omega) z hzS z'
          (by rw [h.symm _ _ (h.step i (by omega))] at hz'S; exact hz'S)
        rw [hsh, e1 z hz, fm z' hzi]
        constructor
        · rintro ⟨a, b⟩; exact Or.inl ⟨a, b⟩
        · rintro (⟨a, b⟩ | ⟨_, hh⟩)
          · exact ⟨a, b⟩
          · exfalso
            have hz'0 : z' ∈ R0 (c 0) (c 1) := by rw [hh]; exact hq0mem
            exact h.block_disjoint (i := 0) (j := i) (by omega) (by omega) (by omega) hz'0 hzi
      · have hfar := h.far (c (m + 1)) (c 0) (c i) (c (i + 1)) hclose (h.step i hi)
          (fun heq => by have := h.inj _ _ (le_refl _) (by omega) heq; omega)
          (fun heq => by have := h.inj _ _ (le_refl _) (by omega) heq; omega)
          (fun heq => by have := h.inj _ _ (by omega) (by omega) heq; omega)
          (fun heq => by have := h.inj _ _ (by omega) (by omega) heq; omega) z hzS z' hz'S
        constructor
        · intro hh; exact absurd hh hfar
        · rintro (⟨_, hh⟩ | ⟨_, hh⟩)
          · exfalso
            have hz'm : z' ∈ R0 (c m) (c (m + 1)) := by rw [hh]; exact hq1mem
            exact h.block_disjoint (i := i) (j := m) (by omega) (by omega) him hzi hz'm
          · exfalso
            have hz'0 : z' ∈ R0 (c 0) (c 1) := by rw [hh]; exact hq0mem
            exact h.block_disjoint (i := 0) (j := i) (by omega) (by omega) (by omega) hz'0 hzi
  have hlenT := h.length_blocks_ge (m + 1) (le_refl _)
  have hRpos : 1 ≤ R.length := List.length_pos_iff.mpr hRne
  have hole : IsHole G (R ++ blocks R0 c (m + 1)) :=
    isHole_append G R (blocks R0 c (m + 1)) p0 p1 q0 q1 hR.1 hpath hRpos (by omega) (by omega)
      hp0 hp1 hThead hTlast hdisj hcross
  have := hG.1 _ hole
  simpa using this

end Setup

end Strips

section Cycle
open StrongPerfectGraph.LineGraph
variable {W : Type*}

/-- In a 3-connected graph, deleting at most two vertices leaves every other vertex a neighbour
outside the deleted set. -/
theorem exists_nbr_outside [Fintype W] (J : SimpleGraph W) (hJ : IsThreeConnected J)
    (S : Set W) (hS : S.ncard ≤ 2) (a : W) (ha : a ∉ S) : ∃ y, y ∉ S ∧ J.Adj a y := by
  classical
  by_contra hno
  push Not at hno
  have hconn := hJ.2 S hS
  -- there is another vertex outside S
  have hcard : 3 < Fintype.card W := by simpa [Nat.card_eq_fintype_card] using hJ.1
  have hSc : 2 ≤ (Sᶜ : Set W).ncard := by
    have h1 : (Sᶜ : Set W).ncard + S.ncard = Nat.card W := by
      rw [add_comm]; exact Set.ncard_add_ncard_compl S
    rw [Nat.card_eq_fintype_card] at h1
    omega
  obtain ⟨t, htS, hta⟩ : ∃ t ∈ (Sᶜ : Set W), t ≠ a := by
    by_contra hcon
    push Not at hcon
    have : (Sᶜ : Set W) ⊆ {a} := fun x hx => hcon x hx
    have := Set.ncard_le_ncard this (Set.finite_singleton a)
    rw [Set.ncard_singleton] at this
    omega
  obtain ⟨w⟩ := hconn.preconnected ⟨a, ha⟩ ⟨t, htS⟩
  cases w with
  | nil => exact hta rfl
  | cons h p =>
    rename_i y
    exact hno y.1 y.2 (by simpa using h)


theorem two_le_length_of_ends {L : List W} {a b : W} (h1 : L.head? = some a)
    (h2 : L.getLast? = some b) (hab : a ≠ b) : 2 ≤ L.length := by
  rcases L with _ | ⟨x, _ | ⟨y, t⟩⟩
  · simp at h1
  · simp at h1 h2
    exact absurd (h1.symm.trans h2) hab
  · simp

/-- In a 3-connected graph every edge `uv` lies on a cycle with at least four vertices; as a list
this is a duplicate-free path from `v` to `u` with at least four vertices. -/
theorem exists_long_path [Fintype W] [DecidableEq W] (J : SimpleGraph W) (hJ : IsThreeConnected J)
    (u v : W) (huv : J.Adj u v) :
    ∃ q : List W, q.head? = some v ∧ q.getLast? = some u ∧ q.Nodup ∧
      List.IsChain J.Adj q ∧ 4 ≤ q.length := by
  classical
  obtain ⟨z', hz'u, hvz'⟩ := exists_nbr_outside J hJ {u}
    (by simp [Set.ncard_singleton]) v (by simpa using huv.ne.symm)
  have hz'u' : z' ≠ u := by simpa using hz'u
  have hpair : ({v, z'} : Set W).ncard ≤ 2 := by
    have := Set.ncard_insert_le v ({z'} : Set W)
    rw [Set.ncard_singleton] at this
    exact this
  obtain ⟨z, hzS, huz⟩ := exists_nbr_outside J hJ {v, z'} hpair u
    (by simp [huv.ne, hz'u'.symm])
  have hzv : z ≠ v := fun h => hzS (by simp [h])
  have hzz' : z ≠ z' := fun h => hzS (by simp [h])
  have hS3 : ({u, v} : Set W).ncard ≤ 2 := by
    have := Set.ncard_insert_le u ({v} : Set W)
    rw [Set.ncard_singleton] at this
    exact this
  have hH := hJ.2 {u, v} hS3
  have hz'S3 : z' ∈ ({u, v} : Set W)ᶜ := by
    simp [hz'u', hvz'.ne.symm]
  have hzS3 : z ∈ ({u, v} : Set W)ᶜ := by
    simp [huz.ne.symm, hzv]
  obtain ⟨w⟩ := hH.preconnected ⟨z', hz'S3⟩ ⟨z, hzS3⟩
  let P := w.toPath
  let L : List W := P.1.support.map Subtype.val
  have hLne : L ≠ [] := by
    simp only [L, ne_eq, List.map_eq_nil_iff]
    exact SimpleGraph.Walk.support_ne_nil _
  have hLhead : L.head? = some z' := by
    simp only [L, List.head?_map]
    rw [← SimpleGraph.Walk.cons_tail_support P.1]
    rfl
  have hLlast : L.getLast? = some z := by
    simp only [L, List.getLast?_map]
    rw [List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil P.1),
      SimpleGraph.Walk.getLast_support]
    rfl
  have hLnd : L.Nodup := P.2.support_nodup.map Subtype.val_injective
  have hLchain : List.IsChain J.Adj L :=
    List.isChain_map_of_isChain Subtype.val (fun a b h => h) P.1.isChain_adj_support
  have hLmem : ∀ x ∈ L, x ≠ u ∧ x ≠ v := by
    intro x hx
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
    have := s.2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at this
    exact this
  have hlen : 2 ≤ L.length := two_le_length_of_ends hLhead hLlast hzz'.symm
  refine ⟨v :: (L ++ [u]), rfl, by simp [List.getLast?_cons, List.getLast?_append], ?_, ?_, ?_⟩
  · rw [List.nodup_cons, List.nodup_append]
    refine ⟨?_, ⟨hLnd, List.nodup_singleton u, ?_⟩⟩
    · simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨fun h => (hLmem v h).2 rfl, huv.ne.symm⟩
    · intro a ha b hb
      simp at hb
      subst hb
      exact fun h => (hLmem _ ha).1 h
  · rw [List.isChain_cons]
    refine ⟨?_, ?_⟩
    · intro y hy
      rw [List.head?_append_of_ne_nil _ hLne, hLhead] at hy
      simp at hy
      subst hy
      exact hvz'
    · refine List.IsChain.append hLchain (List.IsChain.singleton u) ?_
      intro x hx y hy
      simp at hx hy
      rw [hLlast] at hx
      have hx' := Option.some.inj hx
      subst hx'; subst hy
      exact huz.symm
  · simp
    omega


theorem exists_cycle_fun [Fintype W] (J : SimpleGraph W) (hJ : IsThreeConnected J) (u v : W)
    (huv : J.Adj u v) :
    ∃ (k : ℕ) (c : ℕ → W), 3 ≤ k ∧ c 0 = v ∧ c k = u ∧
      (∀ i j, i ≤ k → j ≤ k → c i = c j → i = j) ∧ ∀ i, i < k → J.Adj (c i) (c (i + 1)) := by
  classical
  obtain ⟨q, hqh, hql, hnd, hch, hlen⟩ := exists_long_path J hJ u v huv
  have hc : ∀ i (hi : i < q.length), q.getD i v = q[i] := fun i hi => List.getD_eq_getElem q v hi
  refine ⟨q.length - 1, fun i => q.getD i v, by omega, ?_, ?_, ?_, ?_⟩
  · show q.getD 0 v = v
    rw [hc 0 (by omega)]
    have := hqh
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at this
    exact Option.some.inj this
  · show q.getD (q.length - 1) v = u
    rw [hc _ (by omega)]
    have := hql
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at this
    exact Option.some.inj this
  · intro i j hi hj hij
    simp only [hc i (by omega), hc j (by omega)] at hij
    exact (hnd.getElem_inj_iff).mp hij
  · intro i hi
    simp only [hc i (by omega), hc (i + 1) (by omega)]
    exact List.isChain_iff_getElem.mp hch i (by omega)

end Cycle

end SPGTLib

open StrongPerfectGraph.LineGraph in
theorem solution {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (hG : StrongPerfectGraph.Main.IsBerge G) (J : SimpleGraph W)
    (hJ : IsThreeConnected J)
    (S : W → W → Set V) (N : W → Set V) (hSN : IsStripSystem J G S N) :
    ∀ u v : W, J.Adj u v → ∀ R R' : List V, IsRung G S N u v R → IsRung G S N u v R' →
      (R.length - 1) % 2 = (R'.length - 1) % 2 := by
  intro u v huv R R' hR hR'
  obtain ⟨hs1, hs2, _, _, hs5, hs6, R0, hR0, _⟩ := hSN
  obtain ⟨k, c, hk, hc0, hck, hinj, hstep⟩ := SPGTLib.exists_cycle_fun J hJ u v huv
  have hsetup : SPGTLib.Setup J G S N R0 c k :=
    ⟨hs1, hs2, hs5, hs6, fun x y hxy => (hR0 x y hxy).1, hinj, hstep⟩
  have hclose : J.Adj (c k) (c 0) := by rw [hck, hc0]; exact huv
  have h1 := hsetup.hole_closure hG hk hclose R (by rw [hck, hc0]; exact hR)
  have h2 := hsetup.hole_closure hG hk hclose R' (by rw [hck, hc0]; exact hR')
  have hRpos : 1 ≤ R.length := List.length_pos_iff.mpr hR.1.1
  have hR'pos : 1 ≤ R'.length := List.length_pos_iff.mpr hR'.1.1
  rw [Nat.even_iff] at h1 h2
  omega
