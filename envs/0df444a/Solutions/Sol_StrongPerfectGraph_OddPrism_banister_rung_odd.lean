-- Prove2me | solution 1 for StrongPerfectGraph.OddPrism.banister_rung_odd
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T12:31:30.937428+00:00
-- url     : https://prove2.me/submissions/999d9d77-95a5-40c8-9c84-157336557ff4

/-
Chudnovsky–Robertson–Seymour–Thomas, 11.3: in a Berge graph with no even prism, every rung of a
step-connected strip is odd, and so is the banister.

Proof. A step together with the banister forms a prism, which cannot be even, and in a Berge graph
the three paths of a prism have the same parity (each pair closes up to a hole); so the banister is
odd. For any rung `a-R-b`, the hole `a0-R0-b0-b-R-a-a0` is even, so `R` is odd as well.
-/
import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_IsInducedPath
import Definitions.Def_StrongPerfectGraph_OddPrism_IsBerge
import Definitions.Def_StrongPerfectGraph_OddPrism_IsPrism
import Definitions.Def_StrongPerfectGraph_OddPrism_IsStepConnectedStrip
import Definitions.Def_StrongPerfectGraph_OddPrism_IsStaircase

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

section Banister
variable {V : Type*}

theorem two_le_length_of_ends {L : List V} {a b : V} (h1 : L.head? = some a)
    (h2 : L.getLast? = some b) (hab : a ≠ b) : 2 ≤ L.length := by
  rcases L with _ | ⟨x, _ | ⟨y, t⟩⟩
  · simp at h1
  · simp at h1 h2
    exact absurd (h1.symm.trans h2) hab
  · simp

/-- Facts about a rung `a-R-b` of a strip: only its first vertex is in `A`, only its last in `B`,
and all its vertices lie in `A ∪ B ∪ C`. -/
theorem rung_facts {A C B : Set V} (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {r : List V} {a b : V} (ha : r.head? = some a) (hb : r.getLast? = some b)
    (haA : a ∈ A) (hbB : b ∈ B) (hint : ∀ x ∈ r, x ≠ a → x ≠ b → x ∈ C) :
    ∀ y ∈ r, (y ∈ A ↔ y = a) ∧ (y ∈ B ↔ y = b) := by
  have hmem_a : a ∈ r := List.mem_of_mem_head? ha
  have hmem_b : b ∈ r := List.mem_of_getLast? hb
  have hab : a ≠ b := fun h => Set.disjoint_left.mp hAB haA (h ▸ hbB)
  intro y hy
  by_cases hya : y = a
  · subst hya
    exact ⟨⟨fun _ => rfl, fun _ => haA⟩, ⟨fun h => absurd h (Set.disjoint_left.mp hAB haA),
      fun h => absurd h hab⟩⟩
  · by_cases hyb : y = b
    · subst hyb
      exact ⟨⟨fun h => absurd h (Set.disjoint_right.mp hAB hbB), fun h => absurd h hya⟩,
        ⟨fun _ => rfl, fun _ => hbB⟩⟩
    · have hyC := hint y hy hya hyb
      have hyA : y ∉ A := fun h => Set.disjoint_left.mp hAC h hyC
      have hyB : y ∉ B := fun h => Set.disjoint_left.mp hBC h hyC
      exact ⟨⟨fun h => absurd h hyA, fun h => absurd h hya⟩,
        ⟨fun h => absurd h hyB, fun h => absurd h hyb⟩⟩


/-- Adjacency between a banister and a rung: only the two ends are matched. -/
theorem banister_rung_adj (G : SimpleGraph V) {A C B : Set V}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {r0 : List V} {a0 b0 : V}
    (hleft : StrongPerfectGraph.OddPrism.IsLeftStar G A C B a0)
    (hright : StrongPerfectGraph.OddPrism.IsRightStar G A C B b0) (hne : a0 ≠ b0)
    (hint0 : ∀ x ∈ r0, x ≠ a0 → x ≠ b0 → ∀ s ∈ A ∪ B ∪ C, ¬ G.Adj x s)
    {r : List V} {a b : V} (ha : r.head? = some a) (hb : r.getLast? = some b)
    (haA : a ∈ A) (hbB : b ∈ B) (hintr : ∀ x ∈ r, x ≠ a → x ≠ b → x ∈ C) :
    ∀ x ∈ r0, ∀ y ∈ r, G.Adj x y ↔ (x = a0 ∧ y = a) ∨ (x = b0 ∧ y = b) := by
  intro x hx y hy
  have hf := rung_facts hAB hAC hBC ha hb haA hbB hintr y hy
  have hyS : y ∈ A ∪ B ∪ C := by
    by_cases hya : y = a
    · exact Or.inl (Or.inl (hya ▸ haA))
    · by_cases hyb : y = b
      · exact Or.inl (Or.inr (hyb ▸ hbB))
      · exact Or.inr (hintr y hy hya hyb)
  by_cases hxa : x = a0
  · subst hxa
    constructor
    · intro hadj
      left
      refine ⟨rfl, ?_⟩
      have hyA : y ∈ A := by
        rcases hyS with (h | h) | h
        · exact h
        · exact absurd (hadj) (hleft.2.2 y (Or.inl h))
        · exact absurd (hadj) (hleft.2.2 y (Or.inr h))
      exact hf.1.mp hyA
    · rintro (⟨_, rfl⟩ | ⟨h, _⟩)
      · exact hleft.2.1 _ haA
      · exact absurd h hne
  · by_cases hxb : x = b0
    · subst hxb
      constructor
      · intro hadj
        right
        refine ⟨rfl, ?_⟩
        have hyB : y ∈ B := by
          rcases hyS with (h | h) | h
          · exact absurd hadj (hright.2.2 y (Or.inl h))
          · exact h
          · exact absurd hadj (hright.2.2 y (Or.inr h))
        exact hf.2.mp hyB
      · rintro (⟨h, _⟩ | ⟨_, rfl⟩)
        · exact absurd h.symm hne
        · exact hright.2.1 _ hbB
    · constructor
      · intro hadj
        exact absurd hadj (hint0 x hx hxa hxb y hyS)
      · rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact absurd h hxa
        · exact absurd h hxb


theorem isPrism_mk {V : Type*} (G : SimpleGraph V) (p1 p2 p3 : List V)
    (h1 : StrongPerfectGraph.OddPrism.IsInducedPath G p1 ∧ 1 ≤ p1.length - 1)
    (h2 : StrongPerfectGraph.OddPrism.IsInducedPath G p2 ∧ 1 ≤ p2.length - 1)
    (h3 : StrongPerfectGraph.OddPrism.IsInducedPath G p3 ∧ 1 ≤ p3.length - 1)
    (d12 : ∀ x ∈ p1, x ∉ p2) (d13 : ∀ x ∈ p1, x ∉ p3) (d23 : ∀ x ∈ p2, x ∉ p3)
    (a12 : ∀ x ∈ p1, ∀ y ∈ p2, G.Adj x y ↔
      (p1.head? = some x ∧ p2.head? = some y) ∨ (p1.getLast? = some x ∧ p2.getLast? = some y))
    (a13 : ∀ x ∈ p1, ∀ y ∈ p3, G.Adj x y ↔
      (p1.head? = some x ∧ p3.head? = some y) ∨ (p1.getLast? = some x ∧ p3.getLast? = some y))
    (a23 : ∀ x ∈ p2, ∀ y ∈ p3, G.Adj x y ↔
      (p2.head? = some x ∧ p3.head? = some y) ∨ (p2.getLast? = some x ∧ p3.getLast? = some y)) :
    StrongPerfectGraph.OddPrism.IsPrism G p1 p2 p3 := by
  have d21 : ∀ x ∈ p2, x ∉ p1 := fun x hx hx1 => d12 x hx1 hx
  have d31 : ∀ x ∈ p3, x ∉ p1 := fun x hx hx1 => d13 x hx1 hx
  have d32 : ∀ x ∈ p3, x ∉ p2 := fun x hx hx1 => d23 x hx1 hx
  have symm : ∀ (q q' : List V), (∀ x ∈ q', ∀ y ∈ q, G.Adj x y ↔
      (q'.head? = some x ∧ q.head? = some y) ∨ (q'.getLast? = some x ∧ q.getLast? = some y)) →
      ∀ x ∈ q, ∀ y ∈ q', G.Adj x y ↔
        (q.head? = some x ∧ q'.head? = some y) ∨ (q.getLast? = some x ∧ q'.getLast? = some y) := by
    intro q q' h x hx y hy
    rw [SimpleGraph.adj_comm, h y hy x hx]
    constructor <;> rintro (⟨u, v⟩ | ⟨u, v⟩)
    · exact Or.inl ⟨v, u⟩
    · exact Or.inr ⟨v, u⟩
    · exact Or.inl ⟨v, u⟩
    · exact Or.inr ⟨v, u⟩
  have a21 := symm p2 p1 a12
  have a31 := symm p3 p1 a13
  have a32 := symm p3 p2 a23
  unfold StrongPerfectGraph.OddPrism.IsPrism
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact h1
    · exact h2
    · exact h3
  · intro i j hij x hx
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact d12 x hx
    · exact d13 x hx
    · exact d21 x hx
    · exact absurd rfl hij
    · exact d23 x hx
    · exact d31 x hx
    · exact d32 x hx
    · exact absurd rfl hij
  · intro i j hij x hx y hy
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact a12 x hx y hy
    · exact a13 x hx y hy
    · exact a21 x hx y hy
    · exact absurd rfl hij
    · exact a23 x hx y hy
    · exact a31 x hx y hy
    · exact a32 x hx y hy
    · exact absurd rfl hij

end Banister

end SPGTLib

open StrongPerfectGraph.OddPrism in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : IsBerge G) (hprism : ¬ ContainsEvenPrism G)
    (A C B : Set V) (hS : IsStepConnected G A C B)
    (r₀ : List V) (hr₀ : IsBanister G A C B r₀) :
    (∀ r : List V, IsRung G A C B r → Odd (r.length - 1)) ∧ Odd (r₀.length - 1) := by
  obtain ⟨⟨hAB, hAC, hBC, hAne, hBne, _⟩, hstep, _, _⟩ := hS
  obtain ⟨hp0, hout0, a0, b0, ha0, hb0, hleft, hright, hint0⟩ := hr₀
  obtain ⟨β, hβ⟩ := hBne
  have hne : a0 ≠ b0 := by
    intro h
    subst h
    exact hleft.2.2 β (Or.inl hβ) (hright.2.1 β hβ)
  have hlen0 : 2 ≤ r₀.length := SPGTLib.two_le_length_of_ends ha0 hb0 hne
  -- every rung vertex lies in A ∪ B ∪ C
  have hrungS : ∀ r : List V, IsRung G A C B r → ∀ y ∈ r, y ∈ A ∪ B ∪ C := by
    rintro r ⟨_, a, b, ha, hb, haA, hbB, hint⟩ y hy
    by_cases hya : y = a
    · exact Or.inl (Or.inl (hya ▸ haA))
    · by_cases hyb : y = b
      · exact Or.inl (Or.inr (hyb ▸ hbB))
      · exact Or.inr (hint y hy hya hyb)
  -- the hole formed by the banister and a rung has even length
  have key : ∀ r : List V, IsRung G A C B r → Even (r₀.length + r.length) ∧ 2 ≤ r.length := by
    intro r hr
    obtain ⟨hpr, a, b, ha, hb, haA, hbB, hint⟩ := hr
    have hab : a ≠ b := fun h => Set.disjoint_left.mp hAB haA (h ▸ hbB)
    have hlen : 2 ≤ r.length := SPGTLib.two_le_length_of_ends ha hb hab
    have hcross := SPGTLib.banister_rung_adj G hAB hAC hBC hleft hright hne hint0 ha hb haA hbB hint
    have hdisj : ∀ x ∈ r₀, x ∉ r.reverse := by
      intro x hx hxr
      exact hout0 x hx (hrungS r ⟨hpr, a, b, ha, hb, haA, hbB, hint⟩ x (List.mem_reverse.mp hxr))
    have hhole : StrongPerfectGraph.Main.IsHole G (r₀ ++ r.reverse) :=
      SPGTLib.isHole_append G r₀ r.reverse a0 b0 b a hp0 (SPGTLib.isInducedPath_reverse hpr)
        (by omega) (by simp; omega) (by simp; omega) ha0 hb0
        (by simpa [List.head?_reverse] using hb) (by simpa [List.getLast?_reverse] using ha)
        hdisj (fun x hx y hy => hcross x hx y (List.mem_reverse.mp hy))
    have := hG.1 _ hhole
    exact ⟨by simpa using this, hlen⟩
  obtain ⟨α, hα⟩ := hAne
  obtain ⟨r₁, r₂, ⟨hr1, hr2, hdisj12, hadj12⟩, _⟩ := hstep α (Or.inl (Or.inl hα))
  have k1 := key r₁ hr1
  have k2 := key r₂ hr2
  have hr1S := hrungS r₁ hr1
  have hr2S := hrungS r₂ hr2
  obtain ⟨hp1, a1, b1, ha1, hb1, ha1A, hb1B, hint1⟩ := hr1
  obtain ⟨hp2, a2, b2, ha2, hb2, ha2A, hb2B, hint2⟩ := hr2
  have h12 : Even (r₁.length + r₂.length) := by
    have hhole : StrongPerfectGraph.Main.IsHole G (r₁ ++ r₂.reverse) :=
      SPGTLib.isHole_append G r₁ r₂.reverse a1 b1 b2 a2 hp1 (SPGTLib.isInducedPath_reverse hp2)
        (by omega) (by simp; omega) (by simp; omega) ha1 hb1
        (by simpa [List.head?_reverse] using hb2) (by simpa [List.getLast?_reverse] using ha2)
        (fun x hx hxr => hdisj12 x hx (List.mem_reverse.mp hxr))
        (fun x hx y hy => by
          rw [hadj12 x hx y (List.mem_reverse.mp hy)]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · rw [ha1] at h1; rw [ha2] at h2
              exact Or.inl ⟨(Option.some.inj h1).symm, (Option.some.inj h2).symm⟩
            · rw [hb1] at h1; rw [hb2] at h2
              exact Or.inr ⟨(Option.some.inj h1).symm, (Option.some.inj h2).symm⟩
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · subst h1; subst h2; exact Or.inl ⟨ha1, ha2⟩
            · subst h1; subst h2; exact Or.inr ⟨hb1, hb2⟩)
    simpa using hG.1 _ hhole
  have hab : ∀ {a b : V}, a ∈ A → b ∈ B → a ≠ b :=
    fun {a b} haA hbB h => Set.disjoint_left.mp hAB haA (h ▸ hbB)
  have hcross : ∀ (r : List V) (a b : V), r.head? = some a → r.getLast? = some b → a ∈ A → b ∈ B →
      (∀ x ∈ r, x ≠ a → x ≠ b → x ∈ C) → ∀ x ∈ r₀,  ∀ y ∈ r,
      G.Adj x y ↔ (r₀.head? = some x ∧ r.head? = some y) ∨
        (r₀.getLast? = some x ∧ r.getLast? = some y) := by
    intro r a b ha hb haA hbB hint x hx y hy
    rw [SPGTLib.banister_rung_adj G hAB hAC hBC hleft hright hne hint0 ha hb haA hbB hint x hx y hy]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · subst h1; subst h2; exact Or.inl ⟨ha0, ha⟩
      · subst h1; subst h2; exact Or.inr ⟨hb0, hb⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · rw [ha0] at h1; rw [ha] at h2
        exact Or.inl ⟨(Option.some.inj h1).symm, (Option.some.inj h2).symm⟩
      · rw [hb0] at h1; rw [hb] at h2
        exact Or.inr ⟨(Option.some.inj h1).symm, (Option.some.inj h2).symm⟩
  have hPrism : IsPrism G r₀ r₁ r₂ :=
    SPGTLib.isPrism_mk G r₀ r₁ r₂ ⟨hp0, by omega⟩ ⟨hp1, by have := k1.2; omega⟩
      ⟨hp2, by have := k2.2; omega⟩
      (fun x hx hx1 => hout0 x hx (hr1S x hx1)) (fun x hx hx2 => hout0 x hx (hr2S x hx2))
      hdisj12
      (hcross r₁ a1 b1 ha1 hb1 ha1A hb1B hint1) (hcross r₂ a2 b2 ha2 hb2 ha2A hb2B hint2) hadj12
  have e1 := k1.1
  have e2 := k2.1
  rw [Nat.even_iff] at e1 e2 h12
  have hl1 := k1.2
  have hl2 := k2.2
  have hodd0 : Odd (r₀.length - 1) := by
    by_contra hcon
    rw [Nat.not_odd_iff_even] at hcon
    apply hprism
    refine ⟨r₀, r₁, r₂, hPrism, hcon, ?_, ?_⟩
    · rw [Nat.even_iff]; rw [Nat.even_iff] at hcon; omega
    · rw [Nat.even_iff]; rw [Nat.even_iff] at hcon; omega
  refine ⟨fun r hr => ?_, hodd0⟩
  have hk := key r hr
  have hk1 := hk.1
  have hk2 := hk.2
  rw [Nat.even_iff] at hk1
  rw [Nat.odd_iff] at hodd0 ⊢
  omega
