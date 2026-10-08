-- Prove2me | solution 1 for StrongPerfectGraph.EvenPrism.prism_paths_same_parity
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T11:56:20.554996+00:00
-- url     : https://prove2.me/submissions/3007a085-9290-4d9d-a338-2200064eb58a

/-
Chudnovsky–Robertson–Seymour–Thomas, 7.2: the three paths of a prism in a Berge graph have
lengths of the same parity.

Any two prism paths `R i` and `R j` together with the two end edges form a hole of length
`|R i| + |R j|` (counted in vertices), which is even because the graph is Berge.
-/
import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_IsInducedPath
import Definitions.Def_StrongPerfectGraph_EvenPrism_Prism

set_option autoImplicit false

namespace SPGTLib

open StrongPerfectGraph.Main

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
    (hPl : 2 ≤ P.length) (hQl : 2 ≤ Q.length)
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
    -- positions of the special vertices inside a nodup list
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
      rw [List.getElem_append_right (by omega : P.length ≤ i), List.getElem_append_right (by omega : P.length ≤ j),
        hQadj _ _ hi'' hj'', succ_mod_eq hi, succ_mod_eq hj]
      split_ifs <;> omega

end SPGTLib

open StrongPerfectGraph.EvenPrism in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : StrongPerfectGraph.Main.IsBerge G) (a b : Fin 3 → V)
    (R : Fin 3 → List V) (hR : IsPrism G a b R) :
    ∀ i j, Even ((R i).length - 1) ↔ Even ((R j).length - 1) := by
  intro i j
  by_cases hij : i = j
  · subst hij; exact Iff.rfl
  obtain ⟨hpath, hdisj, hcross⟩ := hR
  obtain ⟨hPi, hPl, hP0, hP1⟩ := hpath i
  obtain ⟨hPj, hQl, hQ0, hQ1⟩ := hpath j
  have hhole : StrongPerfectGraph.Main.IsHole G (R i ++ (R j).reverse) := by
    refine SPGTLib.isHole_append G (R i) (R j).reverse (a i) (b i) (b j) (a j)
      hPi (SPGTLib.isInducedPath_reverse hPj) hPl (by simpa using hQl) hP0 hP1
      (by simpa [List.head?_reverse] using hQ1) (by simpa [List.getLast?_reverse] using hQ0)
      (fun v hv hv' => hdisj i j hij v hv (List.mem_reverse.mp hv')) ?_
    intro u hu v hv
    exact hcross i j hij u hu v (List.mem_reverse.mp hv)
  have heven := hG.1 _ hhole
  simp only [List.length_append, List.length_reverse, Nat.even_iff] at heven ⊢
  omega
