-- Prove2me | solution 1 for SteinbergFalse.Counterexample.G_not_colorable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T15:27:45.429863+00:00
-- url     : https://prove2.me/submissions/13a8cb90-83f0-4cb9-a796-b021d208dd36

import Mathlib
import Definitions.Def_SteinbergFalse_Counterexample_G

set_option autoImplicit false

namespace SteinbergColorAux
open SteinbergFalse.Counterexample

theorem uniq3 {x y e g : Fin 3} (hxy : x ≠ y) (he1 : e ≠ x) (he2 : e ≠ y) (hg1 : g ≠ x)
    (hg2 : g ≠ y) : e = g := by
  revert x y e g; decide

theorem none3 {x y z w : Fin 3} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (h1 : w ≠ x)
    (h2 : w ≠ y) (h3 : w ≠ z) : False := by
  revert x y z w; decide

theorem two3 {a b c d : Fin 3} (h1 : b ≠ a) (h2 : b ≠ c) (h3 : b ≠ d) (h4 : c ≠ d) :
    a = c ∨ a = d := by
  revert a b c d; decide

def E1 : List (Sym2 (Fin 15)) := [s(0, 5), s(0, 6), s(5, 6), s(1, 4), s(1, 3), s(3, 4), s(2, 7),
  s(2, 8), s(7, 8), s(4, 5), s(4, 10), s(5, 10), s(6, 7), s(6, 11), s(7, 11), s(3, 9), s(8, 9), s(9, 12),
  s(10, 13), s(11, 14), s(12, 13), s(13, 14), s(12, 14)]

theorem G1_adj_of {u v : Fin 15} (h : s(u, v) ∈ E1) (hne : u ≠ v) : G1.Adj u v := by
  rw [G1, SimpleGraph.fromEdgeSet_adj]
  refine ⟨?_, hne⟩
  simp only [E1, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact h

theorem lemma1_color (C : G1.Coloring (Fin 3)) : ¬ (C 0 = C 1 ∧ C 1 = C 2) := by
  rintro ⟨h01, h12⟩
  have v : ∀ {u w : Fin 15}, G1.Adj u w → C u ≠ C w := fun h => C.valid h
  have af := v (G1_adj_of (u := 0) (v := 5) (by decide +kernel) (by decide))
  have ag := v (G1_adj_of (u := 0) (v := 6) (by decide +kernel) (by decide))
  have fg := v (G1_adj_of (u := 5) (v := 6) (by decide +kernel) (by decide))
  have be := v (G1_adj_of (u := 1) (v := 4) (by decide +kernel) (by decide))
  have bd := v (G1_adj_of (u := 1) (v := 3) (by decide +kernel) (by decide))
  have de := v (G1_adj_of (u := 3) (v := 4) (by decide +kernel) (by decide))
  have ch := v (G1_adj_of (u := 2) (v := 7) (by decide +kernel) (by decide))
  have ci := v (G1_adj_of (u := 2) (v := 8) (by decide +kernel) (by decide))
  have hi := v (G1_adj_of (u := 7) (v := 8) (by decide +kernel) (by decide))
  have ef := v (G1_adj_of (u := 4) (v := 5) (by decide +kernel) (by decide))
  have ek := v (G1_adj_of (u := 4) (v := 10) (by decide +kernel) (by decide))
  have fk := v (G1_adj_of (u := 5) (v := 10) (by decide +kernel) (by decide))
  have gh := v (G1_adj_of (u := 6) (v := 7) (by decide +kernel) (by decide))
  have gl := v (G1_adj_of (u := 6) (v := 11) (by decide +kernel) (by decide))
  have hl := v (G1_adj_of (u := 7) (v := 11) (by decide +kernel) (by decide))
  have dj := v (G1_adj_of (u := 3) (v := 9) (by decide +kernel) (by decide))
  have ij := v (G1_adj_of (u := 8) (v := 9) (by decide +kernel) (by decide))
  have jm := v (G1_adj_of (u := 9) (v := 12) (by decide +kernel) (by decide))
  have kn := v (G1_adj_of (u := 10) (v := 13) (by decide +kernel) (by decide))
  have lo := v (G1_adj_of (u := 11) (v := 14) (by decide +kernel) (by decide))
  have mn := v (G1_adj_of (u := 12) (v := 13) (by decide +kernel) (by decide))
  have no := v (G1_adj_of (u := 13) (v := 14) (by decide +kernel) (by decide))
  have mo := v (G1_adj_of (u := 12) (v := 14) (by decide +kernel) (by decide))
  rw [← h01] at be bd
  rw [← h12, ← h01] at ch ci
  have hk : C 10 = C 0 := uniq3 ef ek.symm fk.symm be af
  have hl' : C 11 = C 0 := uniq3 gh gl.symm hl.symm ag ch
  have hn : C 0 ≠ C 13 := by rw [← hk]; exact kn
  have ho : C 0 ≠ C 14 := by rw [← hl']; exact lo
  have hm : C 12 = C 0 := uniq3 no mn mo hn ho
  have hj : C 9 ≠ C 0 := by rw [← hm]; exact jm
  have heg : C 4 = C 6 := uniq3 af.symm ef be.symm fg.symm ag.symm
  have hhf : C 7 = C 5 := uniq3 ag.symm gh.symm ch.symm fg af.symm
  have hdf : C 3 = C 5 := uniq3 be.symm de bd.symm ef.symm af.symm
  have hig : C 8 = C 6 := uniq3 ch.symm hi.symm ci.symm gh ag.symm
  have h95 : C 9 ≠ C 5 := by rw [← hdf]; exact dj.symm
  have h96 : C 9 ≠ C 6 := by rw [← hig]; exact ij.symm
  exact none3 fg ag.symm af.symm h95 h96 hj

theorem G2_le (k : Fin 3) : G1.map (copy2 k) ≤ G2 :=
  le_sup_of_le_left (le_iSup (fun k => G1.map (copy2 k)) k)

def hom2 (k : Fin 3) : G1 →g G2 where
  toFun := copy2 k
  map_rel' h := G2_le k (SimpleGraph.map_adj_apply.2 h)

theorem G2_tri {u v : Fin 42} (h : s(u, v) ∈ [s(3, 4), s(4, 5), s(3, 5)])
    (hne : u ≠ v) : G2.Adj u v := by
  refine (SimpleGraph.sup_adj _ _ _ _).2 (Or.inr ((SimpleGraph.fromEdgeSet_adj _).2 ⟨?_, hne⟩))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact h

theorem lemma2_color (C : G2.Coloring (Fin 3)) : ¬ (C 0 = C 1 ∧ C 1 = C 2) := by
  rintro ⟨h01, h12⟩
  have c0 : ¬ (C 3 = C 0 ∧ C 0 = C 1) := lemma1_color (C.comp (hom2 0))
  have c1 : ¬ (C 5 = C 0 ∧ C 0 = C 2) := lemma1_color (C.comp (hom2 1))
  have c2 : ¬ (C 4 = C 1 ∧ C 1 = C 2) := lemma1_color (C.comp (hom2 2))
  have t34 := C.valid (G2_tri (u := 3) (v := 4) (by decide +kernel) (by decide))
  have t45 := C.valid (G2_tri (u := 4) (v := 5) (by decide +kernel) (by decide))
  have t35 := C.valid (G2_tri (u := 3) (v := 5) (by decide +kernel) (by decide))
  have h3 : C 3 ≠ C 0 := fun h => c0 ⟨h, h01⟩
  have h5 : C 5 ≠ C 0 := fun h => c1 ⟨h, h01.trans h12⟩
  have h4 : C 4 ≠ C 0 := fun h => c2 ⟨h.trans h01, h12⟩
  exact none3 t34 t45 t35 h3.symm h4.symm h5.symm

theorem G_le (k : Fin 4) : G2.map (copyG k) ≤ G :=
  le_sup_of_le_left (le_iSup (fun k => G2.map (copyG k)) k)

def homG (k : Fin 4) : G2 →g G where
  toFun := copyG k
  map_rel' h := G_le k (SimpleGraph.map_adj_apply.2 h)

theorem G_thick {u v : Fin 166}
    (h : s(u, v) ∈ [s(6, 4), s(4, 7), s(6, 7), s(4, 0), s(0, 1), s(1, 2), s(1, 3), s(2, 3),
      s(8, 5), s(5, 9), s(8, 9), s(5, 0)]) (hne : u ≠ v) : G.Adj u v := by
  refine (SimpleGraph.sup_adj _ _ _ _).2 (Or.inr ((SimpleGraph.fromEdgeSet_adj _).2 ⟨?_, hne⟩))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact h

theorem G_not_colorable' : ¬ G.Colorable 3 := by
  rintro ⟨C⟩
  have c0 : ¬ (C 0 = C 2 ∧ C 2 = C 6) := lemma2_color (C.comp (homG 0))
  have c1 : ¬ (C 0 = C 2 ∧ C 2 = C 7) := lemma2_color (C.comp (homG 1))
  have c2 : ¬ (C 0 = C 3 ∧ C 3 = C 8) := lemma2_color (C.comp (homG 2))
  have c3 : ¬ (C 0 = C 3 ∧ C 3 = C 9) := lemma2_color (C.comp (homG 3))
  have v : ∀ {u w : Fin 166}, G.Adj u w → C u ≠ C w := fun h => C.valid h
  have d64 := v (G_thick (u := 6) (v := 4) (by decide +kernel) (by decide))
  have d47 := v (G_thick (u := 4) (v := 7) (by decide +kernel) (by decide))
  have d67 := v (G_thick (u := 6) (v := 7) (by decide +kernel) (by decide))
  have d40 := v (G_thick (u := 4) (v := 0) (by decide +kernel) (by decide))
  have d10 := v (G_thick (u := 1) (v := 0) (by decide +kernel) (by decide))
  have d12 := v (G_thick (u := 1) (v := 2) (by decide +kernel) (by decide))
  have d13 := v (G_thick (u := 1) (v := 3) (by decide +kernel) (by decide))
  have d23 := v (G_thick (u := 2) (v := 3) (by decide +kernel) (by decide))
  have d85 := v (G_thick (u := 8) (v := 5) (by decide +kernel) (by decide))
  have d59 := v (G_thick (u := 5) (v := 9) (by decide +kernel) (by decide))
  have d89 := v (G_thick (u := 8) (v := 9) (by decide +kernel) (by decide))
  have d50 := v (G_thick (u := 5) (v := 0) (by decide +kernel) (by decide))
  rcases two3 d10 d12 d13 d23 with h | h
  · have h6 : C 6 ≠ C 0 := fun h' => c0 ⟨h, h.symm.trans h'.symm⟩
    have h7 : C 7 ≠ C 0 := fun h' => c1 ⟨h, h.symm.trans h'.symm⟩
    exact none3 d67 h7 h6 d64.symm d47 d40
  · have h8 : C 8 ≠ C 0 := fun h' => c2 ⟨h, h.symm.trans h'.symm⟩
    have h9 : C 9 ≠ C 0 := fun h' => c3 ⟨h, h.symm.trans h'.symm⟩
    exact none3 d89 h9 h8 d85.symm d59 d50

end SteinbergColorAux

open SteinbergFalse.Counterexample in
theorem solution : ¬ G.Colorable 3 := by
  exact SteinbergColorAux.G_not_colorable'
