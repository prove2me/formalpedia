-- Prove2me | solution 1 for TranscendenceTheory.finite_spectrum_cleared_bezout
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T00:33:08.454703+00:00
-- url     : https://prove2.me/submissions/0d59b5d9-a4d3-490e-a739-9d557356c7c2

import Theorems.Thm_TranscendenceTheory_guarded_root_avoidance_bezout
import Theorems.Thm_TranscendenceTheory_bounded_bezout_field_descent
import Theorems.Thm_TranscendenceTheory_bounded_bezout_clear_denominators
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.BigOperators

theorem solution
    (R : Type*) [CommRing R] [IsDomain R]
    (ι : Type*) [Fintype ι] (x : ι → R)
    (f h : Polynomial R) (hf : f.natDegree ≠ 0) :
    (∀ i, h.eval (x i) = 0 → f.eval (x i) ≠ 0) ↔
      let g : Polynomial R := ∏ i, (Polynomial.X - Polynomial.C (x i))
      ∃ d : R, d ≠ 0 ∧ ∃ u v w : Polynomial R,
        u * f + v * g + w * h = Polynomial.C d ∧
        v.natDegree < f.natDegree ∧ w.natDegree < f.natDegree ∧
        u.natDegree ≤ max g.natDegree h.natDegree := by
  classical
  let g : Polynomial R := ∏ i, (Polynomial.X - Polynomial.C (x i))
  have hg (i : ι) : g.eval (x i) = 0 := by
    simp only [g, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (x i))
  constructor
  · intro hvalues
    let K := FractionRing R
    let L := AlgebraicClosure K
    let j : R →+* L := (algebraMap K L).comp (algebraMap R K)
    have hj : Function.Injective j :=
      (algebraMap K L).injective.comp (IsFractionRing.injective R K)
    have hdeg (p : Polynomial R) : (p.map j).natDegree = p.natDegree :=
      Polynomial.natDegree_map_eq_of_injective hj p
    have hf0 : f.map j ≠ 0 := by
      intro hz
      exact hf (by rw [← hdeg f, hz, Polynomial.natDegree_zero])
    have havoid : ∀ z ∈ (f.map j).roots,
        (g.map j).eval z = 0 → (h.map j).eval z ≠ 0 := by
      intro z hz hgz hhz
      have hex : ∃ i : ι, z = j (x i) := by
        simp only [g, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
          Polynomial.map_C, Polynomial.eval_prod, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C] at hgz
        obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hgz
        exact ⟨i, sub_eq_zero.mp hi⟩
      obtain ⟨i, rfl⟩ := hex
      have hhi : h.eval (x i) = 0 := by
        apply hj
        simpa only [Polynomial.eval_map_apply, map_zero] using hhz
      apply hvalues i hhi
      apply hj
      have hfi := (Polynomial.mem_roots hf0).mp hz
      simpa only [Polynomial.IsRoot, Polynomial.eval_map_apply, map_zero] using hfi
    have hcertificate := (TranscendenceTheory.guarded_root_avoidance_bezout
      L (f.map j) (g.map j) (h.map j) (by simpa only [hdeg] using hf)).mp havoid
    apply (TranscendenceTheory.bounded_bezout_clear_denominators R K f g h
      (max g.natDegree h.natDegree) f.natDegree f.natDegree).mp
    apply (TranscendenceTheory.bounded_bezout_field_descent K L
      (f.map (algebraMap R K)) (g.map (algebraMap R K)) (h.map (algebraMap R K))
      (max g.natDegree h.natDegree) f.natDegree f.natDegree).mp
    simpa only [Polynomial.map_map, hdeg] using hcertificate
  · rintro ⟨d, hd, u, v, w, hid, _, _, _⟩ i hhi hfi
    change u * f + v * g + w * h = Polynomial.C d at hid
    have hev := congrArg (Polynomial.eval (x i)) hid
    apply hd
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      hfi, hg, hhi, mul_zero, zero_add] using hev.symm
