-- Prove2me | solution 1 for TranscendenceTheory.guarded_root_avoidance_bezout
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-19T21:55:12.149671+00:00
-- url     : https://prove2.me/submissions/4c3c9c36-0b8d-4956-9f2b-0309e5862c37

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.Ring

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K]
    (f g h : Polynomial K) (hf : f.natDegree ≠ 0) :
    (∀ z ∈ f.roots, g.eval z = 0 → h.eval z ≠ 0) ↔
      ∃ a b c : Polynomial K,
        a * f + b * g + c * h = 1 ∧
        b.natDegree < f.natDegree ∧ c.natDegree < f.natDegree ∧
        a.natDegree ≤ max g.natDegree h.natDegree := by
  classical
  have hf0 : f ≠ 0 := by
    intro hzero
    exact hf (by simp [hzero])
  constructor
  · intro havoid
    have hcop : IsCoprime (EuclideanDomain.gcd f g) h := by
      apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K _ _).mpr
      intro z
      by_cases hz : (EuclideanDomain.gcd f g).eval z = 0
      · right
        change h.eval z ≠ 0
        have hfg : f.eval z = 0 ∧ g.eval z = 0 :=
          Polynomial.isRoot_gcd_iff_isRoot_left_right.mp hz
        exact havoid z ((Polynomial.mem_roots hf0).mpr hfg.1) hfg.2
      · left
        exact hz
    obtain ⟨u, v, huv⟩ := hcop
    let a₀ := u * EuclideanDomain.gcdA f g
    let b₀ := u * EuclideanDomain.gcdB f g
    have hbase : a₀ * f + b₀ * g + v * h = 1 := by
      rw [EuclideanDomain.gcd_eq_gcd_ab] at huv
      calc
        a₀ * f + b₀ * g + v * h =
            u * (f * EuclideanDomain.gcdA f g + g * EuclideanDomain.gcdB f g) + v * h := by
          dsimp [a₀, b₀]
          ring
        _ = 1 := huv
    let a := a₀ + (b₀ / f) * g + (v / f) * h
    let b := b₀ % f
    let c := v % f
    have hid : a * f + b * g + c * h = 1 := by
      dsimp [a, b, c]
      rw [EuclideanDomain.mod_eq_sub_mul_div, EuclideanDomain.mod_eq_sub_mul_div]
      calc
        (a₀ + b₀ / f * g + v / f * h) * f + (b₀ - f * (b₀ / f)) * g +
            (v - f * (v / f)) * h = a₀ * f + b₀ * g + v * h := by ring
        _ = 1 := hbase
    have hb : b.natDegree < f.natDegree := Polynomial.natDegree_mod_lt b₀ hf
    have hc : c.natDegree < f.natDegree := Polynomial.natDegree_mod_lt v hf
    refine ⟨a, b, c, hid, hb, hc, ?_⟩
    by_cases ha0 : a = 0
    · simp [ha0]
    have haf : a * f = 1 - (b * g + c * h) := by
      rw [← hid]
      ring
    have hbg : (b * g).natDegree ≤ f.natDegree + max g.natDegree h.natDegree :=
      Polynomial.natDegree_mul_le.trans
        (Nat.add_le_add (Nat.le_of_lt hb) (le_max_left _ _))
    have hch : (c * h).natDegree ≤ f.natDegree + max g.natDegree h.natDegree :=
      Polynomial.natDegree_mul_le.trans
        (Nat.add_le_add (Nat.le_of_lt hc) (le_max_right _ _))
    have hdeg : (a * f).natDegree ≤ f.natDegree + max g.natDegree h.natDegree := by
      rw [haf]
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · simp
      · exact (Polynomial.natDegree_add_le _ _).trans (max_le hbg hch)
    rw [Polynomial.natDegree_mul ha0 hf0] at hdeg
    exact Nat.le_of_add_le_add_right (by simpa only [Nat.add_comm f.natDegree] using hdeg)
  · rintro ⟨a, b, c, hid, _, _, _⟩ z hz hgz hhz
    have hfz := (Polynomial.mem_roots hf0).mp hz
    change f.eval z = 0 at hfz
    have hev := congrArg (Polynomial.eval z) hid
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      hfz, hgz, hhz, mul_zero, zero_add] at hev
    exact zero_ne_one hev
