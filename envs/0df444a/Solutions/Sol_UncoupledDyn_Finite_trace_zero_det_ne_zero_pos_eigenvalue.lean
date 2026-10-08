-- Prove2me | solution 1 for UncoupledDyn.Finite.trace_zero_det_ne_zero_pos_eigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:29:51.48627+00:00
-- url     : https://prove2.me/submissions/edd5b152-d2c2-4a83-a68d-1824b1c3556b

import Mathlib



theorem solution (M : Matrix (Fin 3) (Fin 3) ℝ)
    (htr : M.trace = 0) (hdet : M.det ≠ 0) :
    ∃ z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)), 0 < z.re := by
  classical
  let A := M.map (algebraMap ℝ ℂ)
  have hcard : A.charpoly.roots.card = 3 := by
    have hh := Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits A.charpoly)
    simpa [Matrix.charpoly_natDegree_eq_dim] using hh
  obtain ⟨u, v, w, hr⟩ := Multiset.card_eq_three.1 hcard
  have hs : u + v + w = 0 := by
    have ht := Matrix.trace_eq_sum_roots_charpoly A
    have htrace : A.trace = 0 := by
      change (∑ i, (algebraMap ℝ ℂ) (M i i)) = 0
      rw [← map_sum]
      exact congrArg (algebraMap ℝ ℂ) htr
    rw [htrace, hr] at ht
    simpa [add_assoc] using ht.symm
  have hd : (M.det : ℂ) = u * v * w := by
    have hh := Matrix.det_eq_prod_roots_charpoly A
    rw [hr] at hh
    change (M.map (algebraMap ℝ ℂ)).det = _ at hh
    have hmap := (algebraMap ℝ ℂ).map_det M
    change (M.det : ℂ) = (M.map (algebraMap ℝ ℂ)).det at hmap
    exact hmap.trans (by simpa [mul_assoc] using hh)
  have hmem (z : ℂ) (hz : z ∈ ({u,v,w} : Multiset ℂ)) :
      z ∈ spectrum ℂ A := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.2
    exact (Polynomial.mem_roots A.charpoly_monic.ne_zero).1 (hr ▸ hz)
  by_contra h
  have hn (z : ℂ) (hz : z ∈ ({u,v,w} : Multiset ℂ)) : z.re ≤ 0 := by
    by_contra hh
    exact h ⟨z, hmem z hz, lt_of_not_ge hh⟩
  have hu := hn u (by simp)
  have hv := hn v (by simp)
  have hw := hn w (by simp)
  have hsre := congrArg Complex.re hs
  simp only [Complex.add_re, Complex.zero_re] at hsre
  have hu0 : u.re = 0 := by linarith
  have hv0 : v.re = 0 := by linarith
  have hw0 : w.re = 0 := by linarith
  have hdre := congrArg Complex.re hd
  simp [Complex.mul_re, Complex.mul_im, hu0, hv0, hw0] at hdre
  exact hdet hdre




#print axioms solution
