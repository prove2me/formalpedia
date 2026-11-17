-- Prove2me | solution 1 for XiPairingPublished.paired_canonical_product
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T10:30:04.302132+00:00
-- url     : https://prove2.me/submissions/9c17b6f1-2490-488e-9023-820422bf7ae2

import Mathlib
open scoped BigOperators

theorem paired_atom (a z : ℂ) :
    ((1-z/a)*Complex.exp (z/a))*((1-z/(-a))*Complex.exp (z/(-a))) =
      1 + z^2/(-a^2) := by
  rw [div_neg, sub_neg_eq_add]
  calc
    ((1-z/a)*Complex.exp (z/a))*((1+z/a)*Complex.exp (-(z/a))) =
        ((1-z/a)*(1+z/a)) * (Complex.exp (z/a)*Complex.exp (-(z/a))) := by ring
    _ = (1-z/a)*(1+z/a) := by rw [← Complex.exp_add]; simp
    _ = 1+z^2/(-a^2) := by ring

theorem solution {I : Type*} (a : I → ℂ) (z : ℂ)
    (hp : Multipliable (fun i => (1-z/a i)*Complex.exp (z/a i)))
    (hm : Multipliable (fun i => (1-z/(-a i))*Complex.exp (z/(-a i)))) :
    Multipliable (fun i => 1+z^2/(-(a i)^2)) ∧
    (∏' i, (1-z/a i)*Complex.exp (z/a i)) *
    (∏' i, (1-z/(-a i))*Complex.exp (z/(-a i))) =
      ∏' i, (1+z^2/(-(a i)^2)) := by
  have hfun : (fun i => ((1-z/a i)*Complex.exp (z/a i))*
      ((1-z/(-a i))*Complex.exp (z/(-a i)))) =
      (fun i => 1+z^2/(-(a i)^2)) := funext (fun i => paired_atom (a i) z)
  constructor
  · rw [← hfun]
    exact hp.mul hm
  · rw [← hp.tprod_mul hm]
    exact tprod_congr (fun i => paired_atom (a i) z)
#print axioms solution
