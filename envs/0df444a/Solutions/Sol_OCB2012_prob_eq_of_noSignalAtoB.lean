-- Prove2me | solution 1 for OCB2012.prob_eq_of_noSignalAtoB
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-08T23:14:15.092851+00:00
-- url     : https://prove2.me/submissions/abb388cc-b6b0-44b1-90b3-98041f549716

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012Sol
open OCB2012

lemma prob_noSignalAtoB_formula {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2] [Fintype b1]
    [Fintype b2] [DecidableEq a2] (X : Matrix (a1 × (b1 × b2)) (a1 × (b1 × b2)) ℂ)
    (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (MB : Matrix (b1 × b2) (b1 × b2) ℂ) :
    prob (Matrix.of fun r c => if r.1.2 = c.1.2 then X (r.1.1, r.2) (c.1.1, c.2) else 0) MA MB =
      ∑ r1 : a1, ∑ r2 : b1 × b2, ∑ c1 : a1, ∑ c2 : b1 × b2,
        X (r1, r2) (c1, c2) * (ptrace₂ MA c1 r1 * MB c2 r2) := by
  simp only [prob, trace, diag, mul_apply, of_apply, ptrace₂, ite_mul, zero_mul, Finset.mul_sum,
    Finset.sum_mul, Fintype.sum_prod_type, kroneckerMap_apply, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

end OCB2012Sol

theorem solution {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2]
    [Fintype b1] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) (hW : OCB2012.IsNoSignalAtoB W) (MA MA' : Matrix (a1 × a2) (a1 × a2) ℂ)
    (MB : Matrix (b1 × b2) (b1 × b2) ℂ) (h : OCB2012.ptrace₂ MA = OCB2012.ptrace₂ MA') :
    OCB2012.prob W MA MB = OCB2012.prob W MA' MB := by
  obtain ⟨X, rfl⟩ := hW
  rw [OCB2012Sol.prob_noSignalAtoB_formula, OCB2012Sol.prob_noSignalAtoB_formula, h]
