-- Prove2me | solution 1 for ROLDescent.eq_71
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:08:21.184499+00:00
-- url     : https://prove2.me/submissions/0cabda95-624d-46d9-ab1f-786383c95c51

import Mathlib
import Definitions.Def_ROLDescent_WeightedComplex
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_ROLDescent_outProb
import Definitions.Def_ROLDescent_linkWalk

open ROLDescent

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (X : Finset (Finset V)) (d : ℕ) (w : Finset V → ℝ) (hX : WeightedComplex X d w)
    (τ : Finset V) (hτ : τ ∈ X) (hτd : τ.card + 3 ≤ d)
    (i j : V) (hi : i ∈ HDXConc.linkVerts X τ) (hj : j ∈ HDXConc.linkVerts X τ) (hij : j ≠ i) :
    linkWalk X d w τ i j = outProb X d w (insert i τ) j := by
  have hi' : i ∉ τ := (Finset.mem_filter.mp hi).2.1
  have hcard : (insert i τ).card = τ.card + 1 := Finset.card_insert_of_notMem hi'
  have hchild : remRank d (insert i τ) + 1 = remRank d τ := by
    unfold remRank
    rw [hcard]
    omega
  have hreal : (remRank d (insert i τ) : ℝ) = (remRank d τ : ℝ) - 1 := by
    exact sub_eq_of_eq_add (by exact_mod_cast hchild.symm)
      |>.symm
  simp [linkWalk, outProb, hij.symm, hreal]

#print axioms solution
