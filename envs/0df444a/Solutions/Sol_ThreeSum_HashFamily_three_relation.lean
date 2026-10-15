-- Prove2me | solution 1 for ThreeSum.HashFamily.three_relation
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:46:04.261487+00:00
-- url     : https://prove2.me/submissions/7ac2c2b6-dfb0-4465-81e8-c2667c243983

import Definitions.Def_ThreeSum1962Source_Bundle01
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# The actual one-hot hash family

This file develops the dependence classification of the binary one-hot hash
vectors used in the local cover. Hash weights are independent field elements
at coordinate/symbol pairs. The independence statements concern this concrete
family, not an assumed random oracle.
-/

namespace ThreeSum.HashFamily

open scoped BigOperators

variable {α K : Type*}




theorem exists_coordinate_ne {s t : α → Bool} (hst : s ≠ t) :
    ∃ i, s i ≠ t i := by
  classical
  by_contra h
  push Not at h
  exact hst (funext h)

section Relations

variable [Ring K]

/-- Two distinct one-hot words have no nontrivial linear relation. -/
theorem two_relation {s t : α → Bool} (hst : s ≠ t) {a b : K}
    (h : ∀ p, a * oneHot s p + b * oneHot t p = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne hst
  have ha := h (i, s i)
  have hb := h (i, t i)
  simpa [oneHot, hi, Ne.symm hi] using And.intro ha hb

/-- Any three pairwise distinct binary one-hot words are independent.
At a coordinate separating the first two words, the third agrees with one
of them, leaving one coefficient isolated. -/
theorem three_relation_sourceProof {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) {a b c : K}
    (h : ∀ p, a * oneHot s p + b * oneHot t p + c * oneHot u p = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne hst
  have hu : u i = s i ∨ u i = t i := by
    cases hs : s i <;> cases ht : t i <;> cases hu : u i <;> simp_all
  rcases hu with hu | hu
  · have hb : b = 0 := by
      simpa [oneHot, hi, Ne.symm hi, hu] using h (i, t i)
    have hac : a = 0 ∧ c = 0 := two_relation hsu fun p => by simpa [hb] using h p
    exact ⟨hac.1, hb, hac.2⟩
  · have ha : a = 0 := by
      simpa [oneHot, hi, Ne.symm hi, hu] using h (i, s i)
    have hbc : b = 0 ∧ c = 0 := two_relation htu fun p => by simpa [ha] using h p
    exact ⟨ha, hbc.1, hbc.2⟩































end Relations

section LinearIndependence

variable [Field K]

































end LinearIndependence

section UniformFibers

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [Field K]































































end UniformFibers

section ActualHashes

variable {ι : Type*} [Fintype α] [Field K]
















end ActualHashes

section WordEvents

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]












































































































































end WordEvents

section IncidenceCounting

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]

























































end IncidenceCounting

section GraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]






















































































































































end GraphMoments

section SeparableTrimming

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]





















































































































































end SeparableTrimming

section TrimmedGraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
































end TrimmedGraphMoments

end ThreeSum.HashFamily

end

universe u_1 u_2

theorem solution : ∀ {α : Type u_1} {K : Type u_2} [inst : Ring.{u_2} K] {s t u : α → Bool},
  @Ne.{u_1 + 1} (α → Bool) s t →
    @Ne.{u_1 + 1} (α → Bool) s u →
      @Ne.{u_1 + 1} (α → Bool) t u →
        ∀ {a b c : K},
          (∀ (p : Prod.{u_1, 0} α Bool),
              @Eq.{u_2 + 1} K
                (@HAdd.hAdd.{u_2, u_2, u_2} K K K
                  (@instHAdd.{u_2} K
                    (@Distrib.toAdd.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
                  (@HAdd.hAdd.{u_2, u_2, u_2} K K K
                    (@instHAdd.{u_2} K
                      (@Distrib.toAdd.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
                    (@HMul.hMul.{u_2, u_2, u_2} K K K
                      (@instHMul.{u_2} K
                        (@Distrib.toMul.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
                      a
                      (@ThreeSum.HashFamily.oneHot.{u_1, u_2} α K
                        (@MulZeroClass.toZero.{u_2} K
                          (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))
                        (@AddMonoidWithOne.toOne.{u_2} K
                          (@AddGroupWithOne.toAddMonoidWithOne.{u_2} K (@Ring.toAddGroupWithOne.{u_2} K inst)))
                        s p))
                    (@HMul.hMul.{u_2, u_2, u_2} K K K
                      (@instHMul.{u_2} K
                        (@Distrib.toMul.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
                      b
                      (@ThreeSum.HashFamily.oneHot.{u_1, u_2} α K
                        (@MulZeroClass.toZero.{u_2} K
                          (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))
                        (@AddMonoidWithOne.toOne.{u_2} K
                          (@AddGroupWithOne.toAddMonoidWithOne.{u_2} K (@Ring.toAddGroupWithOne.{u_2} K inst)))
                        t p)))
                  (@HMul.hMul.{u_2, u_2, u_2} K K K
                    (@instHMul.{u_2} K
                      (@Distrib.toMul.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
                    c
                    (@ThreeSum.HashFamily.oneHot.{u_1, u_2} α K
                      (@MulZeroClass.toZero.{u_2} K
                        (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))
                      (@AddMonoidWithOne.toOne.{u_2} K
                        (@AddGroupWithOne.toAddMonoidWithOne.{u_2} K (@Ring.toAddGroupWithOne.{u_2} K inst)))
                      u p)))
                (@OfNat.ofNat.{u_2} K (nat_lit 0)
                  (@Zero.toOfNat0.{u_2} K
                    (@MulZeroClass.toZero.{u_2} K
                      (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))))) →
            And
              (@Eq.{u_2 + 1} K a
                (@OfNat.ofNat.{u_2} K (nat_lit 0)
                  (@Zero.toOfNat0.{u_2} K
                    (@MulZeroClass.toZero.{u_2} K
                      (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))))
              (And
                (@Eq.{u_2 + 1} K b
                  (@OfNat.ofNat.{u_2} K (nat_lit 0)
                    (@Zero.toOfNat0.{u_2} K
                      (@MulZeroClass.toZero.{u_2} K
                        (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))))
                (@Eq.{u_2 + 1} K c
                  (@OfNat.ofNat.{u_2} K (nat_lit 0)
                    (@Zero.toOfNat0.{u_2} K
                      (@MulZeroClass.toZero.{u_2} K
                        (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))))) := by
  exact @ThreeSum.HashFamily.three_relation_sourceProof

#print axioms solution
