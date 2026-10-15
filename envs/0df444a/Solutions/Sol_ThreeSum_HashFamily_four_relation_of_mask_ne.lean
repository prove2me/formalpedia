-- Prove2me | solution 1 for ThreeSum.HashFamily.four_relation_of_mask_ne
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:12:38.570362+00:00
-- url     : https://prove2.me/submissions/fb238753-8fc5-4085-88f2-fea0d3cd12fe

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
import Theorems.Thm_ThreeSum_HashFamily_three_relation


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











section Relations

variable [Ring K]





























/-- If the equality masks of two edges differ, one coordinate has a 3+1
pattern among their four endpoint words. With four distinct endpoints this
forces full independence. The only possible no-shared-endpoint dependence
therefore has an identical output equality mask. -/
theorem four_relation_of_mask_ne_sourceProof {s t u v : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hm : ∃ i, (s i == t i) ≠ (u i == v i)) {a b c d : K}
    (h : ∀ p, a * oneHot s p + b * oneHot t p + c * oneHot u p + d * oneHot v p = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hz : a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0 := by
    obtain ⟨i, hi⟩ := hm
    have hf := h (i, false)
    have ht := h (i, true)
    cases hs : s i <;> cases hti : t i <;> cases hu : u i <;> cases hv : v i <;>
      simp_all [oneHot]
  rcases hz with ha | hb | hc | hd
  · have hr := three_relation htu htv huv (a := b) (b := c) (c := d)
      (fun p => by simpa [ha] using h p)
    exact ⟨ha, hr.1, hr.2.1, hr.2.2⟩
  · have hr := three_relation hsu hsv huv (a := a) (b := c) (c := d)
      (fun p => by simpa [hb] using h p)
    exact ⟨hr.1, hb, hr.2.1, hr.2.2⟩
  · have hr := three_relation hst hsv htv (a := a) (b := b) (c := d)
      (fun p => by simpa [hc] using h p)
    exact ⟨hr.1, hr.2.1, hc, hr.2.2⟩
  · have hr := three_relation hst hsu htu (a := a) (b := b) (c := c)
      (fun p => by simpa [hd] using h p)
    exact ⟨hr.1, hr.2.1, hr.2.2, hd⟩

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

theorem solution : ∀ {α : Type u_1} {K : Type u_2} [inst : Ring.{u_2} K] {s t u v : α → Bool},
  @Ne.{u_1 + 1} (α → Bool) s t →
    @Ne.{u_1 + 1} (α → Bool) s u →
      @Ne.{u_1 + 1} (α → Bool) s v →
        @Ne.{u_1 + 1} (α → Bool) t u →
          @Ne.{u_1 + 1} (α → Bool) t v →
            @Ne.{u_1 + 1} (α → Bool) u v →
              (∃ (i : α),
                  @Ne.{1} Bool (@BEq.beq.{0} Bool (@instBEqOfDecidableEq.{0} Bool instDecidableEqBool) (s i) (t i))
                    (@BEq.beq.{0} Bool (@instBEqOfDecidableEq.{0} Bool instDecidableEqBool) (u i) (v i))) →
                ∀ {a b c d : K},
                  (∀ (p : Prod.{u_1, 0} α Bool),
                      @Eq.{u_2 + 1} K
                        (@HAdd.hAdd.{u_2, u_2, u_2} K K K
                          (@instHAdd.{u_2} K
                            (@Distrib.toAdd.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
                          (@HAdd.hAdd.{u_2, u_2, u_2} K K K
                            (@instHAdd.{u_2} K
                              (@Distrib.toAdd.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
                            (@HAdd.hAdd.{u_2, u_2, u_2} K K K
                              (@instHAdd.{u_2} K
                                (@Distrib.toAdd.{u_2} K
                                  (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
                              (@HMul.hMul.{u_2, u_2, u_2} K K K
                                (@instHMul.{u_2} K
                                  (@Distrib.toMul.{u_2} K
                                    (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
                                a
                                (@ThreeSum.HashFamily.oneHot.{u_1, u_2} α K
                                  (@MulZeroClass.toZero.{u_2} K
                                    (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))
                                  (@AddMonoidWithOne.toOne.{u_2} K
                                    (@AddGroupWithOne.toAddMonoidWithOne.{u_2} K
                                      (@Ring.toAddGroupWithOne.{u_2} K inst)))
                                  s p))
                              (@HMul.hMul.{u_2, u_2, u_2} K K K
                                (@instHMul.{u_2} K
                                  (@Distrib.toMul.{u_2} K
                                    (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
                                b
                                (@ThreeSum.HashFamily.oneHot.{u_1, u_2} α K
                                  (@MulZeroClass.toZero.{u_2} K
                                    (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))
                                  (@AddMonoidWithOne.toOne.{u_2} K
                                    (@AddGroupWithOne.toAddMonoidWithOne.{u_2} K
                                      (@Ring.toAddGroupWithOne.{u_2} K inst)))
                                  t p)))
                            (@HMul.hMul.{u_2, u_2, u_2} K K K
                              (@instHMul.{u_2} K
                                (@Distrib.toMul.{u_2} K
                                  (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
                              c
                              (@ThreeSum.HashFamily.oneHot.{u_1, u_2} α K
                                (@MulZeroClass.toZero.{u_2} K
                                  (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))
                                (@AddMonoidWithOne.toOne.{u_2} K
                                  (@AddGroupWithOne.toAddMonoidWithOne.{u_2} K (@Ring.toAddGroupWithOne.{u_2} K inst)))
                                u p)))
                          (@HMul.hMul.{u_2, u_2, u_2} K K K
                            (@instHMul.{u_2} K
                              (@Distrib.toMul.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
                            d
                            (@ThreeSum.HashFamily.oneHot.{u_1, u_2} α K
                              (@MulZeroClass.toZero.{u_2} K
                                (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))
                              (@AddMonoidWithOne.toOne.{u_2} K
                                (@AddGroupWithOne.toAddMonoidWithOne.{u_2} K (@Ring.toAddGroupWithOne.{u_2} K inst)))
                              v p)))
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
                        (And
                          (@Eq.{u_2 + 1} K c
                            (@OfNat.ofNat.{u_2} K (nat_lit 0)
                              (@Zero.toOfNat0.{u_2} K
                                (@MulZeroClass.toZero.{u_2} K
                                  (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))))
                          (@Eq.{u_2 + 1} K d
                            (@OfNat.ofNat.{u_2} K (nat_lit 0)
                              (@Zero.toOfNat0.{u_2} K
                                (@MulZeroClass.toZero.{u_2} K
                                  (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))))))) := by
  exact @ThreeSum.HashFamily.four_relation_of_mask_ne_sourceProof

#print axioms solution
