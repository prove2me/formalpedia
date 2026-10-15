-- Prove2me | solution 1 for ThreeSum.HashFamily.raw_second_moment_five
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:06:22.842985+00:00
-- url     : https://prove2.me/submissions/24d5ec23-4faf-4a99-ba60-387453d81ebf

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
import Theorems.Thm_ThreeSum_HashFamily_raw_second_moment


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


























































































































/-- The paper's coarse `5 lambda` raw second-moment bound follows from
explicit graph-size and exceptional-partner inequalities. -/
theorem raw_second_moment_five_sourceProof (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f)
    (B : ℕ) (hB : ∀ e, (badPartners left right e).card ≤ B)
    (hBp : B ≤ 3 * Fintype.card K) (hEp : Fintype.card E ≤ Fintype.card K ^ 2)
    (a b : K) :
    Fintype.card K ^ 2 *
        (∑ w, incidenceCount (fun e => pairEvent (left e) (right e) a b) w ^ 2) ≤
      5 * Fintype.card E * Fintype.card (α × Bool → K) := by
  have hp : 0 < Fintype.card K ^ 2 := pow_pos Fintype.card_pos _
  have hs := raw_second_moment left right hinj hcross B hB a b
  have hE : Fintype.card E ^ 2 ≤ Fintype.card E * Fintype.card K ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_left (Fintype.card E) hEp
  have hBB : Fintype.card E * B * Fintype.card K ≤
      3 * Fintype.card E * Fintype.card K ^ 2 := by
    have h := Nat.mul_le_mul_right (Fintype.card K)
      (Nat.mul_le_mul_left (Fintype.card E) hBp)
    convert h using 1 <;> ring
  have hs' : Fintype.card K ^ 4 *
      (∑ w, incidenceCount (fun e => pairEvent (left e) (right e) a b) w ^ 2) ≤
        Fintype.card (α × Bool → K) * (5 * Fintype.card E * Fintype.card K ^ 2) := by
    refine hs.trans (Nat.mul_le_mul_left _ ?_)
    nlinarith only [hE, hBB]
  apply Nat.le_of_mul_le_mul_left (c := Fintype.card K ^ 2) ?_ hp
  convert hs' using 1 <;> ring

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

universe u_1 u_2 u_3

theorem solution : ∀ {α : Type u_1} {K : Type u_2} {E : Type u_3} [inst : Fintype.{u_3} E] [DecidableEq.{u_3 + 1} E]
  [inst_2 : Fintype.{u_1} α] [inst_3 : DecidableEq.{u_1 + 1} α] [inst_4 : Field.{u_2} K] [inst_5 : Fintype.{u_2} K]
  [inst_6 : DecidableEq.{u_2 + 1} K] (left right : E → α → Bool),
  (@Function.Injective.{u_3 + 1, u_1 + 1} E (Prod.{u_1, u_1} (α → Bool) (α → Bool)) fun (e : E) =>
      @Prod.mk.{u_1, u_1} (α → Bool) (α → Bool) (left e) (right e)) →
    (∀ (e f : E), @Ne.{u_1 + 1} (α → Bool) (left e) (right f)) →
      ∀ (B : Nat),
        (∀ (e : E),
            @LE.le.{0} Nat instLENat
              (@Finset.card.{u_3} E (@ThreeSum.HashFamily.badPartners.{u_1, u_3} α E inst inst_2 left right e)) B) →
          @LE.le.{0} Nat instLENat B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fintype.card.{u_2} K inst_5)) →
            @LE.le.{0} Nat instLENat (@Fintype.card.{u_3} E inst)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@Fintype.card.{u_2} K inst_5) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
              ∀ (a b : K),
                @LE.le.{0} Nat instLENat
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@Fintype.card.{u_2} K inst_5) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (∑ w : Prod.{u_1, 0} α Bool → K,
                      @HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                        (@ThreeSum.HashFamily.incidenceCount.{max u_2 u_1, u_3} (Prod.{u_1, 0} α Bool → K) E inst
                          (fun (a b : Prod.{u_1, 0} α Bool → K) =>
                            @Fintype.decidablePiFintype.{u_2, u_1} (Prod.{u_1, 0} α Bool)
                              (fun (a : Prod.{u_1, 0} α Bool) => K) (fun (a : Prod.{u_1, 0} α Bool) => inst_6)
                              (@instFintypeProd.{u_1, 0} α Bool inst_2 Bool.fintype) a b)
                          (fun (e : E) =>
                            @ThreeSum.HashFamily.pairEvent.{u_1, u_2} α K inst_2 inst_3 inst_4 inst_5 inst_6 (left e)
                              (right e) a b)
                          w)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (@Fintype.card.{u_3} E inst))
                    (@Fintype.card.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
                      (@Pi.instFintype.{u_1, u_2} (Prod.{u_1, 0} α Bool) (fun (a : Prod.{u_1, 0} α Bool) => K)
                        (fun (a b : Prod.{u_1, 0} α Bool) =>
                          @instDecidableEqProd.{u_1, 0} α Bool inst_3 instDecidableEqBool a b)
                        (@instFintypeProd.{u_1, 0} α Bool inst_2 Bool.fintype) fun (a : Prod.{u_1, 0} α Bool) =>
                        inst_5))) := by
  exact @ThreeSum.HashFamily.raw_second_moment_five_sourceProof

#print axioms solution
