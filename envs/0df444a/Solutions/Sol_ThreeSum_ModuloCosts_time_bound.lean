-- Prove2me | solution 1 for ThreeSum.ModuloCosts.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:37:57.81399+00:00
-- url     : https://prove2.me/submissions/6821777b-c3ea-4886-aa4c-b896f74ca5d0

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba

section


/-!
# Karatsuba as a fixed program in the benchmark language

The procedure below is a finite `Light.Stmt`, independent of the input
capacity. Recursive products share an eight-capacity scratch area. The
linear-time `half` routine avoids an additional persistent power table.
-/

namespace ThreeSum.LightKaratsuba

open Light
open ThreeSum.Karatsuba
open Polynomial























































theorem time_bound (k : ℕ) : time k + 2500 * 2 ^ k ≤ 2530 * 3 ^ k := by
  induction k with
  | zero => norm_num [time]
  | succ k ih =>
    simp only [time, pow_succ]
    nlinarith

theorem time_le (k : ℕ) : time k ≤ 2530 * 3 ^ k :=
  (Nat.le_add_right _ _).trans (time_bound k)

























































section Join

variable {lim : Limits} {P : Program} {d pLinear pFill : ℕ}




































































































































end Join

section BaseCase

variable {lim : Limits} {P : Program} {d : ℕ}






































end BaseCase

















































































































section RecursiveExecution

variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}











































































































































end RecursiveExecution

section CompleteProcedure

variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}




















































































end CompleteProcedure

end ThreeSum.LightKaratsuba

end

section


/-!
# Arbitrary-length interface for the verified multiplication routine

These exact inequalities convert a requested positive coefficient length
to its power-of-two capacity. Polynomial padding preserves the represented
product. The fifth-power bounds include any fixed linear preparation and
folding overhead, so no real-exponent oracle is needed for the time bound.
-/

namespace ThreeSum.KaratsubaInterface

open ThreeSum.Karatsuba ThreeSum.LightKaratsuba Polynomial



theorem le_capacity (p : ℕ) : p ≤ capacity p := Nat.le_pow_clog (by decide) p























































































end ThreeSum.KaratsubaInterface

end

section


/-!
# Finite arithmetic-operation bounds for the complete counting backend

The only input-size dependence outside the Karatsuba term is the number of
original elements times their remainder bit budget. Histogram initialization,
capacity computation and folding are included in the displayed constant.
-/

namespace ThreeSum.ModuloCosts

open KaratsubaInterface



theorem capacity_le_roundedPower (p : ℕ) : capacity p ≤ roundedPower p :=
  Nat.pow_le_pow_left (by decide) _

theorem log_le_roundedPower (p : ℕ) : Nat.clog 2 p ≤ roundedPower p :=
  (Nat.lt_pow_self (by decide : 1 < 2)).le.trans (capacity_le_roundedPower p)

theorem time_bound_sourceProof (p nA nB nC N U : ℕ)
    (ha : nA ≤ N) (hb : nB ≤ N) (hc : nC ≤ N) :
    LightModuloCounts.time p nA nB nC U ≤
      10000 * (roundedPower p + N*(Nat.log 2 (U+1)+1) + 1) := by
  have hcap := capacity_le_roundedPower p
  have hlog := log_le_roundedPower p
  have hp := (le_capacity p).trans hcap
  have hK : LightKaratsuba.time (Nat.clog 2 p) ≤ 2530*roundedPower p :=
    LightKaratsuba.time_le _
  have hNa := Nat.mul_le_mul_right (Nat.log 2 (U+1)+1) ha
  have hNb := Nat.mul_le_mul_right (Nat.log 2 (U+1)+1) hb
  have hNc := Nat.mul_le_mul_right (Nat.log 2 (U+1)+1) hc
  unfold LightModuloCounts.time LightCapacity.time LightResidueHistogram.time
    LightHistogram.histogramTime LightHistogram.countTime LightCyclic.combinedTime
    LightArray.linearTime LightResidues.residuesTime LightResidues.residueBudget
    LightLookupSum.time
  simp only [Light.fillTime]
  nlinarith




















end ThreeSum.ModuloCosts

end


theorem solution : ∀ (p nA nB nC N U : Nat),
  @LE.le.{0} Nat instLENat nA N →
    @LE.le.{0} Nat instLENat nB N →
      @LE.le.{0} Nat instLENat nC N →
        @LE.le.{0} Nat instLENat (ThreeSum.LightModuloCounts.time p nA nB nC U)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 10000) (instOfNatNat (nat_lit 10000)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.ModuloCosts.roundedPower p)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) N
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (Nat.log (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) U
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @ThreeSum.ModuloCosts.time_bound_sourceProof

#print axioms solution
