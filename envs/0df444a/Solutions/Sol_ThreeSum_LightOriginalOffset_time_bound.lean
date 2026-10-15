-- Prove2me | solution 1 for ThreeSum.LightOriginalOffset.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:51:25.304068+00:00
-- url     : https://prove2.me/submissions/1a1178e8-426a-4d02-b806-d102b90f5a78

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
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
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues

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
# An actual minimum scan of the fast cyclic correlation

The returned offset obeys the exact mean bound for the supplied histograms.
The choice is made by a fixed program, not by an existential witness in the
proof. The histograms themselves are the procedure's array inputs.
-/

namespace ThreeSum.LightBalancedOffset

open Light Karatsuba CyclicFold LightKaratsuba Finset
open scoped BigOperators



























variable {lim : Limits} {P : Program} {d : ℕ}




























































theorem time_bound (k p : ℕ) (hp : p ≤ 2^k) :
    time k p ≤ LightKaratsuba.time k + 226*2^k + 226 := by
  unfold time LightCyclic.combinedTime LightMinimum.time LightArray.linearTime
  omega






end ThreeSum.LightBalancedOffset

end

section


/-!
# Original integers to a padded signed histogram

The executable procedure first computes canonical residues of the signed
original integers and then fills the entire requested histogram capacity.
Its postcondition is the precise padded polynomial vector consumed by the
verified cyclic-convolution routine. Repeated input values remain distinct
incidences and contribute their full multiplicity.
-/

namespace ThreeSum.LightResidueHistogram

open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba

variable {lim : Limits} {P : Program} {d : ℕ}



























































































































































theorem time_bound (n cap U : ℕ) :
    time n cap U ≤ 13 * cap + 131 * n * (Nat.log 2 (U + 1) + 1) + 53 := by
  unfold time residuesTime residueBudget histogramTime countTime
  simp only [fillTime]
  nlinarith

end ThreeSum.LightResidueHistogram

end

section


/-!
# An actual common offset from two original signed key arrays

The fixed program builds both padded histograms, including reversal, from
the supplied integer keys. It computes its own power-of-two capacity and
chooses the least correlation minimum with the checked fast multiplication.
Repeated keys count separately. No histogram or capacity table is supplied.
-/

namespace ThreeSum.LightOriginalOffset

open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000




































































variable {lim : Limits} {P : Program} {d : ℕ}























































































































theorem time_bound_sourceProof (p nLeft nRight U : ℕ) :
    time p nLeft nRight U ≤ LightKaratsuba.time (Nat.clog 2 p)+252*capacity p+
      131*(nLeft+nRight)*(Nat.log 2 (U+1)+1)+12*Nat.clog 2 p+642 := by
  have hL := LightResidueHistogram.time_bound nLeft (capacity p) U
  have hR := LightResidueHistogram.time_bound nRight (capacity p) U
  have hM := LightBalancedOffset.time_bound (Nat.clog 2 p) p (le_capacity p)
  change LightBalancedOffset.time (Nat.clog 2 p) p ≤
    LightKaratsuba.time (Nat.clog 2 p)+226*capacity p+226 at hM
  calc
    time p nLeft nRight U ≤ LightCapacity.time p+
        (13*capacity p+131*nLeft*(Nat.log 2 (U+1)+1)+53)+
        (13*capacity p+131*nRight*(Nat.log 2 (U+1)+1)+53)+
        (LightKaratsuba.time (Nat.clog 2 p)+226*capacity p+226)+300 := by
      unfold time
      omega
    _ = _ := by unfold LightCapacity.time; ring

end ThreeSum.LightOriginalOffset

end


theorem solution : ∀ (p nLeft nRight U : Nat),
  @LE.le.{0} Nat instLENat (ThreeSum.LightOriginalOffset.time p nLeft nRight U)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (ThreeSum.LightKaratsuba.time (Nat.clog (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) p))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 252) (instOfNatNat (nat_lit 252)))
              (ThreeSum.KaratsubaInterface.capacity p)))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 131) (instOfNatNat (nat_lit 131)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) nLeft nRight))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (Nat.log (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) U
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
          (Nat.clog (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) p)))
      (@OfNat.ofNat.{0} Nat (nat_lit 642) (instOfNatNat (nat_lit 642)))) := by
  exact @ThreeSum.LightOriginalOffset.time_bound_sourceProof

#print axioms solution
