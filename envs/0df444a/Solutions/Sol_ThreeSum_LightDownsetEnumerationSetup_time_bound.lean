-- Prove2me | solution 1 for ThreeSum.LightDownsetEnumerationSetup.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:20:10.04414+00:00
-- url     : https://prove2.me/submissions/797a42b0-986d-4590-817a-72893e0a1d72

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_LightDownsetEnumeration_time_bound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# A complete fixed program for compact downset enumeration

The main routine builds one power table and enumerates every layer through
the given cutoff into adjacent output cells. Its specification names the
exact compact list and bounds actual benchmark-language execution time.
-/

namespace ThreeSum.LightDownsetEnumerationSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}
































































theorem time_bound_sourceProof {L cut : ℕ} (hcut : cut ≤ L) :
    time L cut ≤ 1200*(L+1)^2*(downsetCap L cut+1) := by
  have h := LightDownsetEnumeration.time_bound hcut
  have hL : L+1 ≤ (L+1)^2*(downsetCap L cut+1) := by
    have hs : L+1 ≤ (L+1)^2 := by
      calc
        L+1 ≤ (L+1)*(L+1) := Nat.le_mul_of_pos_left _ (by omega)
        _ = (L+1)^2 := (pow_two _).symm
    exact hs.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hp : 1 ≤ (L+1)^2*(downsetCap L cut+1) := by omega
  unfold time powTableTime
  have ht : LightDownsetEnumeration.time L cut ≤
      1000*((L+1)^2*(downsetCap L cut+1)) := by simpa only [Nat.mul_assoc] using h
  calc
    _ ≤ 1200*((L+1)^2*(downsetCap L cut+1)) := by omega
    _ = _ := by ring

end ThreeSum.LightDownsetEnumerationSetup

end


theorem solution : ∀ {L cut : Nat},
  @LE.le.{0} Nat instLENat cut L →
    @LE.le.{0} Nat instLENat (ThreeSum.LightDownsetEnumerationSetup.time L cut)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 1200) (instOfNatNat (nat_lit 1200)))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.SubsetAddress.downsetCap L cut)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @ThreeSum.LightDownsetEnumerationSetup.time_bound_sourceProof

#print axioms solution
