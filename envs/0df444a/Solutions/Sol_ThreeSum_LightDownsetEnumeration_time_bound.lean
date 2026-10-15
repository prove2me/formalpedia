-- Prove2me | solution 1 for ThreeSum.LightDownsetEnumeration.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:50:03.012907+00:00
-- url     : https://prove2.me/submissions/c85528f4-29a3-49b9-a5b3-ad58bd45cb79

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
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
# Sequential enumeration of a compact downset

This routine invokes the guarded layer enumerator for the successive
cardinalities. Each layer starts immediately after the preceding layer;
the only traversal besides the emitted masks is polynomial in the bit
width. All power-table reads are shared across the layer calls.
-/

namespace ThreeSum.LightDownsetEnumeration

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}
































































































































theorem time_bound_sourceProof {L cut : ℕ} (hcut : cut ≤ L) :
    time L cut ≤ 1000*(L+1)^2*(downsetCap L cut+1) := by
  have hb : budget L cut+70 ≤ 800*(L+1)*(downsetCap L cut+1) := by
    unfold budget
    nlinarith
  have hm := Nat.mul_le_mul_left (cut+1) hb
  have hc := Nat.mul_le_mul_right (800*(L+1)*(downsetCap L cut+1))
    (Nat.succ_le_succ hcut)
  have hp : 1 ≤ (L+1)^2*(downsetCap L cut+1) :=
    Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by omega)) (by omega))
  unfold time
  calc
    _ ≤ (L+1)*(800*(L+1)*(downsetCap L cut+1))+40 := Nat.add_le_add_right (hm.trans hc) 40
    _ = 800*((L+1)^2*(downsetCap L cut+1))+40 := by ring
    _ ≤ 1000*((L+1)^2*(downsetCap L cut+1)) := by omega
    _ = _ := by ring















end ThreeSum.LightDownsetEnumeration

end


theorem solution : ∀ {L cut : Nat},
  @LE.le.{0} Nat instLENat cut L →
    @LE.le.{0} Nat instLENat (ThreeSum.LightDownsetEnumeration.time L cut)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.SubsetAddress.downsetCap L cut)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @ThreeSum.LightDownsetEnumeration.time_bound_sourceProof

#print axioms solution
