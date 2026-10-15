-- Prove2me | solution 1 for ThreeSum.LightZetaPass.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:49:04.433004+00:00
-- url     : https://prove2.me/submissions/6fe0d488-ead6-4833-8040-a2173464c03b

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
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
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# A complete coordinate pass over a compact downset

For each stored cardinality the fixed procedure constructs its layer of
masks, then runs the compact-cell update on that layer. Only the compact
downset and polynomial workspace are allocated; the program never visits
all integers below `2^L`. The source table remains unchanged throughout
the pass.
-/

namespace ThreeSum.LightZetaPass

open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}
































































































































































theorem time_bound_sourceProof {L cut : ℕ} (hcut : cut ≤ L) :
    time L cut ≤ 4000*(L+1)^3*(downsetCap L cut+1) := by
  have hp : 1 ≤ (L+1)^2*(downsetCap L cut+1) := by
    have hh : 0 < (L+1)^2*(downsetCap L cut+1) := by positivity
    omega
  have hlin : L+1 ≤ (L+1)^2 := by nlinarith
  have hsmall := Nat.mul_le_mul_right (downsetCap L cut+1) hlin
  have hb : roundBudget L cut+20 ≤ 3000*((L+1)^2*(downsetCap L cut+1)) := by
    unfold roundBudget enumBudget batchBudget
    nlinarith
  have hm := Nat.mul_le_mul_left (cut+1) hb
  have hc := Nat.mul_le_mul_right (3000*((L+1)^2*(downsetCap L cut+1)))
    (Nat.succ_le_succ hcut)
  have hp₃ : 1 ≤ (L+1)^3*(downsetCap L cut+1) := by
    have hh : 0 < (L+1)^3*(downsetCap L cut+1) := by positivity
    omega
  unfold time
  calc
    _ ≤ (L+1)*(3000*((L+1)^2*(downsetCap L cut+1)))+20 :=
      Nat.add_le_add_right (hm.trans hc) 20
    _ = 3000*((L+1)^3*(downsetCap L cut+1))+20 := by ring
    _ ≤ 4000*((L+1)^3*(downsetCap L cut+1)) := by omega
    _ = _ := by ring

end ThreeSum.LightZetaPass

end


theorem solution : ∀ {L cut : Nat},
  @LE.le.{0} Nat instLENat cut L →
    @LE.le.{0} Nat instLENat (ThreeSum.LightZetaPass.time L cut)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4000) (instOfNatNat (nat_lit 4000)))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.SubsetAddress.downsetCap L cut)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @ThreeSum.LightZetaPass.time_bound_sourceProof

#print axioms solution
