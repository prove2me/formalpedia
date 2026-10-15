-- Prove2me | solution 1 for ThreeSum.LightRadixKeys.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:52:25.876552+00:00
-- url     : https://prove2.me/submissions/6fc7a11b-48c7-403a-bc88-4f7c4400362d

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists

section


/-!
# Costed Cartesian rows for positional keys

For every local key, an actual affine scan writes one entire row of extended
keys. The arrays contain the complete product list, including equal integer
keys attached to different original records. No division or decoding loop is
used to locate Cartesian coordinates at runtime.
-/

namespace ThreeSum.LightRadixRows

open Light RadixKeyLists

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000















variable {lim : Limits} {P : Program} {d : ℕ}











































































































theorem time_bound_product (m n : ℕ) (hn : 0 < n) : time m n ≤ 130*m*n+20 := by
  unfold time LightReportingAffine.time
  have hmn : m ≤ m*n := Nat.le_mul_of_pos_right m hn
  nlinarith

end ThreeSum.LightRadixRows

end

section


/-!
# Complete positional-key product construction

The three fixed procedures build every product stage. Each stage has a
computed length header followed by its literal key array. The recursive
caller reads the previous header and appends Cartesian rows. Its final
array contains every record sequence, retaining repeated keys.
-/

namespace ThreeSum.LightRadixKeys

open Light RadixKeyLists

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000













































theorem time_bound_sourceProof (m J : ℕ) (hm : 1 ≤ m) :
    time m J ≤ 300*(J+1)*(m^J+1) := by
  have haux : ∀ j, j ≤ J → time m j ≤ 50+j*(130*m^J+220) := by
    intro j
    induction j with
    | zero => simp [time]
    | succ j ih =>
      intro hj
      have ht := ih (by omega)
      have hr := LightRadixRows.time_bound_product m (m^j) (Nat.pow_pos (by omega))
      have hp := Nat.pow_le_pow_right hm hj
      rw [pow_succ'] at hp
      have hp' := Nat.mul_le_mul_left 130 hp
      rw [time]
      nlinarith
  have hh := haux J le_rfl
  have he : 300*(J+1)*(m^J+1) =
      50+J*(130*m^J+220)+(170*J*m^J+80*J+300*m^J+250) := by ring
  rw [he]
  omega












variable {lim : Limits} {P : Program}























































































































end ThreeSum.LightRadixKeys

end


theorem solution : ∀ (m J : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m →
    @LE.le.{0} Nat instLENat (ThreeSum.LightRadixKeys.time m J)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) m J)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @ThreeSum.LightRadixKeys.time_bound_sourceProof

#print axioms solution
