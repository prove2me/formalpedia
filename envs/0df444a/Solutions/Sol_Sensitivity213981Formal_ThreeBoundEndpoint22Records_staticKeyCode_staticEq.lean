-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Records.staticKeyCode_staticEq
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:52:39.906743+00:00
-- url     : https://prove2.me/submissions/dfc000f1-3af7-4975-9072-588e24fdd946

import Definitions.Def_Sensitivity213981Formal_Endpoint22StaticProjection
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto


namespace Sensitivity213981Formal
section
/- The nineteen static fields are an arithmetic projection of each packed row. -/


set_option autoImplicit false
set_option maxHeartbeats 400000

namespace ThreeBoundEndpoint22Records



theorem staticKeyCode_mod (code : ℕ) : staticKeyCode code % 16^12 = code % 16^12 := by
  simp only [staticKeyCode, Nat.add_mul_mod_self_left, Nat.mod_mod]

theorem staticKeyCode_div (code : ℕ) : staticKeyCode code / 16^12 = code / 16^34 := by
  unfold staticKeyCode
  rw [Nat.add_mul_div_left _ _ (by decide : 0 <  (16:ℕ)^12)]
  rw [Nat.div_eq_of_lt (Nat.mod_lt _ (by decide : 0 <  (16:ℕ)^12)), Nat.zero_add]

theorem staticKeyCode_low_digit (code k : ℕ) (hk : k <  12) :
    (staticKeyCode code / 16^k) % 16 = (code / 16^k) % 16 := by
  have hd : (16:ℕ)^k * 16 ∣ 16^12 := by
    rw [← pow_succ]
    exact pow_dvd_pow 16 (by omega)
  have hm : staticKeyCode code % (16^k*16) = code % (16^k*16) := by
    calc
      _ = (staticKeyCode code % 16^12) % (16^k*16) := (Nat.mod_mod_of_dvd _ hd).symm
      _ = (code % 16^12) % (16^k*16) := by rw [staticKeyCode_mod]
      _ = _ := Nat.mod_mod_of_dvd _ hd
  rw [← Nat.mod_mul_right_div_self, hm, Nat.mod_mul_right_div_self]

theorem staticKeyCode_high_div (code k : ℕ) :
    staticKeyCode code / 16^(12+k) = code / 16^(34+k) := by
  rw [pow_add, ← Nat.div_div_eq_div_mul, staticKeyCode_div,
    Nat.div_div_eq_div_mul, ← pow_add]

/-- Projection preserves every field used by cap and converted-cost preparation. -/
theorem staticKeyCode_staticEq (code : ℕ) :
    ThreeBoundRankCached.StaticEq (codeRecord code) (staticCodeRecord (staticKeyCode code)) := by
  constructor
  · intro k
    have h12 : k.val <  12 := k.isLt
    have h41 : k.val <  41 := by omega
    simp only [codeRecord, staticCodeRecord, if_pos h41, if_pos h12]
    unfold decodeDigit
    rw [staticKeyCode_low_digit code k.val h12]
  · intro k
    have h41 : 34+k.val <  41 := by omega
    have hn : ¬34+k.val <  12 := by omega
    have hr : 34 ≤  34+k.val ∧ 34+k.val <  41 := ⟨by omega,h41⟩
    have he : 34+k.val-22=12+k.val := by omega
    simp only [codeRecord, staticCodeRecord, if_pos h41, if_neg hn, if_pos hr, he]
    rw [staticKeyCode_high_div]

end ThreeBoundEndpoint22Records


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (code : Nat),
  Sensitivity213981Formal.ThreeBoundRankCached.StaticEq
    (Sensitivity213981Formal.ThreeBoundEndpoint22Records.codeRecord code)
    (Sensitivity213981Formal.ThreeBoundEndpoint22Records.staticCodeRecord
      (Sensitivity213981Formal.ThreeBoundEndpoint22Records.staticKeyCode code)) := @Sensitivity213981Formal.ThreeBoundEndpoint22Records.staticKeyCode_staticEq
