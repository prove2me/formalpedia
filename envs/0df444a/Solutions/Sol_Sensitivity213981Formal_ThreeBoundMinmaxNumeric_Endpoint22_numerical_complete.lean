-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.numerical_complete
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:29:35.773359+00:00
-- url     : https://prove2.me/submissions/205b55db-5267-4b52-9e93-9e26a87a3851

import Definitions.Def_Sensitivity213981Formal_Endpoint22NumericData
import Definitions.Def_Sensitivity213981Formal_Endpoint22NumericalComplete
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData
import Definitions.Def_Sensitivity213981Formal_Endpoint22SeedCover0
import Definitions.Def_Sensitivity213981Formal_Endpoint22SeedCover1
import Definitions.Def_Sensitivity213981Formal_Endpoint22SeedCover2
import Definitions.Def_Sensitivity213981Formal_Endpoint22SeedCover3
import Definitions.Def_Sensitivity213981Formal_MinmaxCoreBounds
import Definitions.Def_Sensitivity213981Formal_MinmaxHybridTransfer
import Definitions.Def_Sensitivity213981Formal_MinmaxRankRawTransfer
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Init.Data.Nat.Bitwise.Lemmas
import Lean
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_seed_bounds0
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_seed_bounds1
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_seed_bounds2
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_seed_bounds3


namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile ClosureCertificate




theorem aChoice_checked0 : ∀ i j : Fin 22, i≤ j →
    (aChoice0 i j)∈aSeeds0 ∧ i≤ (aChoice0 i j).1 ∧
    (aChoice0 i j).1≤ (aChoice0 i j).2 ∧ (aChoice0 i j).2≤ j ∧
    rawProfile0 (.a (aChoice0 i j).1 (aChoice0 i j).2)≤ rawProfile0 (.a i j):=by decide +kernel

theorem aCovers0 : ThreeBoundMinmaxHybrid.ACovers rawProfile0 aSeeds0:=by
  intro i j hij
  exact ⟨aChoice0 i j,aChoice_checked0 i j hij⟩
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_0_0 : ∀ j : Fin 22, (0 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 0) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 0 j) := by decide +kernel

theorem m_choice_check_0_0 : ∀ j : Fin 22, (0 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 0) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 0 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 0) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 0 j) := by decide +kernel

theorem p_core_check_0_0 : ∀ l : Fin 22, (0 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 0) (recipe 0 (next 0)) (recipe 0 l)
      (rawProfile0 (.a (next 0) l))≤ rawProfile0 (.p 0 l) := by decide +kernel

theorem d_core_check_0_0 : ∀ j l : Fin 22, (0 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 0) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 0 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 0 j l) := by decide +kernel

theorem b_base_check_0_1 : ∀ j : Fin 22, (1 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 1) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 1 j) := by decide +kernel

theorem m_choice_check_0_1 : ∀ j : Fin 22, (1 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 1) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 1 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 1) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 1 j) := by decide +kernel

theorem p_core_check_0_1 : ∀ l : Fin 22, (1 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 1) (recipe 0 (next 1)) (recipe 0 l)
      (rawProfile0 (.a (next 1) l))≤ rawProfile0 (.p 1 l) := by decide +kernel

theorem d_core_check_0_1 : ∀ j l : Fin 22, (1 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 1) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 1 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 1 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_0_2 : ∀ j : Fin 22, (2 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 2) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 2 j) := by decide +kernel

theorem m_choice_check_0_2 : ∀ j : Fin 22, (2 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 2) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 2 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 2) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 2 j) := by decide +kernel

theorem p_core_check_0_2 : ∀ l : Fin 22, (2 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 2) (recipe 0 (next 2)) (recipe 0 l)
      (rawProfile0 (.a (next 2) l))≤ rawProfile0 (.p 2 l) := by decide +kernel

theorem d_core_check_0_2 : ∀ j l : Fin 22, (2 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 2) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 2 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 2 j l) := by decide +kernel

theorem b_base_check_0_3 : ∀ j : Fin 22, (3 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 3) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 3 j) := by decide +kernel

theorem m_choice_check_0_3 : ∀ j : Fin 22, (3 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 3) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 3 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 3) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 3 j) := by decide +kernel

theorem p_core_check_0_3 : ∀ l : Fin 22, (3 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 3) (recipe 0 (next 3)) (recipe 0 l)
      (rawProfile0 (.a (next 3) l))≤ rawProfile0 (.p 3 l) := by decide +kernel

theorem d_core_check_0_3 : ∀ j l : Fin 22, (3 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 3) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 3 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 3 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_0_4 : ∀ j : Fin 22, (4 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 4) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 4 j) := by decide +kernel

theorem m_choice_check_0_4 : ∀ j : Fin 22, (4 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 4) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 4 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 4) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 4 j) := by decide +kernel

theorem p_core_check_0_4 : ∀ l : Fin 22, (4 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 4) (recipe 0 (next 4)) (recipe 0 l)
      (rawProfile0 (.a (next 4) l))≤ rawProfile0 (.p 4 l) := by decide +kernel

theorem d_core_check_0_4 : ∀ j l : Fin 22, (4 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 4) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 4 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 4 j l) := by decide +kernel

theorem b_base_check_0_5 : ∀ j : Fin 22, (5 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 5) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 5 j) := by decide +kernel

theorem m_choice_check_0_5 : ∀ j : Fin 22, (5 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 5) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 5 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 5) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 5 j) := by decide +kernel

theorem p_core_check_0_5 : ∀ l : Fin 22, (5 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 5) (recipe 0 (next 5)) (recipe 0 l)
      (rawProfile0 (.a (next 5) l))≤ rawProfile0 (.p 5 l) := by decide +kernel

theorem d_core_check_0_5 : ∀ j l : Fin 22, (5 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 5) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 5 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 5 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_0_6 : ∀ j : Fin 22, (6 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 6) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 6 j) := by decide +kernel

theorem m_choice_check_0_6 : ∀ j : Fin 22, (6 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 6) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 6 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 6) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 6 j) := by decide +kernel

theorem p_core_check_0_6 : ∀ l : Fin 22, (6 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 6) (recipe 0 (next 6)) (recipe 0 l)
      (rawProfile0 (.a (next 6) l))≤ rawProfile0 (.p 6 l) := by decide +kernel

theorem d_core_check_0_6 : ∀ j l : Fin 22, (6 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 6) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 6 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 6 j l) := by decide +kernel

theorem b_base_check_0_7 : ∀ j : Fin 22, (7 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 7) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 7 j) := by decide +kernel

theorem m_choice_check_0_7 : ∀ j : Fin 22, (7 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 7) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 7 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 7) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 7 j) := by decide +kernel

theorem p_core_check_0_7 : ∀ l : Fin 22, (7 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 7) (recipe 0 (next 7)) (recipe 0 l)
      (rawProfile0 (.a (next 7) l))≤ rawProfile0 (.p 7 l) := by decide +kernel

theorem d_core_check_0_7 : ∀ j l : Fin 22, (7 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 7) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 7 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 7 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_0_8 : ∀ j : Fin 22, (8 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 8) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 8 j) := by decide +kernel

theorem m_choice_check_0_8 : ∀ j : Fin 22, (8 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 8) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 8 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 8) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 8 j) := by decide +kernel

theorem p_core_check_0_8 : ∀ l : Fin 22, (8 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 8) (recipe 0 (next 8)) (recipe 0 l)
      (rawProfile0 (.a (next 8) l))≤ rawProfile0 (.p 8 l) := by decide +kernel

theorem d_core_check_0_8 : ∀ j l : Fin 22, (8 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 8) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 8 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 8 j l) := by decide +kernel

theorem b_base_check_0_9 : ∀ j : Fin 22, (9 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 9) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 9 j) := by decide +kernel

theorem m_choice_check_0_9 : ∀ j : Fin 22, (9 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 9) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 9 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 9) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 9 j) := by decide +kernel

theorem p_core_check_0_9 : ∀ l : Fin 22, (9 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 9) (recipe 0 (next 9)) (recipe 0 l)
      (rawProfile0 (.a (next 9) l))≤ rawProfile0 (.p 9 l) := by decide +kernel

theorem d_core_check_0_9 : ∀ j l : Fin 22, (9 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 9) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 9 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 9 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_0_10 : ∀ j : Fin 22, (10 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 10) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 10 j) := by decide +kernel

theorem m_choice_check_0_10 : ∀ j : Fin 22, (10 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 10) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 10 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 10) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 10 j) := by decide +kernel

theorem p_core_check_0_10 : ∀ l : Fin 22, (10 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 10) (recipe 0 (next 10)) (recipe 0 l)
      (rawProfile0 (.a (next 10) l))≤ rawProfile0 (.p 10 l) := by decide +kernel

theorem d_core_check_0_10 : ∀ j l : Fin 22, (10 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 10) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 10 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 10 j l) := by decide +kernel

theorem b_base_check_0_11 : ∀ j : Fin 22, (11 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 11) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 11 j) := by decide +kernel

theorem m_choice_check_0_11 : ∀ j : Fin 22, (11 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 11) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 11 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 11) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 11 j) := by decide +kernel

theorem p_core_check_0_11 : ∀ l : Fin 22, (11 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 11) (recipe 0 (next 11)) (recipe 0 l)
      (rawProfile0 (.a (next 11) l))≤ rawProfile0 (.p 11 l) := by decide +kernel

theorem d_core_check_0_11 : ∀ j l : Fin 22, (11 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 11) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 11 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 11 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_0_12 : ∀ j : Fin 22, (12 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 12) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 12 j) := by decide +kernel

theorem m_choice_check_0_12 : ∀ j : Fin 22, (12 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 12) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 12 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 12) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 12 j) := by decide +kernel

theorem p_core_check_0_12 : ∀ l : Fin 22, (12 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 12) (recipe 0 (next 12)) (recipe 0 l)
      (rawProfile0 (.a (next 12) l))≤ rawProfile0 (.p 12 l) := by decide +kernel

theorem d_core_check_0_12 : ∀ j l : Fin 22, (12 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 12) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 12 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 12 j l) := by decide +kernel

theorem b_base_check_0_13 : ∀ j : Fin 22, (13 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 13) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 13 j) := by decide +kernel

theorem m_choice_check_0_13 : ∀ j : Fin 22, (13 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 13) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 13 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 13) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 13 j) := by decide +kernel

theorem p_core_check_0_13 : ∀ l : Fin 22, (13 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 13) (recipe 0 (next 13)) (recipe 0 l)
      (rawProfile0 (.a (next 13) l))≤ rawProfile0 (.p 13 l) := by decide +kernel

theorem d_core_check_0_13 : ∀ j l : Fin 22, (13 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 13) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 13 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 13 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_0_14 : ∀ j : Fin 22, (14 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 14) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 14 j) := by decide +kernel

theorem m_choice_check_0_14 : ∀ j : Fin 22, (14 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 14) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 14 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 14) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 14 j) := by decide +kernel

theorem p_core_check_0_14 : ∀ l : Fin 22, (14 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 14) (recipe 0 (next 14)) (recipe 0 l)
      (rawProfile0 (.a (next 14) l))≤ rawProfile0 (.p 14 l) := by decide +kernel

theorem d_core_check_0_14 : ∀ j l : Fin 22, (14 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 14) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 14 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 14 j l) := by decide +kernel

theorem b_base_check_0_15 : ∀ j : Fin 22, (15 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 15) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 15 j) := by decide +kernel

theorem m_choice_check_0_15 : ∀ j : Fin 22, (15 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 15) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 15 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 15) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 15 j) := by decide +kernel

theorem p_core_check_0_15 : ∀ l : Fin 22, (15 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 15) (recipe 0 (next 15)) (recipe 0 l)
      (rawProfile0 (.a (next 15) l))≤ rawProfile0 (.p 15 l) := by decide +kernel

theorem d_core_check_0_15 : ∀ j l : Fin 22, (15 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 15) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 15 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 15 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_0_16 : ∀ j : Fin 22, (16 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 16) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 16 j) := by decide +kernel

theorem m_choice_check_0_16 : ∀ j : Fin 22, (16 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 16) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 16 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 16) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 16 j) := by decide +kernel

theorem p_core_check_0_16 : ∀ l : Fin 22, (16 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 16) (recipe 0 (next 16)) (recipe 0 l)
      (rawProfile0 (.a (next 16) l))≤ rawProfile0 (.p 16 l) := by decide +kernel

theorem d_core_check_0_16 : ∀ j l : Fin 22, (16 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 16) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 16 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 16 j l) := by decide +kernel

theorem b_base_check_0_17 : ∀ j : Fin 22, (17 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 17) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 17 j) := by decide +kernel

theorem m_choice_check_0_17 : ∀ j : Fin 22, (17 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 17) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 17 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 17) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 17 j) := by decide +kernel

theorem p_core_check_0_17 : ∀ l : Fin 22, (17 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 17) (recipe 0 (next 17)) (recipe 0 l)
      (rawProfile0 (.a (next 17) l))≤ rawProfile0 (.p 17 l) := by decide +kernel

theorem d_core_check_0_17 : ∀ j l : Fin 22, (17 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 17) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 17 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 17 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_0_18 : ∀ j : Fin 22, (18 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 18) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 18 j) := by decide +kernel

theorem m_choice_check_0_18 : ∀ j : Fin 22, (18 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 18) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 18 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 18) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 18 j) := by decide +kernel

theorem p_core_check_0_18 : ∀ l : Fin 22, (18 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 18) (recipe 0 (next 18)) (recipe 0 l)
      (rawProfile0 (.a (next 18) l))≤ rawProfile0 (.p 18 l) := by decide +kernel

theorem d_core_check_0_18 : ∀ j l : Fin 22, (18 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 18) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 18 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 18 j l) := by decide +kernel

theorem b_base_check_0_19 : ∀ j : Fin 22, (19 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 19) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 19 j) := by decide +kernel

theorem m_choice_check_0_19 : ∀ j : Fin 22, (19 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 19) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 19 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 19) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 19 j) := by decide +kernel

theorem p_core_check_0_19 : ∀ l : Fin 22, (19 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 19) (recipe 0 (next 19)) (recipe 0 l)
      (rawProfile0 (.a (next 19) l))≤ rawProfile0 (.p 19 l) := by decide +kernel

theorem d_core_check_0_19 : ∀ j l : Fin 22, (19 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 19) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 19 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 19 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_0_20 : ∀ j : Fin 22, (20 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 20) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 20 j) := by decide +kernel

theorem m_choice_check_0_20 : ∀ j : Fin 22, (20 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 20) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 20 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 20) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 20 j) := by decide +kernel

theorem p_core_check_0_20 : ∀ l : Fin 22, (20 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 20) (recipe 0 (next 20)) (recipe 0 l)
      (rawProfile0 (.a (next 20) l))≤ rawProfile0 (.p 20 l) := by decide +kernel

theorem d_core_check_0_20 : ∀ j l : Fin 22, (20 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 20) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 20 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 20 j l) := by decide +kernel

theorem b_base_check_0_21 : ∀ j : Fin 22, (21 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 21) (recipe 0 j)).eval profile0≤ rawProfile0 (.b 21 j) := by decide +kernel

theorem m_choice_check_0_21 : ∀ j : Fin 22, (21 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 21) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 21 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 21) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m 21 j) := by decide +kernel

theorem p_core_check_0_21 : ∀ l : Fin 22, (21 : Fin 22)< l →
    pCore 22 18 profile0 (recipe 0 21) (recipe 0 (next 21)) (recipe 0 l)
      (rawProfile0 (.a (next 21) l))≤ rawProfile0 (.p 21 l) := by decide +kernel

theorem d_core_check_0_21 : ∀ j l : Fin 22, (21 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 21) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 21 j)+rawProfile0 (.p j l))≤ rawProfile0 (.d 21 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_checked0 : ∀ i j : Fin 22, i≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 0 i) (recipe 0 j)).eval profile0≤ rawProfile0 (.b i j) := by
  intro i
  fin_cases i
  · exact b_base_check_0_0
  · exact b_base_check_0_1
  · exact b_base_check_0_2
  · exact b_base_check_0_3
  · exact b_base_check_0_4
  · exact b_base_check_0_5
  · exact b_base_check_0_6
  · exact b_base_check_0_7
  · exact b_base_check_0_8
  · exact b_base_check_0_9
  · exact b_base_check_0_10
  · exact b_base_check_0_11
  · exact b_base_check_0_12
  · exact b_base_check_0_13
  · exact b_base_check_0_14
  · exact b_base_check_0_15
  · exact b_base_check_0_16
  · exact b_base_check_0_17
  · exact b_base_check_0_18
  · exact b_base_check_0_19
  · exact b_base_check_0_20
  · exact b_base_check_0_21

theorem m_choice_checked0 : ∀ i j : Fin 22, i≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 0 i) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m i j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 0 i) (recipe 0 j) (recipe 0 (next j))).eval profile0≤ rawProfile0 (.m i j) := by
  intro i
  fin_cases i
  · exact m_choice_check_0_0
  · exact m_choice_check_0_1
  · exact m_choice_check_0_2
  · exact m_choice_check_0_3
  · exact m_choice_check_0_4
  · exact m_choice_check_0_5
  · exact m_choice_check_0_6
  · exact m_choice_check_0_7
  · exact m_choice_check_0_8
  · exact m_choice_check_0_9
  · exact m_choice_check_0_10
  · exact m_choice_check_0_11
  · exact m_choice_check_0_12
  · exact m_choice_check_0_13
  · exact m_choice_check_0_14
  · exact m_choice_check_0_15
  · exact m_choice_check_0_16
  · exact m_choice_check_0_17
  · exact m_choice_check_0_18
  · exact m_choice_check_0_19
  · exact m_choice_check_0_20
  · exact m_choice_check_0_21

theorem p_core_checked0 : ∀ j l : Fin 22, j< l →
    pCore 22 18 profile0 (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.a (next j) l))≤ rawProfile0 (.p j l) := by
  intro i
  fin_cases i
  · exact p_core_check_0_0
  · exact p_core_check_0_1
  · exact p_core_check_0_2
  · exact p_core_check_0_3
  · exact p_core_check_0_4
  · exact p_core_check_0_5
  · exact p_core_check_0_6
  · exact p_core_check_0_7
  · exact p_core_check_0_8
  · exact p_core_check_0_9
  · exact p_core_check_0_10
  · exact p_core_check_0_11
  · exact p_core_check_0_12
  · exact p_core_check_0_13
  · exact p_core_check_0_14
  · exact p_core_check_0_15
  · exact p_core_check_0_16
  · exact p_core_check_0_17
  · exact p_core_check_0_18
  · exact p_core_check_0_19
  · exact p_core_check_0_20
  · exact p_core_check_0_21

theorem d_core_checked0 : ∀ i j l : Fin 22, i≤ j → j< l →
    dCore 22 2795 profile0 (recipe 0 i) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m i j)+rawProfile0 (.p j l))≤ rawProfile0 (.d i j l) := by
  intro i
  fin_cases i
  · exact d_core_check_0_0
  · exact d_core_check_0_1
  · exact d_core_check_0_2
  · exact d_core_check_0_3
  · exact d_core_check_0_4
  · exact d_core_check_0_5
  · exact d_core_check_0_6
  · exact d_core_check_0_7
  · exact d_core_check_0_8
  · exact d_core_check_0_9
  · exact d_core_check_0_10
  · exact d_core_check_0_11
  · exact d_core_check_0_12
  · exact d_core_check_0_13
  · exact d_core_check_0_14
  · exact d_core_check_0_15
  · exact d_core_check_0_16
  · exact d_core_check_0_17
  · exact d_core_check_0_18
  · exact d_core_check_0_19
  · exact d_core_check_0_20
  · exact d_core_check_0_21

theorem core_bounds0 : ThreeBoundMinmaxHybrid.CoreBounds 2795 18 (recipe 0) profile0 rawProfile0 := by
  constructor
  · intro i j hij
    exact (min_le_left _ _).trans (b_base_checked0 i j hij)
  · intro i j hij hj
    rcases m_choice_checked0 i j hij hj with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans h
  · exact p_core_checked0
  · exact d_core_checked0
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile ClosureCertificate




theorem aChoice_checked1 : ∀ i j : Fin 22, i≤ j →
    (aChoice1 i j)∈aSeeds1 ∧ i≤ (aChoice1 i j).1 ∧
    (aChoice1 i j).1≤ (aChoice1 i j).2 ∧ (aChoice1 i j).2≤ j ∧
    rawProfile1 (.a (aChoice1 i j).1 (aChoice1 i j).2)≤ rawProfile1 (.a i j):=by decide +kernel

theorem aCovers1 : ThreeBoundMinmaxHybrid.ACovers rawProfile1 aSeeds1:=by
  intro i j hij
  exact ⟨aChoice1 i j,aChoice_checked1 i j hij⟩
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_1_0 : ∀ j : Fin 22, (0 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 0) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 0 j) := by decide +kernel

theorem m_choice_check_1_0 : ∀ j : Fin 22, (0 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 0) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 0 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 0) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 0 j) := by decide +kernel

theorem p_core_check_1_0 : ∀ l : Fin 22, (0 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 0) (recipe 1 (next 0)) (recipe 1 l)
      (rawProfile1 (.a (next 0) l))≤ rawProfile1 (.p 0 l) := by decide +kernel

theorem d_core_check_1_0 : ∀ j l : Fin 22, (0 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 0) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 0 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 0 j l) := by decide +kernel

theorem b_base_check_1_1 : ∀ j : Fin 22, (1 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 1) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 1 j) := by decide +kernel

theorem m_choice_check_1_1 : ∀ j : Fin 22, (1 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 1) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 1 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 1) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 1 j) := by decide +kernel

theorem p_core_check_1_1 : ∀ l : Fin 22, (1 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 1) (recipe 1 (next 1)) (recipe 1 l)
      (rawProfile1 (.a (next 1) l))≤ rawProfile1 (.p 1 l) := by decide +kernel

theorem d_core_check_1_1 : ∀ j l : Fin 22, (1 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 1) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 1 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 1 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_1_2 : ∀ j : Fin 22, (2 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 2) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 2 j) := by decide +kernel

theorem m_choice_check_1_2 : ∀ j : Fin 22, (2 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 2) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 2 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 2) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 2 j) := by decide +kernel

theorem p_core_check_1_2 : ∀ l : Fin 22, (2 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 2) (recipe 1 (next 2)) (recipe 1 l)
      (rawProfile1 (.a (next 2) l))≤ rawProfile1 (.p 2 l) := by decide +kernel

theorem d_core_check_1_2 : ∀ j l : Fin 22, (2 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 2) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 2 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 2 j l) := by decide +kernel

theorem b_base_check_1_3 : ∀ j : Fin 22, (3 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 3) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 3 j) := by decide +kernel

theorem m_choice_check_1_3 : ∀ j : Fin 22, (3 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 3) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 3 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 3) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 3 j) := by decide +kernel

theorem p_core_check_1_3 : ∀ l : Fin 22, (3 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 3) (recipe 1 (next 3)) (recipe 1 l)
      (rawProfile1 (.a (next 3) l))≤ rawProfile1 (.p 3 l) := by decide +kernel

theorem d_core_check_1_3 : ∀ j l : Fin 22, (3 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 3) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 3 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 3 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_1_4 : ∀ j : Fin 22, (4 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 4) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 4 j) := by decide +kernel

theorem m_choice_check_1_4 : ∀ j : Fin 22, (4 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 4) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 4 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 4) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 4 j) := by decide +kernel

theorem p_core_check_1_4 : ∀ l : Fin 22, (4 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 4) (recipe 1 (next 4)) (recipe 1 l)
      (rawProfile1 (.a (next 4) l))≤ rawProfile1 (.p 4 l) := by decide +kernel

theorem d_core_check_1_4 : ∀ j l : Fin 22, (4 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 4) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 4 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 4 j l) := by decide +kernel

theorem b_base_check_1_5 : ∀ j : Fin 22, (5 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 5) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 5 j) := by decide +kernel

theorem m_choice_check_1_5 : ∀ j : Fin 22, (5 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 5) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 5 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 5) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 5 j) := by decide +kernel

theorem p_core_check_1_5 : ∀ l : Fin 22, (5 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 5) (recipe 1 (next 5)) (recipe 1 l)
      (rawProfile1 (.a (next 5) l))≤ rawProfile1 (.p 5 l) := by decide +kernel

theorem d_core_check_1_5 : ∀ j l : Fin 22, (5 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 5) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 5 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 5 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_1_6 : ∀ j : Fin 22, (6 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 6) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 6 j) := by decide +kernel

theorem m_choice_check_1_6 : ∀ j : Fin 22, (6 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 6) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 6 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 6) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 6 j) := by decide +kernel

theorem p_core_check_1_6 : ∀ l : Fin 22, (6 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 6) (recipe 1 (next 6)) (recipe 1 l)
      (rawProfile1 (.a (next 6) l))≤ rawProfile1 (.p 6 l) := by decide +kernel

theorem d_core_check_1_6 : ∀ j l : Fin 22, (6 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 6) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 6 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 6 j l) := by decide +kernel

theorem b_base_check_1_7 : ∀ j : Fin 22, (7 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 7) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 7 j) := by decide +kernel

theorem m_choice_check_1_7 : ∀ j : Fin 22, (7 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 7) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 7 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 7) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 7 j) := by decide +kernel

theorem p_core_check_1_7 : ∀ l : Fin 22, (7 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 7) (recipe 1 (next 7)) (recipe 1 l)
      (rawProfile1 (.a (next 7) l))≤ rawProfile1 (.p 7 l) := by decide +kernel

theorem d_core_check_1_7 : ∀ j l : Fin 22, (7 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 7) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 7 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 7 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_1_8 : ∀ j : Fin 22, (8 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 8) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 8 j) := by decide +kernel

theorem m_choice_check_1_8 : ∀ j : Fin 22, (8 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 8) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 8 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 8) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 8 j) := by decide +kernel

theorem p_core_check_1_8 : ∀ l : Fin 22, (8 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 8) (recipe 1 (next 8)) (recipe 1 l)
      (rawProfile1 (.a (next 8) l))≤ rawProfile1 (.p 8 l) := by decide +kernel

theorem d_core_check_1_8 : ∀ j l : Fin 22, (8 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 8) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 8 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 8 j l) := by decide +kernel

theorem b_base_check_1_9 : ∀ j : Fin 22, (9 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 9) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 9 j) := by decide +kernel

theorem m_choice_check_1_9 : ∀ j : Fin 22, (9 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 9) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 9 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 9) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 9 j) := by decide +kernel

theorem p_core_check_1_9 : ∀ l : Fin 22, (9 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 9) (recipe 1 (next 9)) (recipe 1 l)
      (rawProfile1 (.a (next 9) l))≤ rawProfile1 (.p 9 l) := by decide +kernel

theorem d_core_check_1_9 : ∀ j l : Fin 22, (9 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 9) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 9 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 9 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_1_10 : ∀ j : Fin 22, (10 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 10) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 10 j) := by decide +kernel

theorem m_choice_check_1_10 : ∀ j : Fin 22, (10 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 10) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 10 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 10) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 10 j) := by decide +kernel

theorem p_core_check_1_10 : ∀ l : Fin 22, (10 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 10) (recipe 1 (next 10)) (recipe 1 l)
      (rawProfile1 (.a (next 10) l))≤ rawProfile1 (.p 10 l) := by decide +kernel

theorem d_core_check_1_10 : ∀ j l : Fin 22, (10 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 10) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 10 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 10 j l) := by decide +kernel

theorem b_base_check_1_11 : ∀ j : Fin 22, (11 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 11) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 11 j) := by decide +kernel

theorem m_choice_check_1_11 : ∀ j : Fin 22, (11 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 11) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 11 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 11) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 11 j) := by decide +kernel

theorem p_core_check_1_11 : ∀ l : Fin 22, (11 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 11) (recipe 1 (next 11)) (recipe 1 l)
      (rawProfile1 (.a (next 11) l))≤ rawProfile1 (.p 11 l) := by decide +kernel

theorem d_core_check_1_11 : ∀ j l : Fin 22, (11 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 11) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 11 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 11 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_1_12 : ∀ j : Fin 22, (12 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 12) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 12 j) := by decide +kernel

theorem m_choice_check_1_12 : ∀ j : Fin 22, (12 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 12) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 12 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 12) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 12 j) := by decide +kernel

theorem p_core_check_1_12 : ∀ l : Fin 22, (12 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 12) (recipe 1 (next 12)) (recipe 1 l)
      (rawProfile1 (.a (next 12) l))≤ rawProfile1 (.p 12 l) := by decide +kernel

theorem d_core_check_1_12 : ∀ j l : Fin 22, (12 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 12) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 12 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 12 j l) := by decide +kernel

theorem b_base_check_1_13 : ∀ j : Fin 22, (13 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 13) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 13 j) := by decide +kernel

theorem m_choice_check_1_13 : ∀ j : Fin 22, (13 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 13) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 13 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 13) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 13 j) := by decide +kernel

theorem p_core_check_1_13 : ∀ l : Fin 22, (13 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 13) (recipe 1 (next 13)) (recipe 1 l)
      (rawProfile1 (.a (next 13) l))≤ rawProfile1 (.p 13 l) := by decide +kernel

theorem d_core_check_1_13 : ∀ j l : Fin 22, (13 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 13) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 13 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 13 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_1_14 : ∀ j : Fin 22, (14 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 14) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 14 j) := by decide +kernel

theorem m_choice_check_1_14 : ∀ j : Fin 22, (14 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 14) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 14 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 14) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 14 j) := by decide +kernel

theorem p_core_check_1_14 : ∀ l : Fin 22, (14 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 14) (recipe 1 (next 14)) (recipe 1 l)
      (rawProfile1 (.a (next 14) l))≤ rawProfile1 (.p 14 l) := by decide +kernel

theorem d_core_check_1_14 : ∀ j l : Fin 22, (14 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 14) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 14 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 14 j l) := by decide +kernel

theorem b_base_check_1_15 : ∀ j : Fin 22, (15 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 15) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 15 j) := by decide +kernel

theorem m_choice_check_1_15 : ∀ j : Fin 22, (15 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 15) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 15 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 15) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 15 j) := by decide +kernel

theorem p_core_check_1_15 : ∀ l : Fin 22, (15 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 15) (recipe 1 (next 15)) (recipe 1 l)
      (rawProfile1 (.a (next 15) l))≤ rawProfile1 (.p 15 l) := by decide +kernel

theorem d_core_check_1_15 : ∀ j l : Fin 22, (15 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 15) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 15 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 15 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_1_16 : ∀ j : Fin 22, (16 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 16) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 16 j) := by decide +kernel

theorem m_choice_check_1_16 : ∀ j : Fin 22, (16 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 16) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 16 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 16) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 16 j) := by decide +kernel

theorem p_core_check_1_16 : ∀ l : Fin 22, (16 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 16) (recipe 1 (next 16)) (recipe 1 l)
      (rawProfile1 (.a (next 16) l))≤ rawProfile1 (.p 16 l) := by decide +kernel

theorem d_core_check_1_16 : ∀ j l : Fin 22, (16 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 16) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 16 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 16 j l) := by decide +kernel

theorem b_base_check_1_17 : ∀ j : Fin 22, (17 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 17) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 17 j) := by decide +kernel

theorem m_choice_check_1_17 : ∀ j : Fin 22, (17 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 17) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 17 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 17) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 17 j) := by decide +kernel

theorem p_core_check_1_17 : ∀ l : Fin 22, (17 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 17) (recipe 1 (next 17)) (recipe 1 l)
      (rawProfile1 (.a (next 17) l))≤ rawProfile1 (.p 17 l) := by decide +kernel

theorem d_core_check_1_17 : ∀ j l : Fin 22, (17 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 17) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 17 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 17 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_1_18 : ∀ j : Fin 22, (18 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 18) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 18 j) := by decide +kernel

theorem m_choice_check_1_18 : ∀ j : Fin 22, (18 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 18) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 18 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 18) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 18 j) := by decide +kernel

theorem p_core_check_1_18 : ∀ l : Fin 22, (18 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 18) (recipe 1 (next 18)) (recipe 1 l)
      (rawProfile1 (.a (next 18) l))≤ rawProfile1 (.p 18 l) := by decide +kernel

theorem d_core_check_1_18 : ∀ j l : Fin 22, (18 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 18) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 18 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 18 j l) := by decide +kernel

theorem b_base_check_1_19 : ∀ j : Fin 22, (19 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 19) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 19 j) := by decide +kernel

theorem m_choice_check_1_19 : ∀ j : Fin 22, (19 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 19) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 19 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 19) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 19 j) := by decide +kernel

theorem p_core_check_1_19 : ∀ l : Fin 22, (19 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 19) (recipe 1 (next 19)) (recipe 1 l)
      (rawProfile1 (.a (next 19) l))≤ rawProfile1 (.p 19 l) := by decide +kernel

theorem d_core_check_1_19 : ∀ j l : Fin 22, (19 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 19) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 19 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 19 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_1_20 : ∀ j : Fin 22, (20 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 20) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 20 j) := by decide +kernel

theorem m_choice_check_1_20 : ∀ j : Fin 22, (20 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 20) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 20 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 20) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 20 j) := by decide +kernel

theorem p_core_check_1_20 : ∀ l : Fin 22, (20 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 20) (recipe 1 (next 20)) (recipe 1 l)
      (rawProfile1 (.a (next 20) l))≤ rawProfile1 (.p 20 l) := by decide +kernel

theorem d_core_check_1_20 : ∀ j l : Fin 22, (20 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 20) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 20 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 20 j l) := by decide +kernel

theorem b_base_check_1_21 : ∀ j : Fin 22, (21 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 21) (recipe 1 j)).eval profile1≤ rawProfile1 (.b 21 j) := by decide +kernel

theorem m_choice_check_1_21 : ∀ j : Fin 22, (21 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 21) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 21 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 21) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m 21 j) := by decide +kernel

theorem p_core_check_1_21 : ∀ l : Fin 22, (21 : Fin 22)< l →
    pCore 22 18 profile1 (recipe 1 21) (recipe 1 (next 21)) (recipe 1 l)
      (rawProfile1 (.a (next 21) l))≤ rawProfile1 (.p 21 l) := by decide +kernel

theorem d_core_check_1_21 : ∀ j l : Fin 22, (21 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 21) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 21 j)+rawProfile1 (.p j l))≤ rawProfile1 (.d 21 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_checked1 : ∀ i j : Fin 22, i≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 1 i) (recipe 1 j)).eval profile1≤ rawProfile1 (.b i j) := by
  intro i
  fin_cases i
  · exact b_base_check_1_0
  · exact b_base_check_1_1
  · exact b_base_check_1_2
  · exact b_base_check_1_3
  · exact b_base_check_1_4
  · exact b_base_check_1_5
  · exact b_base_check_1_6
  · exact b_base_check_1_7
  · exact b_base_check_1_8
  · exact b_base_check_1_9
  · exact b_base_check_1_10
  · exact b_base_check_1_11
  · exact b_base_check_1_12
  · exact b_base_check_1_13
  · exact b_base_check_1_14
  · exact b_base_check_1_15
  · exact b_base_check_1_16
  · exact b_base_check_1_17
  · exact b_base_check_1_18
  · exact b_base_check_1_19
  · exact b_base_check_1_20
  · exact b_base_check_1_21

theorem m_choice_checked1 : ∀ i j : Fin 22, i≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 1 i) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m i j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 1 i) (recipe 1 j) (recipe 1 (next j))).eval profile1≤ rawProfile1 (.m i j) := by
  intro i
  fin_cases i
  · exact m_choice_check_1_0
  · exact m_choice_check_1_1
  · exact m_choice_check_1_2
  · exact m_choice_check_1_3
  · exact m_choice_check_1_4
  · exact m_choice_check_1_5
  · exact m_choice_check_1_6
  · exact m_choice_check_1_7
  · exact m_choice_check_1_8
  · exact m_choice_check_1_9
  · exact m_choice_check_1_10
  · exact m_choice_check_1_11
  · exact m_choice_check_1_12
  · exact m_choice_check_1_13
  · exact m_choice_check_1_14
  · exact m_choice_check_1_15
  · exact m_choice_check_1_16
  · exact m_choice_check_1_17
  · exact m_choice_check_1_18
  · exact m_choice_check_1_19
  · exact m_choice_check_1_20
  · exact m_choice_check_1_21

theorem p_core_checked1 : ∀ j l : Fin 22, j< l →
    pCore 22 18 profile1 (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.a (next j) l))≤ rawProfile1 (.p j l) := by
  intro i
  fin_cases i
  · exact p_core_check_1_0
  · exact p_core_check_1_1
  · exact p_core_check_1_2
  · exact p_core_check_1_3
  · exact p_core_check_1_4
  · exact p_core_check_1_5
  · exact p_core_check_1_6
  · exact p_core_check_1_7
  · exact p_core_check_1_8
  · exact p_core_check_1_9
  · exact p_core_check_1_10
  · exact p_core_check_1_11
  · exact p_core_check_1_12
  · exact p_core_check_1_13
  · exact p_core_check_1_14
  · exact p_core_check_1_15
  · exact p_core_check_1_16
  · exact p_core_check_1_17
  · exact p_core_check_1_18
  · exact p_core_check_1_19
  · exact p_core_check_1_20
  · exact p_core_check_1_21

theorem d_core_checked1 : ∀ i j l : Fin 22, i≤ j → j< l →
    dCore 22 2795 profile1 (recipe 1 i) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m i j)+rawProfile1 (.p j l))≤ rawProfile1 (.d i j l) := by
  intro i
  fin_cases i
  · exact d_core_check_1_0
  · exact d_core_check_1_1
  · exact d_core_check_1_2
  · exact d_core_check_1_3
  · exact d_core_check_1_4
  · exact d_core_check_1_5
  · exact d_core_check_1_6
  · exact d_core_check_1_7
  · exact d_core_check_1_8
  · exact d_core_check_1_9
  · exact d_core_check_1_10
  · exact d_core_check_1_11
  · exact d_core_check_1_12
  · exact d_core_check_1_13
  · exact d_core_check_1_14
  · exact d_core_check_1_15
  · exact d_core_check_1_16
  · exact d_core_check_1_17
  · exact d_core_check_1_18
  · exact d_core_check_1_19
  · exact d_core_check_1_20
  · exact d_core_check_1_21

theorem core_bounds1 : ThreeBoundMinmaxHybrid.CoreBounds 2795 18 (recipe 1) profile1 rawProfile1 := by
  constructor
  · intro i j hij
    exact (min_le_left _ _).trans (b_base_checked1 i j hij)
  · intro i j hij hj
    rcases m_choice_checked1 i j hij hj with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans h
  · exact p_core_checked1
  · exact d_core_checked1
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile ClosureCertificate




theorem aChoice_checked2 : ∀ i j : Fin 22, i≤ j →
    (aChoice2 i j)∈aSeeds2 ∧ i≤ (aChoice2 i j).1 ∧
    (aChoice2 i j).1≤ (aChoice2 i j).2 ∧ (aChoice2 i j).2≤ j ∧
    rawProfile2 (.a (aChoice2 i j).1 (aChoice2 i j).2)≤ rawProfile2 (.a i j):=by decide +kernel

theorem aCovers2 : ThreeBoundMinmaxHybrid.ACovers rawProfile2 aSeeds2:=by
  intro i j hij
  exact ⟨aChoice2 i j,aChoice_checked2 i j hij⟩
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_2_0 : ∀ j : Fin 22, (0 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 0) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 0 j) := by decide +kernel

theorem m_choice_check_2_0 : ∀ j : Fin 22, (0 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 0) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 0 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 0) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 0 j) := by decide +kernel

theorem p_core_check_2_0 : ∀ l : Fin 22, (0 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 0) (recipe 2 (next 0)) (recipe 2 l)
      (rawProfile2 (.a (next 0) l))≤ rawProfile2 (.p 0 l) := by decide +kernel

theorem d_core_check_2_0 : ∀ j l : Fin 22, (0 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 0) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 0 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 0 j l) := by decide +kernel

theorem b_base_check_2_1 : ∀ j : Fin 22, (1 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 1) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 1 j) := by decide +kernel

theorem m_choice_check_2_1 : ∀ j : Fin 22, (1 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 1) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 1 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 1) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 1 j) := by decide +kernel

theorem p_core_check_2_1 : ∀ l : Fin 22, (1 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 1) (recipe 2 (next 1)) (recipe 2 l)
      (rawProfile2 (.a (next 1) l))≤ rawProfile2 (.p 1 l) := by decide +kernel

theorem d_core_check_2_1 : ∀ j l : Fin 22, (1 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 1) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 1 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 1 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_2_2 : ∀ j : Fin 22, (2 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 2) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 2 j) := by decide +kernel

theorem m_choice_check_2_2 : ∀ j : Fin 22, (2 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 2) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 2 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 2) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 2 j) := by decide +kernel

theorem p_core_check_2_2 : ∀ l : Fin 22, (2 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 2) (recipe 2 (next 2)) (recipe 2 l)
      (rawProfile2 (.a (next 2) l))≤ rawProfile2 (.p 2 l) := by decide +kernel

theorem d_core_check_2_2 : ∀ j l : Fin 22, (2 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 2) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 2 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 2 j l) := by decide +kernel

theorem b_base_check_2_3 : ∀ j : Fin 22, (3 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 3) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 3 j) := by decide +kernel

theorem m_choice_check_2_3 : ∀ j : Fin 22, (3 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 3) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 3 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 3) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 3 j) := by decide +kernel

theorem p_core_check_2_3 : ∀ l : Fin 22, (3 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 3) (recipe 2 (next 3)) (recipe 2 l)
      (rawProfile2 (.a (next 3) l))≤ rawProfile2 (.p 3 l) := by decide +kernel

theorem d_core_check_2_3 : ∀ j l : Fin 22, (3 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 3) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 3 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 3 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_2_4 : ∀ j : Fin 22, (4 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 4) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 4 j) := by decide +kernel

theorem m_choice_check_2_4 : ∀ j : Fin 22, (4 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 4) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 4 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 4) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 4 j) := by decide +kernel

theorem p_core_check_2_4 : ∀ l : Fin 22, (4 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 4) (recipe 2 (next 4)) (recipe 2 l)
      (rawProfile2 (.a (next 4) l))≤ rawProfile2 (.p 4 l) := by decide +kernel

theorem d_core_check_2_4 : ∀ j l : Fin 22, (4 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 4) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 4 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 4 j l) := by decide +kernel

theorem b_base_check_2_5 : ∀ j : Fin 22, (5 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 5) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 5 j) := by decide +kernel

theorem m_choice_check_2_5 : ∀ j : Fin 22, (5 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 5) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 5 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 5) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 5 j) := by decide +kernel

theorem p_core_check_2_5 : ∀ l : Fin 22, (5 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 5) (recipe 2 (next 5)) (recipe 2 l)
      (rawProfile2 (.a (next 5) l))≤ rawProfile2 (.p 5 l) := by decide +kernel

theorem d_core_check_2_5 : ∀ j l : Fin 22, (5 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 5) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 5 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 5 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_2_6 : ∀ j : Fin 22, (6 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 6) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 6 j) := by decide +kernel

theorem m_choice_check_2_6 : ∀ j : Fin 22, (6 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 6) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 6 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 6) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 6 j) := by decide +kernel

theorem p_core_check_2_6 : ∀ l : Fin 22, (6 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 6) (recipe 2 (next 6)) (recipe 2 l)
      (rawProfile2 (.a (next 6) l))≤ rawProfile2 (.p 6 l) := by decide +kernel

theorem d_core_check_2_6 : ∀ j l : Fin 22, (6 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 6) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 6 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 6 j l) := by decide +kernel

theorem b_base_check_2_7 : ∀ j : Fin 22, (7 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 7) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 7 j) := by decide +kernel

theorem m_choice_check_2_7 : ∀ j : Fin 22, (7 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 7) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 7 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 7) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 7 j) := by decide +kernel

theorem p_core_check_2_7 : ∀ l : Fin 22, (7 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 7) (recipe 2 (next 7)) (recipe 2 l)
      (rawProfile2 (.a (next 7) l))≤ rawProfile2 (.p 7 l) := by decide +kernel

theorem d_core_check_2_7 : ∀ j l : Fin 22, (7 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 7) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 7 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 7 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_2_8 : ∀ j : Fin 22, (8 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 8) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 8 j) := by decide +kernel

theorem m_choice_check_2_8 : ∀ j : Fin 22, (8 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 8) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 8 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 8) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 8 j) := by decide +kernel

theorem p_core_check_2_8 : ∀ l : Fin 22, (8 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 8) (recipe 2 (next 8)) (recipe 2 l)
      (rawProfile2 (.a (next 8) l))≤ rawProfile2 (.p 8 l) := by decide +kernel

theorem d_core_check_2_8 : ∀ j l : Fin 22, (8 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 8) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 8 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 8 j l) := by decide +kernel

theorem b_base_check_2_9 : ∀ j : Fin 22, (9 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 9) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 9 j) := by decide +kernel

theorem m_choice_check_2_9 : ∀ j : Fin 22, (9 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 9) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 9 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 9) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 9 j) := by decide +kernel

theorem p_core_check_2_9 : ∀ l : Fin 22, (9 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 9) (recipe 2 (next 9)) (recipe 2 l)
      (rawProfile2 (.a (next 9) l))≤ rawProfile2 (.p 9 l) := by decide +kernel

theorem d_core_check_2_9 : ∀ j l : Fin 22, (9 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 9) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 9 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 9 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_2_10 : ∀ j : Fin 22, (10 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 10) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 10 j) := by decide +kernel

theorem m_choice_check_2_10 : ∀ j : Fin 22, (10 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 10) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 10 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 10) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 10 j) := by decide +kernel

theorem p_core_check_2_10 : ∀ l : Fin 22, (10 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 10) (recipe 2 (next 10)) (recipe 2 l)
      (rawProfile2 (.a (next 10) l))≤ rawProfile2 (.p 10 l) := by decide +kernel

theorem d_core_check_2_10 : ∀ j l : Fin 22, (10 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 10) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 10 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 10 j l) := by decide +kernel

theorem b_base_check_2_11 : ∀ j : Fin 22, (11 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 11) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 11 j) := by decide +kernel

theorem m_choice_check_2_11 : ∀ j : Fin 22, (11 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 11) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 11 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 11) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 11 j) := by decide +kernel

theorem p_core_check_2_11 : ∀ l : Fin 22, (11 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 11) (recipe 2 (next 11)) (recipe 2 l)
      (rawProfile2 (.a (next 11) l))≤ rawProfile2 (.p 11 l) := by decide +kernel

theorem d_core_check_2_11 : ∀ j l : Fin 22, (11 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 11) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 11 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 11 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_2_12 : ∀ j : Fin 22, (12 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 12) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 12 j) := by decide +kernel

theorem m_choice_check_2_12 : ∀ j : Fin 22, (12 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 12) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 12 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 12) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 12 j) := by decide +kernel

theorem p_core_check_2_12 : ∀ l : Fin 22, (12 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 12) (recipe 2 (next 12)) (recipe 2 l)
      (rawProfile2 (.a (next 12) l))≤ rawProfile2 (.p 12 l) := by decide +kernel

theorem d_core_check_2_12 : ∀ j l : Fin 22, (12 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 12) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 12 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 12 j l) := by decide +kernel

theorem b_base_check_2_13 : ∀ j : Fin 22, (13 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 13) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 13 j) := by decide +kernel

theorem m_choice_check_2_13 : ∀ j : Fin 22, (13 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 13) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 13 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 13) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 13 j) := by decide +kernel

theorem p_core_check_2_13 : ∀ l : Fin 22, (13 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 13) (recipe 2 (next 13)) (recipe 2 l)
      (rawProfile2 (.a (next 13) l))≤ rawProfile2 (.p 13 l) := by decide +kernel

theorem d_core_check_2_13 : ∀ j l : Fin 22, (13 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 13) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 13 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 13 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_2_14 : ∀ j : Fin 22, (14 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 14) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 14 j) := by decide +kernel

theorem m_choice_check_2_14 : ∀ j : Fin 22, (14 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 14) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 14 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 14) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 14 j) := by decide +kernel

theorem p_core_check_2_14 : ∀ l : Fin 22, (14 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 14) (recipe 2 (next 14)) (recipe 2 l)
      (rawProfile2 (.a (next 14) l))≤ rawProfile2 (.p 14 l) := by decide +kernel

theorem d_core_check_2_14 : ∀ j l : Fin 22, (14 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 14) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 14 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 14 j l) := by decide +kernel

theorem b_base_check_2_15 : ∀ j : Fin 22, (15 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 15) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 15 j) := by decide +kernel

theorem m_choice_check_2_15 : ∀ j : Fin 22, (15 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 15) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 15 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 15) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 15 j) := by decide +kernel

theorem p_core_check_2_15 : ∀ l : Fin 22, (15 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 15) (recipe 2 (next 15)) (recipe 2 l)
      (rawProfile2 (.a (next 15) l))≤ rawProfile2 (.p 15 l) := by decide +kernel

theorem d_core_check_2_15 : ∀ j l : Fin 22, (15 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 15) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 15 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 15 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_2_16 : ∀ j : Fin 22, (16 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 16) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 16 j) := by decide +kernel

theorem m_choice_check_2_16 : ∀ j : Fin 22, (16 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 16) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 16 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 16) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 16 j) := by decide +kernel

theorem p_core_check_2_16 : ∀ l : Fin 22, (16 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 16) (recipe 2 (next 16)) (recipe 2 l)
      (rawProfile2 (.a (next 16) l))≤ rawProfile2 (.p 16 l) := by decide +kernel

theorem d_core_check_2_16 : ∀ j l : Fin 22, (16 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 16) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 16 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 16 j l) := by decide +kernel

theorem b_base_check_2_17 : ∀ j : Fin 22, (17 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 17) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 17 j) := by decide +kernel

theorem m_choice_check_2_17 : ∀ j : Fin 22, (17 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 17) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 17 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 17) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 17 j) := by decide +kernel

theorem p_core_check_2_17 : ∀ l : Fin 22, (17 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 17) (recipe 2 (next 17)) (recipe 2 l)
      (rawProfile2 (.a (next 17) l))≤ rawProfile2 (.p 17 l) := by decide +kernel

theorem d_core_check_2_17 : ∀ j l : Fin 22, (17 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 17) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 17 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 17 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_2_18 : ∀ j : Fin 22, (18 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 18) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 18 j) := by decide +kernel

theorem m_choice_check_2_18 : ∀ j : Fin 22, (18 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 18) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 18 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 18) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 18 j) := by decide +kernel

theorem p_core_check_2_18 : ∀ l : Fin 22, (18 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 18) (recipe 2 (next 18)) (recipe 2 l)
      (rawProfile2 (.a (next 18) l))≤ rawProfile2 (.p 18 l) := by decide +kernel

theorem d_core_check_2_18 : ∀ j l : Fin 22, (18 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 18) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 18 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 18 j l) := by decide +kernel

theorem b_base_check_2_19 : ∀ j : Fin 22, (19 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 19) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 19 j) := by decide +kernel

theorem m_choice_check_2_19 : ∀ j : Fin 22, (19 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 19) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 19 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 19) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 19 j) := by decide +kernel

theorem p_core_check_2_19 : ∀ l : Fin 22, (19 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 19) (recipe 2 (next 19)) (recipe 2 l)
      (rawProfile2 (.a (next 19) l))≤ rawProfile2 (.p 19 l) := by decide +kernel

theorem d_core_check_2_19 : ∀ j l : Fin 22, (19 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 19) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 19 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 19 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_2_20 : ∀ j : Fin 22, (20 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 20) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 20 j) := by decide +kernel

theorem m_choice_check_2_20 : ∀ j : Fin 22, (20 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 20) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 20 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 20) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 20 j) := by decide +kernel

theorem p_core_check_2_20 : ∀ l : Fin 22, (20 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 20) (recipe 2 (next 20)) (recipe 2 l)
      (rawProfile2 (.a (next 20) l))≤ rawProfile2 (.p 20 l) := by decide +kernel

theorem d_core_check_2_20 : ∀ j l : Fin 22, (20 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 20) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 20 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 20 j l) := by decide +kernel

theorem b_base_check_2_21 : ∀ j : Fin 22, (21 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 21) (recipe 2 j)).eval profile2≤ rawProfile2 (.b 21 j) := by decide +kernel

theorem m_choice_check_2_21 : ∀ j : Fin 22, (21 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 21) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 21 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 21) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m 21 j) := by decide +kernel

theorem p_core_check_2_21 : ∀ l : Fin 22, (21 : Fin 22)< l →
    pCore 22 18 profile2 (recipe 2 21) (recipe 2 (next 21)) (recipe 2 l)
      (rawProfile2 (.a (next 21) l))≤ rawProfile2 (.p 21 l) := by decide +kernel

theorem d_core_check_2_21 : ∀ j l : Fin 22, (21 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 21) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 21 j)+rawProfile2 (.p j l))≤ rawProfile2 (.d 21 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_checked2 : ∀ i j : Fin 22, i≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 2 i) (recipe 2 j)).eval profile2≤ rawProfile2 (.b i j) := by
  intro i
  fin_cases i
  · exact b_base_check_2_0
  · exact b_base_check_2_1
  · exact b_base_check_2_2
  · exact b_base_check_2_3
  · exact b_base_check_2_4
  · exact b_base_check_2_5
  · exact b_base_check_2_6
  · exact b_base_check_2_7
  · exact b_base_check_2_8
  · exact b_base_check_2_9
  · exact b_base_check_2_10
  · exact b_base_check_2_11
  · exact b_base_check_2_12
  · exact b_base_check_2_13
  · exact b_base_check_2_14
  · exact b_base_check_2_15
  · exact b_base_check_2_16
  · exact b_base_check_2_17
  · exact b_base_check_2_18
  · exact b_base_check_2_19
  · exact b_base_check_2_20
  · exact b_base_check_2_21

theorem m_choice_checked2 : ∀ i j : Fin 22, i≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 2 i) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m i j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 2 i) (recipe 2 j) (recipe 2 (next j))).eval profile2≤ rawProfile2 (.m i j) := by
  intro i
  fin_cases i
  · exact m_choice_check_2_0
  · exact m_choice_check_2_1
  · exact m_choice_check_2_2
  · exact m_choice_check_2_3
  · exact m_choice_check_2_4
  · exact m_choice_check_2_5
  · exact m_choice_check_2_6
  · exact m_choice_check_2_7
  · exact m_choice_check_2_8
  · exact m_choice_check_2_9
  · exact m_choice_check_2_10
  · exact m_choice_check_2_11
  · exact m_choice_check_2_12
  · exact m_choice_check_2_13
  · exact m_choice_check_2_14
  · exact m_choice_check_2_15
  · exact m_choice_check_2_16
  · exact m_choice_check_2_17
  · exact m_choice_check_2_18
  · exact m_choice_check_2_19
  · exact m_choice_check_2_20
  · exact m_choice_check_2_21

theorem p_core_checked2 : ∀ j l : Fin 22, j< l →
    pCore 22 18 profile2 (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.a (next j) l))≤ rawProfile2 (.p j l) := by
  intro i
  fin_cases i
  · exact p_core_check_2_0
  · exact p_core_check_2_1
  · exact p_core_check_2_2
  · exact p_core_check_2_3
  · exact p_core_check_2_4
  · exact p_core_check_2_5
  · exact p_core_check_2_6
  · exact p_core_check_2_7
  · exact p_core_check_2_8
  · exact p_core_check_2_9
  · exact p_core_check_2_10
  · exact p_core_check_2_11
  · exact p_core_check_2_12
  · exact p_core_check_2_13
  · exact p_core_check_2_14
  · exact p_core_check_2_15
  · exact p_core_check_2_16
  · exact p_core_check_2_17
  · exact p_core_check_2_18
  · exact p_core_check_2_19
  · exact p_core_check_2_20
  · exact p_core_check_2_21

theorem d_core_checked2 : ∀ i j l : Fin 22, i≤ j → j< l →
    dCore 22 2795 profile2 (recipe 2 i) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m i j)+rawProfile2 (.p j l))≤ rawProfile2 (.d i j l) := by
  intro i
  fin_cases i
  · exact d_core_check_2_0
  · exact d_core_check_2_1
  · exact d_core_check_2_2
  · exact d_core_check_2_3
  · exact d_core_check_2_4
  · exact d_core_check_2_5
  · exact d_core_check_2_6
  · exact d_core_check_2_7
  · exact d_core_check_2_8
  · exact d_core_check_2_9
  · exact d_core_check_2_10
  · exact d_core_check_2_11
  · exact d_core_check_2_12
  · exact d_core_check_2_13
  · exact d_core_check_2_14
  · exact d_core_check_2_15
  · exact d_core_check_2_16
  · exact d_core_check_2_17
  · exact d_core_check_2_18
  · exact d_core_check_2_19
  · exact d_core_check_2_20
  · exact d_core_check_2_21

theorem core_bounds2 : ThreeBoundMinmaxHybrid.CoreBounds 2795 18 (recipe 2) profile2 rawProfile2 := by
  constructor
  · intro i j hij
    exact (min_le_left _ _).trans (b_base_checked2 i j hij)
  · intro i j hij hj
    rcases m_choice_checked2 i j hij hj with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans h
  · exact p_core_checked2
  · exact d_core_checked2
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile ClosureCertificate




theorem aChoice_checked3 : ∀ i j : Fin 22, i≤ j →
    (aChoice3 i j)∈aSeeds3 ∧ i≤ (aChoice3 i j).1 ∧
    (aChoice3 i j).1≤ (aChoice3 i j).2 ∧ (aChoice3 i j).2≤ j ∧
    rawProfile3 (.a (aChoice3 i j).1 (aChoice3 i j).2)≤ rawProfile3 (.a i j):=by decide +kernel

theorem aCovers3 : ThreeBoundMinmaxHybrid.ACovers rawProfile3 aSeeds3:=by
  intro i j hij
  exact ⟨aChoice3 i j,aChoice_checked3 i j hij⟩
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_3_0 : ∀ j : Fin 22, (0 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 0) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 0 j) := by decide +kernel

theorem m_choice_check_3_0 : ∀ j : Fin 22, (0 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 0) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 0 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 0) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 0 j) := by decide +kernel

theorem p_core_check_3_0 : ∀ l : Fin 22, (0 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 0) (recipe 3 (next 0)) (recipe 3 l)
      (rawProfile3 (.a (next 0) l))≤ rawProfile3 (.p 0 l) := by decide +kernel

theorem d_core_check_3_0 : ∀ j l : Fin 22, (0 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 0) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 0 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 0 j l) := by decide +kernel

theorem b_base_check_3_1 : ∀ j : Fin 22, (1 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 1) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 1 j) := by decide +kernel

theorem m_choice_check_3_1 : ∀ j : Fin 22, (1 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 1) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 1 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 1) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 1 j) := by decide +kernel

theorem p_core_check_3_1 : ∀ l : Fin 22, (1 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 1) (recipe 3 (next 1)) (recipe 3 l)
      (rawProfile3 (.a (next 1) l))≤ rawProfile3 (.p 1 l) := by decide +kernel

theorem d_core_check_3_1 : ∀ j l : Fin 22, (1 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 1) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 1 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 1 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_3_2 : ∀ j : Fin 22, (2 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 2) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 2 j) := by decide +kernel

theorem m_choice_check_3_2 : ∀ j : Fin 22, (2 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 2) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 2 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 2) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 2 j) := by decide +kernel

theorem p_core_check_3_2 : ∀ l : Fin 22, (2 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 2) (recipe 3 (next 2)) (recipe 3 l)
      (rawProfile3 (.a (next 2) l))≤ rawProfile3 (.p 2 l) := by decide +kernel

theorem d_core_check_3_2 : ∀ j l : Fin 22, (2 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 2) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 2 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 2 j l) := by decide +kernel

theorem b_base_check_3_3 : ∀ j : Fin 22, (3 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 3) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 3 j) := by decide +kernel

theorem m_choice_check_3_3 : ∀ j : Fin 22, (3 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 3) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 3 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 3) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 3 j) := by decide +kernel

theorem p_core_check_3_3 : ∀ l : Fin 22, (3 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 3) (recipe 3 (next 3)) (recipe 3 l)
      (rawProfile3 (.a (next 3) l))≤ rawProfile3 (.p 3 l) := by decide +kernel

theorem d_core_check_3_3 : ∀ j l : Fin 22, (3 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 3) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 3 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 3 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_3_4 : ∀ j : Fin 22, (4 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 4) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 4 j) := by decide +kernel

theorem m_choice_check_3_4 : ∀ j : Fin 22, (4 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 4) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 4 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 4) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 4 j) := by decide +kernel

theorem p_core_check_3_4 : ∀ l : Fin 22, (4 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 4) (recipe 3 (next 4)) (recipe 3 l)
      (rawProfile3 (.a (next 4) l))≤ rawProfile3 (.p 4 l) := by decide +kernel

theorem d_core_check_3_4 : ∀ j l : Fin 22, (4 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 4) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 4 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 4 j l) := by decide +kernel

theorem b_base_check_3_5 : ∀ j : Fin 22, (5 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 5) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 5 j) := by decide +kernel

theorem m_choice_check_3_5 : ∀ j : Fin 22, (5 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 5) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 5 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 5) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 5 j) := by decide +kernel

theorem p_core_check_3_5 : ∀ l : Fin 22, (5 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 5) (recipe 3 (next 5)) (recipe 3 l)
      (rawProfile3 (.a (next 5) l))≤ rawProfile3 (.p 5 l) := by decide +kernel

theorem d_core_check_3_5 : ∀ j l : Fin 22, (5 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 5) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 5 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 5 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_3_6 : ∀ j : Fin 22, (6 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 6) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 6 j) := by decide +kernel

theorem m_choice_check_3_6 : ∀ j : Fin 22, (6 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 6) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 6 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 6) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 6 j) := by decide +kernel

theorem p_core_check_3_6 : ∀ l : Fin 22, (6 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 6) (recipe 3 (next 6)) (recipe 3 l)
      (rawProfile3 (.a (next 6) l))≤ rawProfile3 (.p 6 l) := by decide +kernel

theorem d_core_check_3_6 : ∀ j l : Fin 22, (6 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 6) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 6 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 6 j l) := by decide +kernel

theorem b_base_check_3_7 : ∀ j : Fin 22, (7 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 7) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 7 j) := by decide +kernel

theorem m_choice_check_3_7 : ∀ j : Fin 22, (7 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 7) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 7 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 7) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 7 j) := by decide +kernel

theorem p_core_check_3_7 : ∀ l : Fin 22, (7 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 7) (recipe 3 (next 7)) (recipe 3 l)
      (rawProfile3 (.a (next 7) l))≤ rawProfile3 (.p 7 l) := by decide +kernel

theorem d_core_check_3_7 : ∀ j l : Fin 22, (7 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 7) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 7 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 7 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_3_8 : ∀ j : Fin 22, (8 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 8) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 8 j) := by decide +kernel

theorem m_choice_check_3_8 : ∀ j : Fin 22, (8 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 8) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 8 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 8) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 8 j) := by decide +kernel

theorem p_core_check_3_8 : ∀ l : Fin 22, (8 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 8) (recipe 3 (next 8)) (recipe 3 l)
      (rawProfile3 (.a (next 8) l))≤ rawProfile3 (.p 8 l) := by decide +kernel

theorem d_core_check_3_8 : ∀ j l : Fin 22, (8 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 8) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 8 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 8 j l) := by decide +kernel

theorem b_base_check_3_9 : ∀ j : Fin 22, (9 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 9) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 9 j) := by decide +kernel

theorem m_choice_check_3_9 : ∀ j : Fin 22, (9 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 9) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 9 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 9) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 9 j) := by decide +kernel

theorem p_core_check_3_9 : ∀ l : Fin 22, (9 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 9) (recipe 3 (next 9)) (recipe 3 l)
      (rawProfile3 (.a (next 9) l))≤ rawProfile3 (.p 9 l) := by decide +kernel

theorem d_core_check_3_9 : ∀ j l : Fin 22, (9 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 9) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 9 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 9 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_3_10 : ∀ j : Fin 22, (10 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 10) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 10 j) := by decide +kernel

theorem m_choice_check_3_10 : ∀ j : Fin 22, (10 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 10) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 10 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 10) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 10 j) := by decide +kernel

theorem p_core_check_3_10 : ∀ l : Fin 22, (10 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 10) (recipe 3 (next 10)) (recipe 3 l)
      (rawProfile3 (.a (next 10) l))≤ rawProfile3 (.p 10 l) := by decide +kernel

theorem d_core_check_3_10 : ∀ j l : Fin 22, (10 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 10) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 10 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 10 j l) := by decide +kernel

theorem b_base_check_3_11 : ∀ j : Fin 22, (11 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 11) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 11 j) := by decide +kernel

theorem m_choice_check_3_11 : ∀ j : Fin 22, (11 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 11) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 11 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 11) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 11 j) := by decide +kernel

theorem p_core_check_3_11 : ∀ l : Fin 22, (11 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 11) (recipe 3 (next 11)) (recipe 3 l)
      (rawProfile3 (.a (next 11) l))≤ rawProfile3 (.p 11 l) := by decide +kernel

theorem d_core_check_3_11 : ∀ j l : Fin 22, (11 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 11) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 11 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 11 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_3_12 : ∀ j : Fin 22, (12 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 12) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 12 j) := by decide +kernel

theorem m_choice_check_3_12 : ∀ j : Fin 22, (12 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 12) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 12 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 12) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 12 j) := by decide +kernel

theorem p_core_check_3_12 : ∀ l : Fin 22, (12 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 12) (recipe 3 (next 12)) (recipe 3 l)
      (rawProfile3 (.a (next 12) l))≤ rawProfile3 (.p 12 l) := by decide +kernel

theorem d_core_check_3_12 : ∀ j l : Fin 22, (12 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 12) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 12 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 12 j l) := by decide +kernel

theorem b_base_check_3_13 : ∀ j : Fin 22, (13 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 13) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 13 j) := by decide +kernel

theorem m_choice_check_3_13 : ∀ j : Fin 22, (13 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 13) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 13 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 13) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 13 j) := by decide +kernel

theorem p_core_check_3_13 : ∀ l : Fin 22, (13 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 13) (recipe 3 (next 13)) (recipe 3 l)
      (rawProfile3 (.a (next 13) l))≤ rawProfile3 (.p 13 l) := by decide +kernel

theorem d_core_check_3_13 : ∀ j l : Fin 22, (13 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 13) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 13 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 13 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_3_14 : ∀ j : Fin 22, (14 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 14) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 14 j) := by decide +kernel

theorem m_choice_check_3_14 : ∀ j : Fin 22, (14 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 14) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 14 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 14) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 14 j) := by decide +kernel

theorem p_core_check_3_14 : ∀ l : Fin 22, (14 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 14) (recipe 3 (next 14)) (recipe 3 l)
      (rawProfile3 (.a (next 14) l))≤ rawProfile3 (.p 14 l) := by decide +kernel

theorem d_core_check_3_14 : ∀ j l : Fin 22, (14 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 14) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 14 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 14 j l) := by decide +kernel

theorem b_base_check_3_15 : ∀ j : Fin 22, (15 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 15) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 15 j) := by decide +kernel

theorem m_choice_check_3_15 : ∀ j : Fin 22, (15 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 15) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 15 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 15) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 15 j) := by decide +kernel

theorem p_core_check_3_15 : ∀ l : Fin 22, (15 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 15) (recipe 3 (next 15)) (recipe 3 l)
      (rawProfile3 (.a (next 15) l))≤ rawProfile3 (.p 15 l) := by decide +kernel

theorem d_core_check_3_15 : ∀ j l : Fin 22, (15 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 15) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 15 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 15 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_3_16 : ∀ j : Fin 22, (16 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 16) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 16 j) := by decide +kernel

theorem m_choice_check_3_16 : ∀ j : Fin 22, (16 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 16) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 16 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 16) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 16 j) := by decide +kernel

theorem p_core_check_3_16 : ∀ l : Fin 22, (16 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 16) (recipe 3 (next 16)) (recipe 3 l)
      (rawProfile3 (.a (next 16) l))≤ rawProfile3 (.p 16 l) := by decide +kernel

theorem d_core_check_3_16 : ∀ j l : Fin 22, (16 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 16) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 16 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 16 j l) := by decide +kernel

theorem b_base_check_3_17 : ∀ j : Fin 22, (17 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 17) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 17 j) := by decide +kernel

theorem m_choice_check_3_17 : ∀ j : Fin 22, (17 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 17) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 17 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 17) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 17 j) := by decide +kernel

theorem p_core_check_3_17 : ∀ l : Fin 22, (17 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 17) (recipe 3 (next 17)) (recipe 3 l)
      (rawProfile3 (.a (next 17) l))≤ rawProfile3 (.p 17 l) := by decide +kernel

theorem d_core_check_3_17 : ∀ j l : Fin 22, (17 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 17) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 17 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 17 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_3_18 : ∀ j : Fin 22, (18 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 18) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 18 j) := by decide +kernel

theorem m_choice_check_3_18 : ∀ j : Fin 22, (18 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 18) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 18 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 18) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 18 j) := by decide +kernel

theorem p_core_check_3_18 : ∀ l : Fin 22, (18 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 18) (recipe 3 (next 18)) (recipe 3 l)
      (rawProfile3 (.a (next 18) l))≤ rawProfile3 (.p 18 l) := by decide +kernel

theorem d_core_check_3_18 : ∀ j l : Fin 22, (18 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 18) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 18 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 18 j l) := by decide +kernel

theorem b_base_check_3_19 : ∀ j : Fin 22, (19 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 19) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 19 j) := by decide +kernel

theorem m_choice_check_3_19 : ∀ j : Fin 22, (19 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 19) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 19 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 19) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 19 j) := by decide +kernel

theorem p_core_check_3_19 : ∀ l : Fin 22, (19 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 19) (recipe 3 (next 19)) (recipe 3 l)
      (rawProfile3 (.a (next 19) l))≤ rawProfile3 (.p 19 l) := by decide +kernel

theorem d_core_check_3_19 : ∀ j l : Fin 22, (19 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 19) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 19 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 19 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_check_3_20 : ∀ j : Fin 22, (20 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 20) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 20 j) := by decide +kernel

theorem m_choice_check_3_20 : ∀ j : Fin 22, (20 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 20) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 20 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 20) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 20 j) := by decide +kernel

theorem p_core_check_3_20 : ∀ l : Fin 22, (20 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 20) (recipe 3 (next 20)) (recipe 3 l)
      (rawProfile3 (.a (next 20) l))≤ rawProfile3 (.p 20 l) := by decide +kernel

theorem d_core_check_3_20 : ∀ j l : Fin 22, (20 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 20) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 20 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 20 j l) := by decide +kernel

theorem b_base_check_3_21 : ∀ j : Fin 22, (21 : Fin 22)≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 21) (recipe 3 j)).eval profile3≤ rawProfile3 (.b 21 j) := by decide +kernel

theorem m_choice_check_3_21 : ∀ j : Fin 22, (21 : Fin 22)≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 21) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 21 j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 21) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m 21 j) := by decide +kernel

theorem p_core_check_3_21 : ∀ l : Fin 22, (21 : Fin 22)< l →
    pCore 22 18 profile3 (recipe 3 21) (recipe 3 (next 21)) (recipe 3 l)
      (rawProfile3 (.a (next 21) l))≤ rawProfile3 (.p 21 l) := by decide +kernel

theorem d_core_check_3_21 : ∀ j l : Fin 22, (21 : Fin 22)≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 21) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 21 j)+rawProfile3 (.p j l))≤ rawProfile3 (.d 21 j l) := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile
theorem b_base_checked3 : ∀ i j : Fin 22, i≤ j →
    (ThreeBoundMinmaxNumeric.rawBExpr 22 2795 (recipe 3 i) (recipe 3 j)).eval profile3≤ rawProfile3 (.b i j) := by
  intro i
  fin_cases i
  · exact b_base_check_3_0
  · exact b_base_check_3_1
  · exact b_base_check_3_2
  · exact b_base_check_3_3
  · exact b_base_check_3_4
  · exact b_base_check_3_5
  · exact b_base_check_3_6
  · exact b_base_check_3_7
  · exact b_base_check_3_8
  · exact b_base_check_3_9
  · exact b_base_check_3_10
  · exact b_base_check_3_11
  · exact b_base_check_3_12
  · exact b_base_check_3_13
  · exact b_base_check_3_14
  · exact b_base_check_3_15
  · exact b_base_check_3_16
  · exact b_base_check_3_17
  · exact b_base_check_3_18
  · exact b_base_check_3_19
  · exact b_base_check_3_20
  · exact b_base_check_3_21

theorem m_choice_checked3 : ∀ i j : Fin 22, i≤ j → j.val+1< 22 →
    (ThreeBoundMinmaxNumeric.rawMExpr 22 2795 (recipe 3 i) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m i j) ∨
    (ThreeBoundMinmaxRank.rawMExpr 22 2795 (recipe 3 i) (recipe 3 j) (recipe 3 (next j))).eval profile3≤ rawProfile3 (.m i j) := by
  intro i
  fin_cases i
  · exact m_choice_check_3_0
  · exact m_choice_check_3_1
  · exact m_choice_check_3_2
  · exact m_choice_check_3_3
  · exact m_choice_check_3_4
  · exact m_choice_check_3_5
  · exact m_choice_check_3_6
  · exact m_choice_check_3_7
  · exact m_choice_check_3_8
  · exact m_choice_check_3_9
  · exact m_choice_check_3_10
  · exact m_choice_check_3_11
  · exact m_choice_check_3_12
  · exact m_choice_check_3_13
  · exact m_choice_check_3_14
  · exact m_choice_check_3_15
  · exact m_choice_check_3_16
  · exact m_choice_check_3_17
  · exact m_choice_check_3_18
  · exact m_choice_check_3_19
  · exact m_choice_check_3_20
  · exact m_choice_check_3_21

theorem p_core_checked3 : ∀ j l : Fin 22, j< l →
    pCore 22 18 profile3 (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.a (next j) l))≤ rawProfile3 (.p j l) := by
  intro i
  fin_cases i
  · exact p_core_check_3_0
  · exact p_core_check_3_1
  · exact p_core_check_3_2
  · exact p_core_check_3_3
  · exact p_core_check_3_4
  · exact p_core_check_3_5
  · exact p_core_check_3_6
  · exact p_core_check_3_7
  · exact p_core_check_3_8
  · exact p_core_check_3_9
  · exact p_core_check_3_10
  · exact p_core_check_3_11
  · exact p_core_check_3_12
  · exact p_core_check_3_13
  · exact p_core_check_3_14
  · exact p_core_check_3_15
  · exact p_core_check_3_16
  · exact p_core_check_3_17
  · exact p_core_check_3_18
  · exact p_core_check_3_19
  · exact p_core_check_3_20
  · exact p_core_check_3_21

theorem d_core_checked3 : ∀ i j l : Fin 22, i≤ j → j< l →
    dCore 22 2795 profile3 (recipe 3 i) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m i j)+rawProfile3 (.p j l))≤ rawProfile3 (.d i j l) := by
  intro i
  fin_cases i
  · exact d_core_check_3_0
  · exact d_core_check_3_1
  · exact d_core_check_3_2
  · exact d_core_check_3_3
  · exact d_core_check_3_4
  · exact d_core_check_3_5
  · exact d_core_check_3_6
  · exact d_core_check_3_7
  · exact d_core_check_3_8
  · exact d_core_check_3_9
  · exact d_core_check_3_10
  · exact d_core_check_3_11
  · exact d_core_check_3_12
  · exact d_core_check_3_13
  · exact d_core_check_3_14
  · exact d_core_check_3_15
  · exact d_core_check_3_16
  · exact d_core_check_3_17
  · exact d_core_check_3_18
  · exact d_core_check_3_19
  · exact d_core_check_3_20
  · exact d_core_check_3_21

theorem core_bounds3 : ThreeBoundMinmaxHybrid.CoreBounds 2795 18 (recipe 3) profile3 rawProfile3 := by
  constructor
  · intro i j hij
    exact (min_le_left _ _).trans (b_base_checked3 i j hij)
  · intro i j hij hj
    rcases m_choice_checked3 i j hij hj with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans h
  · exact p_core_checked3
  · exact d_core_checked3
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records



theorem numerical_complete : HybridNumericalBounds records essentialSeeds := by
  intro p
  fin_cases p
  · exact ⟨aCovers0,seed_bounds0,core_bounds0⟩
  · exact ⟨aCovers1,seed_bounds1,core_bounds1⟩
  · exact ⟨aCovers2,seed_bounds2,core_bounds2⟩
  · exact ⟨aCovers3,seed_bounds3,core_bounds3⟩
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.HybridNumericalBounds
  Sensitivity213981Formal.ThreeBoundEndpoint22Records.records
  Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.essentialSeeds := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.numerical_complete
