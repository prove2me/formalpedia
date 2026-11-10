-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.six_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:43:08.370123+00:00
-- url     : https://prove2.me/submissions/c87ea98e-1569-498c-a199-3cff26ac754f

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19PrimeQuditCSS
theorem _root_.solution (p : Nat) [NeZero p] (hp : PrimeAtLeastFive p) :
    (6 : ZMod p) ≠ 0 := by
  intro hzero
  have hfive : 5 ≤ p := hp.five_le
  have hp_dvd : p ∣ 6 := (ZMod.natCast_eq_zero_iff 6 p).mp (by simpa using hzero)
  rw [show 6 = 2 * 3 by norm_num] at hp_dvd
  rcases hp.prime.dvd_mul.mp hp_dvd with hp_two | hp_three
  · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_two
    omega
  · have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hp_three
    omega
end QEC.Distillation.KT19PrimeQuditCSS
