-- Prove2me | solution 1 for WeierstrassCurve.hasseInvariant_tatePowerSeries_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8c132006-5853-5c3f-a9fd-3d762b294be6

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_TateOrigin
import Theorems.Thm_WeierstrassCurve_coeff_invariantDifferential_eq_hasseInvariant
import Theorems.Thm_ModularCurve_one_add_single_mul_derivative_tateOriginX
import Theorems.Thm_ModularCurve_tateOrigin_equation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_hasseInvariant_tatePowerSeries_map
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

open HahnSeries ModularCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "a₃ a₁ map mk a₄ a₂ a₆ hasseInvariant coeff_invariantDifferential_eq_hasseInvariant"
namespace HTasm
p2m_open "WeierstrassCurve"

theorem main (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    WeierstrassCurve.hasseInvariant q (ModularCurve.tatePowerSeries.map (PowerSeries.map (Int.castRingHom (ZMod q)))) = 1 := by
  have hp : q.Prime := Fact.out
  haveI : CharP (PowerSeries (ZMod q)) q := by
    refine charP_of_injective_ringHom (f := PowerSeries.C (R := ZMod q)) ?_ q
    intro a b h
    have := congrArg PowerSeries.constantCoeff h
    simpa using this
  set W : WeierstrassCurve (PowerSeries (ZMod q)) := ModularCurve.tatePowerSeries.map (PowerSeries.map (Int.castRingHom (ZMod q))) with hW
  have ha₁ : W.a₁ = 1 := by simp [hW, WeierstrassCurve.map]
  have ha₂ : W.a₂ = 0 := by simp [hW, WeierstrassCurve.map]
  have ha₃ : W.a₃ = 0 := by simp [hW, WeierstrassCurve.map]
  have ha₄ : W.a₄ = PowerSeries.map (Int.castRingHom (ZMod q)) tateA4 := by simp [hW, WeierstrassCurve.map]
  have ha₆ : W.a₆ = PowerSeries.map (Int.castRingHom (ZMod q)) tateA6 := by simp [hW, WeierstrassCurve.map]
  set x := tateOriginX (ZMod q) with hx
  set y := tateOriginY (ZMod q) with hy

  set p : PowerSeries (PowerSeries (ZMod q)) := PowerSeries.mk fun k => (-1 : PowerSeries (ZMod q)) ^ k with hpdef
  set ω : LaurentSeries (PowerSeries (ZMod q)) := HahnSeries.ofPowerSeries ℤ (PowerSeries (ZMod q)) p with hω
  have hp1 : (1 + PowerSeries.X) * p = 1 := by
    ext n
    rw [add_mul, one_mul, map_add, PowerSeries.coeff_one]
    cases n with
    | zero => simp [hpdef]
    | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, hpdef, PowerSeries.coeff_mk, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n), pow_succ]
      ring
  have hωT : ω * (1 + HahnSeries.single (1 : ℤ) (1 : PowerSeries (ZMod q))) = 1 := by
    rw [hω, ← HahnSeries.ofPowerSeries_X, ← RingHom.map_one (HahnSeries.ofPowerSeries ℤ (PowerSeries (ZMod q))), ← map_add, ← map_mul, mul_comm, hp1]

  have heq : y ^ 2 + HahnSeries.C W.a₁ * x * y + HahnSeries.C W.a₃ * y
      = x ^ 3 + HahnSeries.C W.a₂ * x ^ 2 + HahnSeries.C W.a₄ * x + HahnSeries.C W.a₆ := by
    rw [ha₁, ha₂, ha₃, ha₄, ha₆, map_one, map_zero]
    have h := tateOrigin_equation (ZMod q)
    rw [← hx, ← hy] at h
    linear_combination h
  have hωeq : ω * (2 * y + HahnSeries.C W.a₁ * x + HahnSeries.C W.a₃) = LaurentSeries.derivative (PowerSeries (ZMod q)) x := by
    rw [ha₁, ha₃, map_one, map_zero, one_mul, add_zero, ← one_add_single_mul_derivative_tateOriginX (ZMod q), ← hx,
      ← mul_assoc, hωT, one_mul]
  have hK := coeff_invariantDifferential_eq_hasseInvariant q hq W x y ω heq
    (coeff_tateOriginX_neg_two (ZMod q)) (fun n hn => coeff_tateOriginX_of_lt (ZMod q) hn)
    (coeff_tateOriginY_neg_three (ZMod q)) (fun n hn => coeff_tateOriginY_of_lt (ZMod q) hn) hωeq
  have hq1 : 1 ≤ q := hp.one_lt.le
  rw [← hK, hω, show ((q : ℤ) - 1) = ((q - 1 : ℕ) : ℤ) by omega, HahnSeries.ofPowerSeries_apply_coeff, hpdef,
    PowerSeries.coeff_mk, (hp.even_sub_one hq).neg_one_pow]

end WeierstrassCurve.HTasm

theorem solution (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    WeierstrassCurve.hasseInvariant q (ModularCurve.tatePowerSeries.map (PowerSeries.map (Int.castRingHom (ZMod q)))) = 1 :=
  WeierstrassCurve.HTasm.main q hq

end S_WeierstrassCurve_hasseInvariant_tatePowerSeries_map
end P2MW
export P2MW.S_WeierstrassCurve_hasseInvariant_tatePowerSeries_map (solution)
