-- Prove2me | solution 1 for WeierstrassCurve.Affine.valuation_weilNum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1a0848cc-b9b4-5d49-a82d-80181e2da33a

import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Definitions.Def_EllipticCurve_WeilPairingFun
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isPrincipal_prod_XYIdeal_zpow_iff
import Theorems.Thm_WeierstrassCurve_sum_eq_zero_of_forall_mem_iff_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_Affine_fibSet_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_valuation_weilNum
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors

namespace WeilDiv

variable {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]
  (W : WeierstrassCurve F) [W.IsElliptic]

theorem torsion_finite {n : ℕ} (hn : (n : K) ≠ 0) :
    {S : (W⁄K).Point | (n : ℤ) • S = 0}.Finite := by
  have hcard := WeierstrassCurve.card_torsion_of_isAlgClosed (K := K) W hn
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  haveI : Finite (Submodule.torsionBy ℤ (W⁄K).Point n) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hn0)
  have hset : {S : (W⁄K).Point | (n : ℤ) • S = 0} =
      ((Submodule.torsionBy ℤ (W⁄K).Point n : Submodule ℤ (W⁄K).Point) : Set (W⁄K).Point) := by
    ext S
    rw [Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_torsionBy_iff]
  rw [hset]
  exact Set.toFinite _

theorem card_torsion_toFinset {n : ℕ} (hn : (n : K) ≠ 0) :
    (torsion_finite W hn).toFinset.card = n ^ 2 := by
  rw [← WeierstrassCurve.card_torsion_of_isAlgClosed (K := K) W hn, ← Nat.card_eq_card_finite_toFinset]
  have hset : {S : (W⁄K).Point | (n : ℤ) • S = 0} =
      ((Submodule.torsionBy ℤ (W⁄K).Point n : Submodule ℤ (W⁄K).Point) : Set (W⁄K).Point) := by
    ext S
    rw [Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_torsionBy_iff]
  rw [hset]
  rfl

theorem sum_fibSet_eq_zero {n : ℕ} (hn : (n : K) ≠ 0) {T : (W⁄K).Point} (hT : (n : ℤ) • T = 0) :
    ∑ P ∈ (WeierstrassCurve.Affine.fibSet_finite W hn T).toFinset, P = 0 := by
  classical
  set s := (WeierstrassCurve.Affine.fibSet_finite W hn T).toFinset with hs
  by_cases hne : ∃ P₀ : (W⁄K).Point, (n : ℤ) • P₀ = T
  · obtain ⟨P₀, hP₀⟩ := hne
    set t := (torsion_finite W hn).toFinset with ht
    have hts : s = t.image (· + P₀) := by
      ext P
      simp only [hs, ht, Set.Finite.mem_toFinset, mem_fibSet, Finset.mem_image, Set.mem_setOf_eq]
      constructor
      · intro hP
        exact ⟨P - P₀, by rw [smul_sub, hP, hP₀, sub_self], sub_add_cancel P P₀⟩
      · rintro ⟨S, hS, rfl⟩
        rw [smul_add, hS, hP₀, zero_add]
    rw [hts, Finset.sum_image (fun a _ b _ h => add_right_cancel h), Finset.sum_add_distrib,
      Finset.sum_const, card_torsion_toFinset W hn,
      WeierstrassCurve.sum_eq_zero_of_forall_mem_iff_smul_eq_zero W hn t ?_, zero_add]
    · rw [pow_two, mul_nsmul', ← natCast_zsmul P₀, hP₀, ← natCast_zsmul T, hT]
    · intro P
      rw [ht, Set.Finite.mem_toFinset, Set.mem_setOf_eq, natCast_zsmul]
  · have h0 : s = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro P hP
      rw [hs, Set.Finite.mem_toFinset, mem_fibSet] at hP
      exact hne ⟨P, hP⟩
    rw [h0, Finset.sum_empty]

variable [IsDedekindDomain (W⁄K).CoordinateRing]

omit [IsAlgClosed K] [W.IsElliptic] in

theorem intValuation_of_span_eq_prod (s : Finset (W⁄K).Point) {r : (W⁄K).CoordinateRing}
    (hr : Ideal.span {r} = ∏ P ∈ s, placeIdeal W K P) (P₁ : (W⁄K).Point) (hP₁ : P₁ ≠ 0) :
    (placeOf W K P₁ hP₁).intValuation r = if P₁ ∈ s then exp (-1) else 1 := by
  classical
  set v := placeOf W K P₁ hP₁ with hv
  have hI0 : ∀ P ∈ s, placeIdeal W K P ≠ 0 := by
    intro P _ h0
    by_cases hP : P = 0
    · rw [hP, placeIdeal_zero, Ideal.zero_eq_bot] at h0
      exact top_ne_bot h0
    · rw [placeIdeal_of_ne_zero W K hP, Ideal.zero_eq_bot] at h0
      exact (placeOf W K P hP).ne_bot h0
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, Ideal.span_singleton_eq_bot.mpr rfl, eq_comm, ← Ideal.zero_eq_bot,
      Finset.prod_eq_zero_iff] at hr
    obtain ⟨P, hP, h0⟩ := hr
    exact hI0 P hP h0

  have hle : ∀ P ∈ s, placeIdeal W K P ≤ v.asIdeal → P = P₁ := by
    intro P _ hPle
    by_cases hP0 : P = 0
    · exfalso
      rw [hP0, placeIdeal_zero, top_le_iff] at hPle
      exact v.isPrime.ne_top hPle
    · rw [placeIdeal_of_ne_zero W K hP0] at hPle
      have heq : (placeOf W K P hP0).asIdeal = v.asIdeal :=
        (placeOf W K P hP0).isMaximal.eq_of_le v.isPrime.ne_top hPle
      exact placeOf_injective W K hP0 hP₁ (HeightOneSpectrum.ext heq)
  by_cases hmem : P₁ ∈ s
  · rw [if_pos hmem]
    have hsplit := Finset.prod_eq_mul_prod_diff_singleton_of_mem hmem (fun P => placeIdeal W K P)
    have hmem1 : r ∈ v.asIdeal ^ 1 := by
      rw [pow_one, ← Ideal.span_singleton_le_iff_mem, hr, hsplit, hv, ← placeIdeal_of_ne_zero W K hP₁]
      exact Ideal.mul_le_left
    have hnot2 : r ∉ v.asIdeal ^ 2 := by
      intro h2
      rw [← Ideal.dvd_span_singleton, hr, hsplit, placeIdeal_of_ne_zero W K hP₁, ← hv, sq] at h2
      have h3 : v.asIdeal ∣ ∏ P ∈ s \ {P₁}, placeIdeal W K P :=
        (mul_dvd_mul_iff_left v.ne_bot).mp h2
      rw [Ideal.dvd_iff_le] at h3
      obtain ⟨P, hPs, hPle⟩ := (Ideal.IsPrime.prod_le v.isPrime).mp h3
      have hPP := hle P (Finset.mem_sdiff.mp hPs).1 hPle
      exact (Finset.mem_sdiff.mp hPs).2 (Finset.mem_singleton.mpr hPP)
    have hle1 : v.intValuation r ≤ exp (-((1 : ℕ) : ℤ)) := (intValuation_le_pow_iff_mem v r 1).mpr hmem1
    have hgt2 : ¬ v.intValuation r ≤ exp (-((2 : ℕ) : ℤ)) := fun h =>
      hnot2 ((intValuation_le_pow_iff_mem v r 2).mp h)
    obtain ⟨z, hz⟩ : ∃ z : ℤ, v.intValuation r = exp z :=
      ⟨_, (exp_log (intValuation_ne_zero v r hr0)).symm⟩
    rw [hz] at hle1 hgt2 ⊢
    rw [exp_le_exp] at hle1 hgt2
    push_cast at hle1 hgt2
    congr 1
    omega
  · rw [if_neg hmem, intValuation_eq_one_iff]
    intro hrv
    rw [← Ideal.span_singleton_le_iff_mem, hr] at hrv
    obtain ⟨P, hPs, hPle⟩ := (Ideal.IsPrime.prod_le v.isPrime).mp hrv
    exact hmem (hle P hPs hPle ▸ hPs)

theorem fibIdeal_isPrincipal {n : ℕ} (hn : (n : K) ≠ 0) {T : (W⁄K).Point}
    (hT : (n : ℤ) • T = 0) : (fibIdeal W K n T).IsPrincipal := by
  classical
  have hfin := fibSet_finite W hn T
  rw [fibIdeal_eq W K hfin]
  set s := hfin.toFinset with hs
  let s' : Finset {P : (W⁄K).Point // P ≠ 0} := s.subtype (· ≠ 0)

  have hprod1 : (∏ P ∈ s, placeIdeal W K P) = ∏ i ∈ s', placeIdeal W K i.1 := by
    rw [Finset.prod_subtype_eq_prod_filter, Finset.prod_filter_of_ne]
    intro P _ hP1 hP0
    exact hP1 (by rw [hP0, placeIdeal_zero, Ideal.one_eq_top])
  have key := (WeierstrassCurve.Affine.CoordinateRing.isPrincipal_prod_XYIdeal_zpow_iff (W := W⁄K) s'
    (fun i => i.1.xc) (fun i => i.1.yc) (fun i => Point.nonsingular_xc_yc i.2) (fun _ => 1)).mpr ?_
  · have hcoe : ((∏ i ∈ s', CoordinateRing.XYIdeal' (Point.nonsingular_xc_yc i.2) ^ (1 : ℤ) :
        (FractionalIdeal (W⁄K).CoordinateRing⁰ (W⁄K).FunctionField)ˣ) :
        FractionalIdeal (W⁄K).CoordinateRing⁰ (W⁄K).FunctionField) =
        ((∏ P ∈ s, placeIdeal W K P : Ideal (W⁄K).CoordinateRing) :
          FractionalIdeal (W⁄K).CoordinateRing⁰ (W⁄K).FunctionField) := by
      rw [Units.coe_prod, hprod1]
      have hmap := map_prod (FractionalIdeal.coeIdealHom (W⁄K).CoordinateRing⁰ (W⁄K).FunctionField)
        (fun i : {P : (W⁄K).Point // P ≠ 0} => placeIdeal W K i.1) s'
      change _ = FractionalIdeal.coeIdealHom (W⁄K).CoordinateRing⁰ (W⁄K).FunctionField _
      rw [hmap]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [zpow_one, CoordinateRing.XYIdeal'_eq, placeIdeal_of_ne_zero W K i.2]
      rfl
    have key' := key
    rw [hcoe, FractionalIdeal.coe_coeIdeal] at key'
    exact (IsLocalization.coeSubmodule_isPrincipal _ le_rfl).mp key'
  ·
    have hpt : ∀ i : {P : (W⁄K).Point // P ≠ 0},
        Point.some i.1.xc i.1.yc (Point.nonsingular_xc_yc i.2) = i.1 := fun i => (Point.eq_some_xc_yc i.2).symm
    simp_rw [one_smul, hpt]
    have hsub : ∑ x ∈ s', (x : (W⁄K).Point) = ∑ P ∈ s.filter (· ≠ 0), P :=
      Finset.sum_subtype_eq_sum_filter (fun P : (W⁄K).Point => P)
    rw [hsub, Finset.sum_filter_of_ne (fun P _ hP => hP)]
    exact sum_fibSet_eq_zero W hn hT

theorem span_weilNum_eq {n : ℕ} (hn : (n : K) ≠ 0) {T : (W⁄K).Point} (hT : (n : ℤ) • T = 0) :
    Ideal.span {weilNum W K n T} = ∏ P ∈ (WeierstrassCurve.Affine.fibSet_finite W hn T).toFinset, placeIdeal W K P := by
  rw [span_weilNum W K (fibIdeal_isPrincipal W hn hT), fibIdeal_eq]

end WeilDiv

theorem solution {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hn : (n : K) ≠ 0) {T : (W⁄K).Point} (hT : (n : ℤ) • T = 0) (P : (W⁄K).Point) (hP : P ≠ 0) : (placeOf W K P hP).valuation (W⁄K).FunctionField (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (weilNum W K n T)) = if (n : ℤ) • P = T then exp (-1 : ℤ) else 1 := by
  classical
  rw [valuation_of_algebraMap, WeilDiv.intValuation_of_span_eq_prod W _ (WeilDiv.span_weilNum_eq W hn hT) P hP]
  simp only [Set.Finite.mem_toFinset, mem_fibSet]

end S_WeierstrassCurve_Affine_valuation_weilNum
end P2MW
export P2MW.S_WeierstrassCurve_Affine_valuation_weilNum (solution)
