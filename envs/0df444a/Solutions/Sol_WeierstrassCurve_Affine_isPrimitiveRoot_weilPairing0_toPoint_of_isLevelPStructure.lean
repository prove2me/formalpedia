-- Prove2me | solution 1 for WeierstrassCurve.Affine.isPrimitiveRoot_weilPairing0_toPoint_of_isLevelPStructure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1267f67b-ab62-5a6a-9757-944e99bb7778

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Theorems.Thm_ModularCurve_IsLevelPStructure_exists_eq_nsmul_add_nsmul_of_isLevelPStructure
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_add_left
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_add_right
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_self
import Theorems.Thm_WeierstrassCurve_Affine_eq_zero_of_forall_weilPairing0_eq_one
import Theorems.Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_ModularCurve_isUnit_indepElt_symm
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_isPrimitiveRoot_weilPairing0_toPoint_of_isLevelPStructure
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve WeierstrassCurve.Affine
open scoped MatrixGroups

namespace WeilPrimitiveSol

section Torsion

variable {G : Type*} [AddCommGroup G]

theorem torsion_nsmul {n : ℕ} {S : G} (h : (n : ℤ) • S = 0) (m : ℕ) : (n : ℤ) • (m • S) = 0 := by
  rw [← natCast_zsmul, smul_smul, mul_comm, ← smul_smul, h, smul_zero]

theorem torsion_add {n : ℕ} {S T : G} (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0) :
    (n : ℤ) • (S + T) = 0 := by
  rw [smul_add, hS, hT, add_zero]

theorem zsmul_eq_val_nsmul {ℓ : ℕ} [NeZero ℓ] {P : G} (hP : (ℓ : ℤ) • P = 0) {z : ℤ} {a : ZMod ℓ}
    (hz : (z : ZMod ℓ) = a) : z • P = a.val • P := by
  have h1 : (z : ZMod ℓ) = ((a.val : ℤ) : ZMod ℓ) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]; exact hz
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  obtain ⟨k, hk⟩ := h1
  have hz' : z = (a.val : ℤ) + (ℓ : ℤ) * (-k) := by linarith
  rw [hz', add_zsmul, natCast_zsmul, mul_comm, ← smul_smul, hP, smul_zero, add_zero]

theorem exists_nsmul_eq_of_zsmul {ℓ : ℕ} [NeZero ℓ] {P : G} (hP : (ℓ : ℤ) • P = 0) (k : ℤ) :
    ∃ m : ℕ, k • P = m • P := by
  refine ⟨((k : ZMod ℓ)).val, ?_⟩
  exact zsmul_eq_val_nsmul hP rfl

end Torsion

section Pairing

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]
  (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing]
  {n : ℕ} (hn : (n : K) ≠ 0)

include hn

theorem pair_zero_left (T : (W⁄K).Point) (hT : (n : ℤ) • T = 0) : weilPairing0 W K n 0 T = 1 := by
  have h := weilPairing0_add_left W hn 0 0 T (smul_zero _) (smul_zero _) hT
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem pair_zero_right (S : (W⁄K).Point) (hS : (n : ℤ) • S = 0) : weilPairing0 W K n S 0 = 1 := by
  have h := weilPairing0_add_right W hn S 0 0 hS (smul_zero _) (smul_zero _)
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem pair_nsmul_left (m : ℕ) (S T : (W⁄K).Point) (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0) :
    weilPairing0 W K n (m • S) T = weilPairing0 W K n S T ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, pair_zero_left W hn T hT]
  | succ m ih =>
    rw [succ_nsmul, weilPairing0_add_left W hn _ _ _ (torsion_nsmul hS m) hS hT, ih, pow_succ]

theorem pair_nsmul_right (m : ℕ) (S T : (W⁄K).Point) (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0) :
    weilPairing0 W K n S (m • T) = weilPairing0 W K n S T ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, pair_zero_right W hn S hS]
  | succ m ih =>
    rw [succ_nsmul, weilPairing0_add_right W hn _ _ _ hS (torsion_nsmul hT m) hT, ih, pow_succ]

theorem pair_swap (S T : (W⁄K).Point) (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0) :
    weilPairing0 W K n T S = (weilPairing0 W K n S T)⁻¹ := by
  have h := weilPairing0_self W hn (S + T) (torsion_add hS hT)
  rw [weilPairing0_add_left W hn S T (S + T) hS hT (torsion_add hS hT),
    weilPairing0_add_right W hn S S T hS hS hT, weilPairing0_add_right W hn T S T hT hS hT,
    weilPairing0_self W hn S hS, weilPairing0_self W hn T hT, one_mul, mul_one] at h
  exact eq_inv_of_mul_eq_one_right h

theorem pair_lincomb (a b c d : ℕ) (P Q : (W⁄K).Point) (hP : (n : ℤ) • P = 0) (hQ : (n : ℤ) • Q = 0) :
    weilPairing0 W K n (a • P + b • Q) (c • P + d • Q) =
      weilPairing0 W K n P Q ^ (a * d) * (weilPairing0 W K n P Q ^ (b * c))⁻¹ := by
  have hQ' : (n : ℤ) • (c • P + d • Q) = 0 := torsion_add (torsion_nsmul hP c) (torsion_nsmul hQ d)
  rw [weilPairing0_add_left W hn _ _ _ (torsion_nsmul hP a) (torsion_nsmul hQ b) hQ',
    pair_nsmul_left W hn a P _ hP hQ', pair_nsmul_left W hn b Q _ hQ hQ',
    weilPairing0_add_right W hn P _ _ hP (torsion_nsmul hP c) (torsion_nsmul hQ d),
    weilPairing0_add_right W hn Q _ _ hQ (torsion_nsmul hP c) (torsion_nsmul hQ d),
    pair_nsmul_right W hn c P P hP hP, pair_nsmul_right W hn d P Q hP hQ,
    pair_nsmul_right W hn c Q P hQ hP, pair_nsmul_right W hn d Q Q hQ hQ,
    weilPairing0_self W hn P hP, weilPairing0_self W hn Q hQ, one_pow, one_mul, one_pow, mul_one,
    pair_swap W hn P Q hP hQ, ← pow_mul, ← pow_mul, inv_pow, mul_comm d a, mul_comm c b]

theorem pair_pow_eq_one (P Q : (W⁄K).Point) (hP : (n : ℤ) • P = 0) (hQ : (n : ℤ) • Q = 0) :
    weilPairing0 W K n P Q ^ n = 1 := by
  rw [← pair_nsmul_left W hn n P Q hP hQ, ← natCast_zsmul, hP, pair_zero_left W hn Q hQ]

end Pairing

section Span

variable {K : Type u} [Field K] [DecidableEq K] (V : WeierstrassCurve K) [V.IsElliptic]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓK : (ℓ : K) ≠ 0)

include hℓ3 in
theorem odd_ell : Odd ℓ :=
  (Fact.out : ℓ.Prime).odd_of_ne_two (by omega)

omit [Fact ℓ.Prime] in
include hℓ3 in
theorem ell_ne_two : ℓ ≠ 2 := by omega

omit [DecidableEq K] [V.IsElliptic] in
theorem toPoint_eq_some {x y : K} (h : V.toAffine.Nonsingular x y) :
    toPoint V x y = Point.some x y h := by
  unfold toPoint
  rw [dif_pos h]

include hℓ3 in

theorem zsmul_some_eq_zero {D : LevelPData K} (hD : IsLevelPStructure V ℓ D)
    (nP : V.toAffine.Nonsingular D.xP D.yP) : (ℓ : ℤ) • Point.some D.xP D.yP nP = 0 := by
  rw [natCast_zsmul]
  apply (Point.nsmul_some_eq_zero_iff_eval_prePsi V (odd_ell ℓ hℓ3) nP).mpr
  rw [← WeierstrassCurve.preΨ_ofNat]
  exact hD.preΨ_P

include hℓ3 hℓK in

theorem exists_eq_lincomb {D : LevelPData K} (hD : IsLevelPStructure V ℓ D)
    (nP : V.toAffine.Nonsingular D.xP D.yP) (nQ : V.toAffine.Nonsingular D.xQ D.yQ)
    (S : V.toAffine.Point) (hS : (ℓ : ℤ) • S = 0) :
    ∃ i j : ℕ, S = i • Point.some D.xP D.yP nP + j • Point.some D.xQ D.yQ nQ := by
  have hΔ : IsUnit V.Δ := WeierstrassCurve.isUnit_Δ V
  have hℓP : (ℓ : ℤ) • Point.some D.xP D.yP nP = 0 := zsmul_some_eq_zero V ℓ hℓ3 hD nP
  have hℓPn : ℓ • Point.some D.xP D.yP nP = 0 := by rw [← natCast_zsmul]; exact hℓP
  rcases S with _ | ⟨x, y, h⟩
  · exact ⟨0, 0, by rw [← Point.zero_def, zero_nsmul, zero_nsmul, add_zero]⟩
  by_cases hmem : Point.some x y h ∈ AddSubgroup.zmultiples (Point.some D.xP D.yP nP)
  · obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    obtain ⟨m, hm⟩ := exists_nsmul_eq_of_zsmul (ℓ := ℓ) hℓP k
    exact ⟨m, 0, by rw [zero_nsmul, add_zero, ← hm, hk]⟩
  ·
    have hSn : ℓ • Point.some x y h = 0 := by rw [← natCast_zsmul]; exact hS
    have hψS : (V.preΨ (ℓ : ℤ)).eval x = 0 := by
      rw [WeierstrassCurve.preΨ_ofNat]
      exact (Point.nsmul_some_eq_zero_iff_eval_prePsi V (odd_ell ℓ hℓ3) h).mp hSn
    have hind : IsUnit (indepElt V ℓ D.xP x) := by
      rw [isUnit_iff_ne_zero]
      intro h0
      exact hmem ((indepElt_eq_zero_iff_mem_zmultiples (ell_ne_two ℓ hℓ3) nP h hℓPn).mp h0)
    have hind' : IsUnit (indepElt V ℓ x D.xP) :=
      isUnit_indepElt_symm V ℓ (ell_ne_two ℓ hℓ3) (isUnit_iff_ne_zero.mpr hℓK) hΔ hD.equation_P h.left
        hD.preΨ_P hψS hind
    have hDS : IsLevelPStructure V ℓ ⟨D.xP, D.yP, x, y⟩ :=
      { equation_P := hD.equation_P
        equation_Q := h.left
        preΨ_P := hD.preΨ_P
        preΨ_Q := hψS
        isUnit_indepElt_PQ := hind
        isUnit_indepElt_QP := hind' }
    obtain ⟨_, _, _, _, a, b, c, d, -, -, hcd⟩ :=
      IsLevelPStructure.exists_eq_nsmul_add_nsmul_of_isLevelPStructure ℓ hℓ3 hℓK V hΔ D _ hD hDS
    exact ⟨c.val, d.val, hcd⟩

end Span

end WeilPrimitiveSol

open WeilPrimitiveSol in
theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓK : (ℓ : K) ≠ 0)
    (D : ModularCurve.LevelPData K) (hD : ModularCurve.IsLevelPStructure W ℓ D) :
    IsPrimitiveRoot
      ((weilPairing0 W K ℓ (toPoint (W.baseChange K) D.xP D.yP) (toPoint (W.baseChange K) D.xQ D.yQ) : Kˣ) : K) ℓ := by

  have hVW : W.baseChange K = W := rfl
  haveI hVell : (W.baseChange K).IsElliptic := by rw [hVW]; infer_instance
  haveI : IsDedekindDomain (W⁄K).CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain (W.baseChange K)
  have hDV : IsLevelPStructure (W.baseChange K) ℓ D := hVW ▸ hD
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩

  have nP : (W.baseChange K).toAffine.Nonsingular D.xP D.yP :=
    ((W.baseChange K).toAffine.equation_iff_nonsingular.mp hDV.equation_P)
  have nQ : (W.baseChange K).toAffine.Nonsingular D.xQ D.yQ :=
    ((W.baseChange K).toAffine.equation_iff_nonsingular.mp hDV.equation_Q)
  set P : (W⁄K).Point := Point.some D.xP D.yP nP with hPdef
  set Q : (W⁄K).Point := Point.some D.xQ D.yQ nQ with hQdef
  have htP : toPoint (W.baseChange K) D.xP D.yP = P := toPoint_eq_some _ nP
  have htQ : toPoint (W.baseChange K) D.xQ D.yQ = Q := toPoint_eq_some _ nQ

  have hℓP : (ℓ : ℤ) • P = 0 := zsmul_some_eq_zero (W.baseChange K) ℓ hℓ3 hDV nP
  have hℓQ : (ℓ : ℤ) • Q = 0 := zsmul_some_eq_zero (W.baseChange K) ℓ hℓ3 hDV.swap nQ
  rw [htP, htQ]
  set e : Kˣ := weilPairing0 W K ℓ P Q with hedef
  have hpow : e ^ ℓ = 1 := pair_pow_eq_one W hℓK P Q hℓP hℓQ

  have hne : e ≠ 1 := by
    intro he1
    have hQ0 : Q = 0 := by
      refine eq_zero_of_forall_weilPairing0_eq_one W hℓK Q hℓQ fun S hS => ?_
      obtain ⟨i, j, rfl⟩ := exists_eq_lincomb (W.baseChange K) ℓ hℓ3 hℓK hDV nP nQ S hS
      rw [weilPairing0_add_left W hℓK _ _ _ (torsion_nsmul hℓP i) (torsion_nsmul hℓQ j) hℓQ,
        pair_nsmul_left W hℓK i P Q hℓP hℓQ, pair_nsmul_left W hℓK j Q Q hℓQ hℓQ,
        weilPairing0_self W hℓK Q hℓQ, one_pow, mul_one, ← hedef, he1, one_pow]
    exact Point.some_ne_zero nQ hQ0
  have hord : orderOf e = ℓ := orderOf_eq_prime hpow hne
  exact IsPrimitiveRoot.coe_units_iff.mpr (hord ▸ IsPrimitiveRoot.orderOf e)

end S_WeierstrassCurve_Affine_isPrimitiveRoot_weilPairing0_toPoint_of_isLevelPStructure
end P2MW
export P2MW.S_WeierstrassCurve_Affine_isPrimitiveRoot_weilPairing0_toPoint_of_isLevelPStructure (solution)
