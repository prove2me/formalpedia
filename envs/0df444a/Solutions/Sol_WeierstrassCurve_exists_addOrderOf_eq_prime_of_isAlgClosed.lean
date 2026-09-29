-- Prove2me | solution 1 for WeierstrassCurve.exists_addOrderOf_eq_prime_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b70c62a7-003b-5551-800b-ef85013d6b67

import Mathlib
import Theorems.Thm_WeierstrassCurve_natCard_cycSub_eq_prime_add_one
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_addOrderOf_eq_prime_of_isAlgClosed
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

namespace C1Dev

open Polynomial WeierstrassCurve.Affine

private theorem exists_y {K : Type*} [Field K] [IsAlgClosed K]
    (W : WeierstrassCurve K) (x : K) : ∃ y : K, W.toAffine.Equation x y := by
  set q : Polynomial K := Polynomial.X ^ 2 + Polynomial.C (W.a₁ * x + W.a₃) * Polynomial.X
      - Polynomial.C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) with hq
  have hd : q.degree = 2 := by rw [hq]; compute_degree!
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (by rw [hd]; norm_num)
  refine ⟨y, (W.toAffine.equation_iff x y).mpr ?_⟩
  have hev := Polynomial.IsRoot.def.mp hy
  rw [hq] at hev
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at hev
  linear_combination hev

private theorem char_two_leg {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ℕ) (hp : p.Prime) (hpK : (p : K) ≠ 0) (h2 : (2 : K) = 0) :
    ∃ T : W.toAffine.Point, addOrderOf T = p := by

  have hp2 : p ≠ 2 := fun hp2 => hpK (by rw [hp2, Nat.cast_ofNat, h2])
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p; simp_all
    · exact h

  have hcast : ((p : ℤ) : K) ≠ 0 := by rwa [Int.cast_natCast]
  have hdeg : 0 < (W.ΨSq (p : ℤ)).natDegree :=
    W.natDegree_ΨSq_pos (by simp only [Int.natAbs_natCast]; omega) hcast
  obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root _
    (Polynomial.natDegree_pos_iff_degree_pos.mp hdeg).ne'
  have hroot : (W.ΨSq (p : ℤ)).eval x₀ = 0 := hx₀

  obtain ⟨y₀, hy₀⟩ := exists_y W x₀
  have h : W.toAffine.Nonsingular x₀ y₀ := W.toAffine.equation_iff_nonsingular.mp hy₀

  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpre : (W.preΨ' p).eval x₀ = 0 := by
    have hofn := congrArg (Polynomial.eval x₀) (W.ΨSq_ofNat p)
    rw [hroot, if_neg (Nat.not_even_iff_odd.mpr hodd)] at hofn
    have : (W.preΨ' p).eval x₀ ^ 2 = 0 := by
      simpa using hofn.symm
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have hkill : p • (Point.some x₀ y₀ h : W.toAffine.Point) = 0 :=
    (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd h).mpr hpre
  have hdvd : addOrderOf (Point.some x₀ y₀ h : W.toAffine.Point) ∣ p :=
    addOrderOf_dvd_of_nsmul_eq_zero hkill
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h1 | hord
  · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) (Point.some_ne_zero h)
  · exact ⟨Point.some x₀ y₀ h, hord⟩

end C1Dev

theorem solution {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ℕ) (hp : p.Prime) (hpK : (p : K) ≠ 0) :
    ∃ T : W.toAffine.Point, addOrderOf T = p := by
  by_cases h2 : (2 : K) = 0
  · exact C1Dev.char_two_leg W p hp hpK h2
  · haveI : Fact p.Prime := ⟨hp⟩
    have hcard := WeierstrassCurve.natCard_cycSub_eq_prime_add_one W p hpK h2
    have hne : Nat.card {G : AddSubgroup W.toAffine.Point //
        ∃ g : W.toAffine.Point, addOrderOf g = p ∧ G = AddSubgroup.zmultiples g} ≠ 0 := by
      rw [hcard]; exact Nat.succ_ne_zero p
    obtain ⟨⟨G, g, hg, -⟩⟩ := (Nat.card_ne_zero.mp hne).1
    exact ⟨g, hg⟩

end S_WeierstrassCurve_exists_addOrderOf_eq_prime_of_isAlgClosed
end P2MW
export P2MW.S_WeierstrassCurve_exists_addOrderOf_eq_prime_of_isAlgClosed (solution)
