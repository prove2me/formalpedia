-- Prove2me | solution 1 for WeierstrassCurve.exists_hauptmodulThree_of_not_modRepIsIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4bcfa6d7-f337-5ac6-96f9-2269362f6dc4

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_FLTPrelim_ModularRep
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_Submodule_eq_span_singleton_of_card_eq_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_hauptmodulThree_of_not_modRepIsIrreducible
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point Polynomial

open scoped WeierstrassCurve.Affine

namespace M4cP4Three

section Extraction

theorem exists_eval_Ψ₃_eq_zero (V : WeierstrassCurve ℚ) (hΔ : V.Δ ≠ 0)
    (h3 : ¬ GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ V 3) :
    ∃ q : ℚ, V.Ψ₃.eval q = 0 := by
  haveI hell : V.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩

  have hcases : ∀ d : ZMod 3, d = 0 ∨ d = 1 ∨ d = -1 := by decide
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩

  haveI hnormQ : Normal ℚ (AlgebraicClosure ℚ) := by
    have h : @Normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  haveI halgQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
      inferInstance
    exact h
  haveI hsepQ : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) := by
    have h : @Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
      inferInstance
    exact h
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩

  have hcard : Nat.card (Submodule.torsionBy ℤ (V⁄(AlgebraicClosure ℚ)).Point (3 : ℕ)) = 3 ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed V (by norm_num)
  haveI : Finite (Submodule.torsionBy ℤ (V⁄(AlgebraicClosure ℚ)).Point (3 : ℕ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hnt : Nontrivial (Submodule.torsionBy ℤ (V⁄(AlgebraicClosure ℚ)).Point (3 : ℕ)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)

  have hN : ∃ N : Submodule (ZMod 3) (Submodule.torsionBy ℤ (V⁄(AlgebraicClosure ℚ)).Point (3 : ℕ)),
      IsGaloisStable ℚ N ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
    by_contra hno
    refine h3 ⟨hnt, fun N hN => ?_⟩
    by_contra hcon
    rw [not_or] at hcon
    exact hno ⟨N, hN, hcon.1, hcon.2⟩
  obtain ⟨N, hN, hbot, htop⟩ := hN

  obtain ⟨T, hTN, hT0⟩ := (Submodule.ne_bot_iff N).mp hbot
  have hspan : N = Submodule.span (ZMod 3) {T} :=
    Submodule.eq_span_singleton_of_card_eq_sq hcard N htop hTN hT0

  rcases hT_eq : (T : (V⁄(AlgebraicClosure ℚ)).Point) with _ | ⟨xT, yT, hns⟩
  · exact absurd (Subtype.ext hT_eq) hT0

  have hxfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ xT = xT := by
    intro σ
    have hmem : σ • T ∈ N := hN σ T hTN
    rw [hspan, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hcoe : ((σ • T : Submodule.torsionBy ℤ (V⁄(AlgebraicClosure ℚ)).Point (3 : ℕ)) :
        (V⁄(AlgebraicClosure ℚ)).Point) = Point.map σ.toAlgHom (T : (V⁄(AlgebraicClosure ℚ)).Point) :=
      rfl
    rw [hT_eq, Point.map_some] at hcoe
    rcases hcases c with rfl | rfl | rfl
    ·
      rw [zero_smul] at hc
      have h0 := congrArg Subtype.val hc
      rw [hcoe] at h0
      exact absurd h0.symm (Point.some_ne_zero _)
    ·
      rw [one_smul] at hc
      have h1 := congrArg Subtype.val hc
      rw [hcoe, hT_eq] at h1
      exact (Point.X_eq_iff.mpr (Or.inl h1)).symm
    ·
      rw [neg_one_smul] at hc
      have h2 := congrArg Subtype.val hc
      rw [hcoe, Submodule.coe_neg, hT_eq] at h2
      exact Point.X_eq_iff.mpr (Or.inr h2.symm)

  obtain ⟨q, hq⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ) xT).mpr hxfix

  have h3T : (3 : ℤ) • (Point.some xT yT hns) = 0 := by
    have h := (Submodule.mem_torsionBy_iff _ _).mp T.2
    rw [hT_eq] at h
    exact_mod_cast h
  have hroot : ((V⁄(AlgebraicClosure ℚ)).Ψ₃).eval xT = 0 := by
    have h := (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff
      (V.baseChange (AlgebraicClosure ℚ)) hns 3).mp h3T
    rwa [WeierstrassCurve.ψ_three, evalEval_C] at h

  refine ⟨q, (algebraMap ℚ (AlgebraicClosure ℚ)).injective ?_⟩
  have key : ((V⁄(AlgebraicClosure ℚ)).Ψ₃).eval (algebraMap ℚ (AlgebraicClosure ℚ) q)
      = algebraMap ℚ (AlgebraicClosure ℚ) (V.Ψ₃.eval q) := by
    show ((V.map (algebraMap ℚ (AlgebraicClosure ℚ))).Ψ₃).eval _ = _
    rw [WeierstrassCurve.map_Ψ₃, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  rw [_root_.map_zero, ← key, hq]
  exact hroot

end Extraction

section Producer

set_option maxHeartbeats 16000000 in

theorem threeKernel_clearedMembership (A B x : ℚ)
    (hψ : 3*x^4 + 6*A*x^2 + 12*B*x - A^2 = 0) :
    ∀ N D : ℚ,
      N = -3*(208*A^6 + 96*A^5*x^2 + 2112*A^4*B*x + 1056*A^3*B*x^3 + 5808*A^3*B^2
            + 744*A^2*B^2*x^2 + 14976*A*B^3*x + 7560*B^3*x^3 + 30375*B^4) →
      D = (4*A^3 + 27*B^2) * (8*A^3 + 4*A^2*x^2 + 58*A*B*x + 30*B*x^3 + 125*B^2) →
      (N + 27*D) * (N + 3*D)^3 * (-16*(4*A^3 + 27*B^2)) = (-48*A)^3 * N * D^3 := by
  rintro N D rfl rfl
  linear_combination
    (-1019215872*A^23*x^4 + 55037657088*A^21*B*x^5 + 84085309440*A^19*B^2*x^6 -
      22331529363456*A^17*B^3*x^7 - 167796630355968*A^15*B^4*x^8 - 2038431744*A^24*x^2 +
      293534171136*A^22*B*x^3 - 2697609609216*A^20*B^2*x^4 - 156314590248960*A^18*B^3*x^5 -
      963427307618304*A^16*B^4*x^6 - 316653426966528*A^14*B^5*x^7 -
      4948568613126144*A^12*B^6*x^8 + 339738624*A^25 + 373033009152*A^23*B*x -
      13049020809216*A^21*B^2*x^2 - 349573207818240*A^19*B^3*x^3 -
      1983100234235904*A^17*B^4*x^4 - 4758237072064512*A^15*B^5*x^5 -
      29174012984033280*A^13*B^6*x^6 + 1505288520990720*A^11*B^7*x^7 -
      57427610374471680*A^9*B^8*x^8 - 14544974905344*A^22*B^2 - 250109969301504*A^20*B^3*x -
      1975285078032384*A^18*B^4*x^2 - 14987634245369856*A^16*B^5*x^3 -
      57148390365659136*A^14*B^6*x^4 - 60810931310690304*A^12*B^7*x^5 -
      349676867136651264*A^10*B^8*x^6 + 48081987235676160*A^8*B^9*x^7 -
      326535308854272000*A^6*B^10*x^8 - 1043790822899712*A^19*B^4 -
      13232989783719936*A^17*B^5*x - 51865596120268800*A^15*B^6*x^2 -
      262664003336011776*A^13*B^7*x^3 - 659334061891731456*A^11*B^8*x^4 -
      438976512982351872*A^9*B^9*x^5 - 2072581920590192640*A^7*B^10*x^6 +
      285550851032064000*A^5*B^11*x^7 - 904637746984320000*A^3*B^12*x^8 -
      29923732700135424*A^16*B^6 - 258534850315419648*A^14*B^7*x -
      590482703586852864*A^12*B^8*x^2 - 2438324701266640896*A^10*B^9*x^3 -
      3747004240938135552*A^8*B^10*x^4 - 2010671488208609280*A^6*B^11*x^5 -
      6065903014737408000*A^4*B^12*x^6 + 544110553440000000*A^2*B^13*x^7 -
      968551222500000000*B^14*x^8 - 445644499770851328*A^13*B^8 -
      2522588873465364480*A^11*B^9*x - 3500864189940842496*A^9*B^10*x^2 -
      12691270656073064448*A^7*B^11*x^3 - 10407531450451737600*A^5*B^12*x^4 -
      5739048535173120000*A^3*B^13*x^5 - 6999396834600000000*A*B^14*x^6 -
      3765359469795987456*A^10*B^10 - 13209125879347568640*A^8*B^11*x -
      11287787820364339200*A^6*B^12*x^2 - 35186860236494592000*A^4*B^13*x^3 -
      11201273364852000000*A^2*B^14*x^4 - 7748409780000000000*B^15*x^5 -
      18230028003652608000*A^7*B^12 - 35484113877511680000*A^5*B^13*x -
      19357387248787200000*A^3*B^14*x^2 - 40653323312400000000*A*B^15*x^3 -
      47180124546048000000*A^4*B^14 - 38321912903040000000*A^2*B^15*x -
      15496819560000000000*B^16*x^2 - 50622943896000000000*A*B^16) * hψ

theorem int_mul_self_ne_six (n : ℤ) : n * n ≠ 6 := by
  intro h
  have h4 : ∀ m : ZMod 4, m * m ≠ 6 := by decide
  have hc := congrArg (fun z : ℤ => (z : ZMod 4)) h
  push_cast at hc
  exact h4 _ hc

theorem rat_mul_self_ne_six (s : ℚ) : s * s ≠ 6 := by
  intro h
  have h2 := congrArg Rat.num h
  rw [Rat.mul_self_num] at h2
  exact int_mul_self_ne_six s.num (by simpa using h2)

theorem threeKernel_resultant_identity (A B x : ℚ) :
    (576*A^8*x^2 + 864*A^6*B*x^3 + 288*A^7*B*x + 864*A^5*B^2*x^2 + 1296*A^3*B^3*x^3
        - 144*A^6*B^2 + 432*A^4*B^3*x - 13500*A^2*B^4*x^2 - 20250*B^5*x^3 - 216*A^3*B^4
        - 6750*A*B^5*x + 3375*B^6)
      * (8*A^3 + 4*A^2*x^2 + 58*A*B*x + 30*B*x^3 + 125*B^2)
    + (-768*A^10 - 6912*A^8*B*x - 8640*A^6*B^2*x^2 - 3456*A^7*B^2 - 10368*A^5*B^3*x
        - 12960*A^3*B^4*x^2 + 14544*A^4*B^4 + 162000*A^2*B^5*x + 202500*B^6*x^2
        + 54000*A*B^6)
      * (3*x^4 + 6*A*x^2 + 12*B*x - A^2)
    = 3 * (16*A^6 + 24*A^3*B^2 - 375*B^4)^2 := by
  ring

theorem threeKernel_secondFactor_ne_zero (A B x : ℚ)
    (hΔ : 4*A^3 + 27*B^2 ≠ 0) (hψ : 3*x^4 + 6*A*x^2 + 12*B*x - A^2 = 0) :
    8*A^3 + 4*A^2*x^2 + 58*A*B*x + 30*B*x^3 + 125*B^2 ≠ 0 := by
  intro hG

  have hres : 3 * (16*A^6 + 24*A^3*B^2 - 375*B^4)^2 = 0 := by
    rw [← threeKernel_resultant_identity A B x, hG, hψ]
    ring
  have hsq : (16*A^6 + 24*A^3*B^2 - 375*B^4)^2 = 0 := by linarith
  have h0 : 16*A^6 + 24*A^3*B^2 - 375*B^4 = 0 := sq_eq_zero_iff.mp hsq
  rcases eq_or_ne B 0 with hB | hB
  ·
    apply hΔ
    have hA6 : (A^3)^2 = 0 := by
      rw [hB] at h0
      linear_combination (1/16 : ℚ) * h0
    have hA3 : A^3 = 0 := sq_eq_zero_iff.mp hA6
    rw [hB]
    linear_combination 4 * hA3
  ·
    have hB2 : (B^2 : ℚ) ≠ 0 := pow_ne_zero 2 hB
    have h8B : (8 * B^2 : ℚ) ≠ 0 := mul_ne_zero (by norm_num) hB2
    have hsq384 : (4*A^3 + 3*B^2)^2 = 384 * (B^2)^2 := by linear_combination h0
    apply rat_mul_self_ne_six ((4*A^3 + 3*B^2) / (8*B^2))
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero h8B h8B)]
    linear_combination hsq384

theorem hauptmodulThree_of_clearedMembership {N D W C u : ℚ} (hD : D ≠ 0) (hN : N = u * D)
    (key : (N + 27*D) * (N + 3*D)^3 * W = C * N * D^3) :
    (u + 27) * (u + 3)^3 * W = C * u := by
  apply mul_left_cancel₀ (pow_ne_zero 4 hD)
  calc D^4 * ((u + 27) * (u + 3)^3 * W)
      = ((u * D) + 27*D) * ((u * D) + 3*D)^3 * W := by ring
    _ = (N + 27*D) * (N + 3*D)^3 * W := by rw [← hN]
    _ = C * N * D^3 := key
    _ = C * (u * D) * D^3 := by rw [hN]
    _ = D^4 * (C * u) := by ring

theorem exists_hauptmodulThree_of_psiThreeRoot (A B x : ℚ)
    (hΔ : 4*A^3 + 27*B^2 ≠ 0)
    (hψ : 3*x^4 + 6*A*x^2 + 12*B*x - A^2 = 0) :
    ∃ u : ℚ, u ≠ 0 ∧
      (u + 27) * (u + 3)^3 * (-16*(4*A^3 + 27*B^2)) = (-48*A)^3 * u := by
  set N : ℚ := -3*(208*A^6 + 96*A^5*x^2 + 2112*A^4*B*x + 1056*A^3*B*x^3 + 5808*A^3*B^2
      + 744*A^2*B^2*x^2 + 14976*A*B^3*x + 7560*B^3*x^3 + 30375*B^4) with hNdef
  set D : ℚ := (4*A^3 + 27*B^2) * (8*A^3 + 4*A^2*x^2 + 58*A*B*x + 30*B*x^3 + 125*B^2)
    with hDdef
  have hD : D ≠ 0 := by
    rw [hDdef]
    exact mul_ne_zero hΔ (threeKernel_secondFactor_ne_zero A B x hΔ hψ)
  have mem : (N / D + 27) * (N / D + 3)^3 * (-16*(4*A^3 + 27*B^2)) = (-48*A)^3 * (N / D) :=
    hauptmodulThree_of_clearedMembership hD (div_mul_cancel₀ N hD).symm
      (threeKernel_clearedMembership A B x hψ N D hNdef hDdef)
  refine ⟨N / D, ?_, mem⟩
  intro hu0
  apply hΔ
  have h0 : ((0:ℚ) + 27) * ((0:ℚ) + 3)^3 * (-16*(4*A^3 + 27*B^2)) = (-48*A)^3 * 0 := by
    rw [← hu0]; exact mem
  linear_combination (-(1:ℚ)/11664) * h0

end Producer

section Seam

theorem units_pow_mul_inv_pow (C : VariableChange ℚ) (k : ℕ) :
    ((C.u : ℚˣ) : ℚ) ^ k * ((C.u⁻¹ : ℚˣ) : ℚ) ^ k = 1 := by
  rw [← mul_pow, C.u.mul_inv, one_pow]

theorem variableChange_Δ_ne_zero_of_ne_zero (C : VariableChange ℚ) (W : WeierstrassCurve ℚ)
    (hΔ : W.Δ ≠ 0) : (C • W).Δ ≠ 0 := by
  rw [variableChange_Δ]
  exact mul_ne_zero (pow_ne_zero 12 (Units.ne_zero _)) hΔ

theorem hauptmodulRelation_variableChange (C : VariableChange ℚ) (W : WeierstrassCurve ℚ)
    (g v : ℚ) (h : g * W.Δ = W.c₄ ^ 3 * v) :
    g * (C • W).Δ = (C • W).c₄ ^ 3 * v := by
  rw [variableChange_Δ, variableChange_c₄]
  linear_combination ((C.u⁻¹ : ℚˣ) : ℚ) ^ 12 * h

theorem hauptmodulRelation_of_variableChange (C : VariableChange ℚ) (W : WeierstrassCurve ℚ)
    (g v : ℚ) (h : g * (C • W).Δ = (C • W).c₄ ^ 3 * v) :
    g * W.Δ = W.c₄ ^ 3 * v := by
  have key := hauptmodulRelation_variableChange C⁻¹ (C • W) g v h
  rwa [inv_smul_smul] at key

theorem Ψ₃_eval_variableChange (C : VariableChange ℚ) (W : WeierstrassCurve ℚ) (z : ℚ) :
    ((C.u : ℚˣ) : ℚ) ^ 8 * ((C • W).Ψ₃.eval z)
      = W.Ψ₃.eval (((C.u : ℚˣ) : ℚ) ^ 2 * z + C.r) := by
  simp only [Ψ₃, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat,
    variableChange_b₂, variableChange_b₄, variableChange_b₆, variableChange_b₈]
  linear_combination
    (((C.u : ℚˣ) : ℚ) ^ 6 * z ^ 3 * (W.b₂ + 12 * C.r)) * units_pow_mul_inv_pow C 2
      + (3 * ((C.u : ℚˣ) : ℚ) ^ 4 * z ^ 2 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2))
          * units_pow_mul_inv_pow C 4
      + (3 * ((C.u : ℚˣ) : ℚ) ^ 2 * z
            * (W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂ + 4 * C.r ^ 3))
          * units_pow_mul_inv_pow C 6
      + (W.b₈ + 3 * C.r * W.b₆ + 3 * C.r ^ 2 * W.b₄ + C.r ^ 3 * W.b₂ + 3 * C.r ^ 4)
          * units_pow_mul_inv_pow C 8

theorem Ψ₃_eval_variableChange_eq_zero (C : VariableChange ℚ) (W : WeierstrassCurve ℚ)
    {x : ℚ} (hx : W.Ψ₃.eval x = 0) :
    (C • W).Ψ₃.eval ((x - C.r) * ((C.u⁻¹ : ℚˣ) : ℚ) ^ 2) = 0 := by
  have key := Ψ₃_eval_variableChange C W ((x - C.r) * ((C.u⁻¹ : ℚˣ) : ℚ) ^ 2)
  have harg : ((C.u : ℚˣ) : ℚ) ^ 2 * ((x - C.r) * ((C.u⁻¹ : ℚˣ) : ℚ) ^ 2) + C.r = x := by
    linear_combination (x - C.r) * units_pow_mul_inv_pow C 2
  rw [harg, hx] at key
  exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 8 (Units.ne_zero _))

theorem eval_Ψ₃_of_short (W : WeierstrassCurve ℚ) (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0)
    (h₃ : W.a₃ = 0) (x : ℚ) :
    W.Ψ₃.eval x = 3 * x ^ 4 + 6 * W.a₄ * x ^ 2 + 12 * W.a₆ * x - W.a₄ ^ 2 := by
  simp only [Ψ₃, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    h₁, h₂, h₃]
  ring

theorem exists_hauptmodulThree_of_Ψ₃_root (W : WeierstrassCurve ℚ) (hΔ : W.Δ ≠ 0)
    {x : ℚ} (hx : W.Ψ₃.eval x = 0) :
    ∃ u : ℚ, u ≠ 0 ∧ (u + 27) * (u + 3) ^ 3 * W.Δ = W.c₄ ^ 3 * u := by
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  haveI : Invertible (3 : ℚ) := invertibleOfNonzero (by norm_num)

  set C : VariableChange ℚ := W.toShortNF with hC
  haveI hshort : (C • W).IsShortNF := W.toShortNF_spec
  have ha₁ : (C • W).a₁ = 0 := hshort.a₁
  have ha₂ : (C • W).a₂ = 0 := hshort.a₂
  have ha₃ : (C • W).a₃ = 0 := hshort.a₃

  have hΔ' : (C • W).Δ ≠ 0 := variableChange_Δ_ne_zero_of_ne_zero C W hΔ
  have hΔeq : (C • W).Δ = -16 * (4 * (C • W).a₄ ^ 3 + 27 * (C • W).a₆ ^ 2) :=
    Δ_of_isShortNF (C • W)
  have hAB : 4 * (C • W).a₄ ^ 3 + 27 * (C • W).a₆ ^ 2 ≠ 0 := by
    intro h0
    exact hΔ' (by rw [hΔeq, h0, mul_zero])

  have hx' := Ψ₃_eval_variableChange_eq_zero C W hx
  rw [eval_Ψ₃_of_short (C • W) ha₁ ha₂ ha₃] at hx'

  obtain ⟨u, hu, hrel⟩ :=
    exists_hauptmodulThree_of_psiThreeRoot (C • W).a₄ (C • W).a₆
      ((x - C.r) * ((C.u⁻¹ : ℚˣ) : ℚ) ^ 2) hAB hx'

  refine ⟨u, hu, hauptmodulRelation_of_variableChange C W ((u + 27) * (u + 3) ^ 3) u ?_⟩
  rw [hΔeq, c₄_of_isShortNF (C • W)]
  linear_combination hrel

end Seam

end M4cP4Three

theorem solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (h3 : ¬ W.ModRepIsIrreducible 3) :
    ∃ u : ℚ, u ≠ 0 ∧ (u + 27) * (u + 3) ^ 3 * (W.Δ : ℚ) = (W.c₄ : ℚ) ^ 3 * u := by

  have hΔV : (W.map (Int.castRingHom ℚ)).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ, eq_intCast]
    exact Int.cast_ne_zero.mpr hΔ

  obtain ⟨q, hq⟩ :=
    M4cP4Three.exists_eval_Ψ₃_eq_zero (W.map (Int.castRingHom ℚ)) hΔV h3

  obtain ⟨u, hu, hrel⟩ :=
    M4cP4Three.exists_hauptmodulThree_of_Ψ₃_root (W.map (Int.castRingHom ℚ)) hΔV hq

  rw [WeierstrassCurve.map_Δ, eq_intCast, WeierstrassCurve.map_c₄, eq_intCast] at hrel
  exact ⟨u, hu, hrel⟩

end S_WeierstrassCurve_exists_hauptmodulThree_of_not_modRepIsIrreducible
end P2MW
export P2MW.S_WeierstrassCurve_exists_hauptmodulThree_of_not_modRepIsIrreducible (solution)
