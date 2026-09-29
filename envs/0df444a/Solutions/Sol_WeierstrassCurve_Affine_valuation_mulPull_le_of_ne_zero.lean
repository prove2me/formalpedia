-- Prove2me | solution 1 for WeierstrassCurve.Affine.valuation_mulPull_le_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/572283c9-a388-5ac5-a4f4-bf6880fdcc02

import Definitions.Def_EllipticCurve_FunctionFieldPullback
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_exists_zsmul_some_eq_some_baseChange
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_valuation_mulPull_le_of_ne_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_valuation_mulPull_le_of_ne_zero.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_valuation_mulPull_le_of_ne_zero.WeierstrassCurve.Affine Polynomial IsDedekindDomain WithZero"
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "baseChange_ΨSq Affine map_map map baseChange_Φ ΨSq map_baseChange Affine.Point baseChange_ψ map_injective baseChange Affine.genericPoint card_torsion_of_isAlgClosed Affine.Point.exists_zsmul_some_eq_some_baseChange Affine.Point.smul_some_eq_zero_iff Affine.evalEval_psi_sq"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point.map_baseChange CoordinateRing map baseChange Point.some Point.map_injective FunctionField Point map_baseChange Point.map polynomial Point.xc_some Point.yc_some genericX genericY generic_nonsingular genericPoint transPull map_transPull_genericPoint MulGood mulPull infinite_point placeOf valuation_mulPull_le Point.exists_zsmul_some_eq_some_baseChange Point.smul_some_eq_zero_iff evalEval_psi_sq"
namespace PullEasy
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

variable {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]
  (W : WeierstrassCurve F) [W.IsElliptic]

theorem not_forall_zsmul_eq_zero {n : ℤ} (hn : (n : K) ≠ 0) : ¬ ∀ S : (W⁄K).Point, n • S = 0 := by
  intro hall
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m ∨ n = -m := ⟨n.natAbs, Int.natAbs_eq n⟩
  have hmK : (m : K) ≠ 0 := by
    intro h0
    apply hn
    rcases hm with rfl | rfl
    · rw [Int.cast_natCast, h0]
    · rw [Int.cast_neg, Int.cast_natCast, h0, neg_zero]
  have hcard := WeierstrassCurve.card_torsion_of_isAlgClosed (K := K) W hmK
  have htop : Submodule.torsionBy ℤ (W⁄K).Point m = ⊤ := by
    rw [eq_top_iff]
    intro S _
    rw [Submodule.mem_torsionBy_iff]
    rcases hm with rfl | rfl
    · exact hall S
    · have := hall S
      rwa [neg_smul, neg_eq_zero] at this
  rw [htop, Nat.card_congr (Submodule.topEquiv (R := ℤ) (M := (W⁄K).Point)).toEquiv] at hcard
  have hm0 : m ≠ 0 := by rintro rfl; exact hmK Nat.cast_zero
  haveI : Finite (W⁄K).Point := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hm0)
  exact (infinite_point W K).not_finite ‹_›

theorem zsmul_genericPoint_good {n : ℤ} (hn : (n : K) ≠ 0) : MulGood W K n := by
  constructor
  · intro h0
    apply not_forall_zsmul_eq_zero W hn
    intro S
    have := congrArg (Point.map (transPull W K S)) h0
    rw [map_zsmul, map_transPull_genericPoint, map_zero, smul_add, h0, zero_add, ← map_zsmul] at this
    exact Point.map_injective _ (this.trans (map_zero _).symm)
  · intro P hP
    apply not_forall_zsmul_eq_zero W hn
    intro S
    have := congrArg (Point.map (transPull W K S)) hP
    rw [map_zsmul, map_transPull_genericPoint, Point.map_baseChange, smul_add, hP, ← map_zsmul,
      add_eq_left] at this
    exact Point.map_injective _ (this.trans (map_zero _).symm)

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
theorem evalEval_map_mapRingHom {L : Type*} [CommRing L] (g : K →+* L) (q : K[X][Y]) (a b : L) :
    (q.map (mapRingHom g)).evalEval a b = q.eval₂ (eval₂RingHom g a) b := by
  have hφ : (evalEvalRingHom a b).comp (mapRingHom (mapRingHom g)) = eval₂RingHom (eval₂RingHom g a) b := by
    apply Polynomial.ringHom_ext
    · intro p
      simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_C, coe_evalRingHom, eval_C,
        eval_map, coe_eval₂RingHom, eval₂_C]
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_X, coe_evalRingHom, eval_X,
        eval_C, coe_eval₂RingHom, eval₂_X]
  exact RingHom.congr_fun hφ q

end WeierstrassCurve.Affine.PullEasy

open WeierstrassCurve.Affine.PullEasy in
theorem solution {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hn : (n : K) ≠ 0) (P : (W⁄K).Point) (hP : P ≠ 0) (hnP : (n : ℤ) • P ≠ 0) (h : (W⁄K).FunctionField) (k : ℕ) (hh : (placeOf W K ((n : ℤ) • P) hnP).valuation (W⁄K).FunctionField h ≤ exp (-(k : ℤ))) : (placeOf W K P hP).valuation (W⁄K).FunctionField (mulPull W K n h) ≤ exp (-(k : ℤ)) := by
  have hnK : ((n : ℤ) : K) ≠ 0 := by rwa [Int.cast_natCast]
  have hgood := zsmul_genericPoint_good (K := K) W hnK
  obtain ⟨ω, hω⟩ := WeierstrassCurve.Affine.Point.exists_zsmul_some_eq_some_baseChange W (n : ℤ)

  have hγns := generic_nonsingular W K
  have hψγ : ((W.baseChange (W⁄K).FunctionField).ψ n).evalEval (genericX W K) (genericY W K) ≠ 0 :=
    fun h0 => hgood.1 ((WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff
      (W.baseChange (W⁄K).FunctionField) hγns n).mpr h0)
  obtain ⟨hγ', hγeq⟩ := hω hγns hψγ

  rcases P with _ | ⟨a, b, hab⟩
  · exact absurd rfl hP
  have hψP : ((W.baseChange K).ψ n).evalEval a b ≠ 0 :=
    fun h0 => hnP ((WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff (W.baseChange K) hab n).mpr h0)
  obtain ⟨hP', hPeq⟩ := hω hab hψP
  have hΨP : ((W.baseChange K).ΨSq n).eval a ≠ 0 := by
    rw [← WeierstrassCurve.Affine.evalEval_psi_sq (W.baseChange K) hab.left n]
    exact pow_ne_zero 2 hψP

  have eΦ : (W.baseChange (W⁄K).FunctionField).Φ n = ((W.baseChange K).Φ n).map (algebraMap K (W⁄K).FunctionField) :=
    baseChange_Φ (W := W) (Algebra.ofId K (W⁄K).FunctionField) n
  have eΨ : (W.baseChange (W⁄K).FunctionField).ΨSq n = ((W.baseChange K).ΨSq n).map (algebraMap K (W⁄K).FunctionField) :=
    baseChange_ΨSq (W := W) (Algebra.ofId K (W⁄K).FunctionField) n
  have eψ : (W.baseChange (W⁄K).FunctionField).ψ n = ((W.baseChange K).ψ n).map (mapRingHom (algebraMap K (W⁄K).FunctionField)) :=
    baseChange_ψ (W := W) (Algebra.ofId K (W⁄K).FunctionField) n
  have eω : ω.map (mapRingHom (algebraMap F (W⁄K).FunctionField)) =
      (ω.map (mapRingHom (algebraMap F K))).map (mapRingHom (algebraMap K (W⁄K).FunctionField)) := by
    rw [Polynomial.map_map, mapRingHom_comp, ← IsScalarTower.algebraMap_eq F K (W⁄K).FunctionField]
  refine valuation_mulPull_le W K hgood ((W.baseChange K).Φ n) ((W.baseChange K).ΨSq n)
    (ω.map (mapRingHom (algebraMap F K))) ((W.baseChange K).ψ n) ?_ ?_ hP hnP ?_ hΨP ?_ hψP h k hh
  · have e : Affine.genericPoint W K = Point.some (genericX W K) (genericY W K) hγns := rfl
    rw [e, hγeq, Point.xc_some, eΦ, eΨ, eval_map, eval_map]
  · have e : Affine.genericPoint W K = Point.some (genericX W K) (genericY W K) hγns := rfl
    rw [e, hγeq, Point.yc_some, eω, eψ, evalEval_map_mapRingHom, evalEval_map_mapRingHom]
  · rw [hPeq, Point.xc_some, Point.xc_some]
  · rw [hPeq, Point.yc_some, Point.xc_some, Point.yc_some]

end S_WeierstrassCurve_Affine_valuation_mulPull_le_of_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_Affine_valuation_mulPull_le_of_ne_zero (solution)
