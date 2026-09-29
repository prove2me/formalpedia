-- Prove2me | solution 1 for WeierstrassCurve.Affine.zsmul_genericPoint_good
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/ebd31027-2552-56ad-bc35-9301962545fb

import Definitions.Def_EllipticCurve_FunctionFieldPullback
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_zsmul_genericPoint_good
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_zsmul_genericPoint_good.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_zsmul_genericPoint_good.WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map map_baseChange map_injective Affine.MulGood card_torsion_of_isAlgClosed"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point.map_baseChange map Point.map_injective Point map_baseChange Point.map transPull map_transPull_genericPoint MulGood infinite_point"
namespace Good
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K] [IsAlgClosed K] [W.IsElliptic]

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

end WeierstrassCurve.Affine.Good

open WeierstrassCurve.Affine.Good in
theorem solution {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K] [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] {n : ℤ} (hn : (n : K) ≠ 0) : WeierstrassCurve.Affine.MulGood W K n := by
  constructor
  · intro h0
    apply not_forall_zsmul_eq_zero W K hn
    intro S
    have := congrArg (Point.map (transPull W K S)) h0
    rw [map_zsmul, map_transPull_genericPoint, map_zero, smul_add, h0, zero_add, ← map_zsmul] at this
    exact Point.map_injective _ (this.trans (map_zero _).symm)
  · intro P hP
    apply not_forall_zsmul_eq_zero W K hn
    intro S
    have := congrArg (Point.map (transPull W K S)) hP
    rw [map_zsmul, map_transPull_genericPoint, Point.map_baseChange, smul_add, hP, ← map_zsmul,
      add_eq_left] at this
    exact Point.map_injective _ (this.trans (map_zero _).symm)

end S_WeierstrassCurve_Affine_zsmul_genericPoint_good
end P2MW
export P2MW.S_WeierstrassCurve_Affine_zsmul_genericPoint_good (solution)
