-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.mem_valuationSubring_of_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8b9bc34f-8e5b-550b-a8d9-d877bb673990

import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_mem_valuationSubring_of_nsmul_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K) (W : WeierstrassCurve K) [W.IsElliptic] (h₁ : W.a₁ ∈ A) (h₂ : W.a₂ ∈ A) (h₃ : W.a₃ ∈ A) (h₄ : W.a₄ ∈ A) (h₆ : W.a₆ ∈ A) {n : ℕ} (hn : Odd n) (hnA : (n : K) ∉ A.nonunits) {x y : K} (h : W.toAffine.Nonsingular x y) (hP : n • Point.some x y h = 0) : x ∈ A := by

  have hn0 : (n : K) ≠ 0 := by
    intro h0
    apply hnA
    rw [h0, ValuationSubring.mem_nonunits_iff, Valuation.map_zero]
    exact zero_lt_one

  have hroot : (W.preΨ' n).eval x = 0 :=
    (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hn h).mp hP
  by_contra hxA
  have hvx : 1 < A.valuation x := by
    rw [← not_le]
    exact fun hle => hxA ((A.valuation_le_one_iff x).mp hle)

  have hcoef : ∀ i, A.valuation ((W.preΨ' n).coeff i) ≤ 1 := by
    intro i
    let WA : WeierstrassCurve A := ⟨⟨_, h₁⟩, ⟨_, h₂⟩, ⟨_, h₃⟩, ⟨_, h₄⟩, ⟨_, h₆⟩⟩
    have hW : WA.map (algebraMap A K) = W := rfl
    rw [← hW, WeierstrassCurve.map_preΨ', Polynomial.coeff_map]
    exact A.valuation_le_one _

  set d := (W.preΨ' n).natDegree with hd
  have hlead : A.valuation ((W.preΨ' n).coeff d) = 1 := by
    rw [hd, Polynomial.coeff_natDegree, W.leadingCoeff_preΨ' hn0, if_neg (Nat.not_even_iff_odd.mpr hn)]
    refine le_antisymm ?_ ?_
    · exact (A.valuation_le_one_iff _).mpr (natCast_mem A n)
    · rw [← not_lt, ← ValuationSubring.mem_nonunits_iff]
      exact hnA

  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ] at hroot
  have hxd : A.valuation x ^ d ≠ 0 := pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hvx))
  have hlt : A.valuation (∑ i ∈ Finset.range d, (W.preΨ' n).coeff i * x ^ i) <
      A.valuation x ^ d := by
    apply Valuation.map_sum_lt _ hxd
    intro i hi
    rw [map_mul, map_pow]
    calc A.valuation ((W.preΨ' n).coeff i) * A.valuation x ^ i
        ≤ 1 * A.valuation x ^ i := by gcongr; exact hcoef i
      _ = A.valuation x ^ i := one_mul _
      _ < A.valuation x ^ d := pow_lt_pow_right₀ hvx (Finset.mem_range.mp hi)
  have heq : A.valuation ((W.preΨ' n).coeff d * x ^ d) = A.valuation x ^ d := by
    rw [map_mul, map_pow, hlead, one_mul]
  have hsum : ∑ i ∈ Finset.range d, (W.preΨ' n).coeff i * x ^ i =
      -((W.preΨ' n).coeff d * x ^ d) := eq_neg_of_add_eq_zero_left hroot
  rw [hsum, Valuation.map_neg, heq] at hlt
  exact lt_irrefl _ hlt

end S_WeierstrassCurve_Affine_Point_mem_valuationSubring_of_nsmul_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_mem_valuationSubring_of_nsmul_eq_zero (solution)
