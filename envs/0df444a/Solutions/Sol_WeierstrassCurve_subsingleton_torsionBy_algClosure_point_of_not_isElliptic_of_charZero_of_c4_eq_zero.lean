-- Prove2me | solution 1 for WeierstrassCurve.subsingleton_torsionBy_algClosure_point_of_not_isElliptic_of_charZero_of_c4_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6ca68b59-ccf2-5dfe-90b7-aed00f991400

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_zero_of_c4_eq_zero_of_c6_eq_zero
import Theorems.Thm_WeierstrassCurve_nonempty_addEquiv_affine_point_zero_of_charZero
import Theorems.Thm_WeierstrassCurve_VariableChange_nonempty_addEquiv_affine_point
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_subsingleton_torsionBy_algClosure_point_of_not_isElliptic_of_charZero_of_c4_eq_zero
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"

set_option maxHeartbeats 6400000
open scoped WeierstrassCurve.Affine
open WeierstrassCurve

theorem solution
    (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (hW : ¬ W.IsElliptic)
    (hc4 : W.c₄ = 0) (n : ℕ) (hn : n ≠ 0) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    Subsingleton (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point (n:ℤ)) := by
  letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _

  have hΔ : W.Δ = 0 := by by_contra h; exact hW ⟨isUnit_iff_ne_zero.mpr h⟩
  have hc6 : W.c₆ = 0 := by
    have hrel := WeierstrassCurve.c_relation W
    rw [hΔ, hc4, mul_zero, zero_pow (by norm_num), zero_sub] at hrel
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (neg_eq_zero.mp hrel.symm)

  haveI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  have hc4' : (W.baseChange (AlgebraicClosure K)).c₄ = 0 := by
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, hc4, _root_.map_zero]
  have hc6' : (W.baseChange (AlgebraicClosure K)).c₆ = 0 := by
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₆, hc6, _root_.map_zero]

  obtain ⟨C, hCeq⟩ :=
    WeierstrassCurve.exists_variableChange_smul_eq_zero_of_c4_eq_zero_of_c6_eq_zero
      (W.baseChange (AlgebraicClosure K)) hc4' hc6'

  obtain ⟨eC⟩ :=
    WeierstrassCurve.VariableChange.nonempty_addEquiv_affine_point
      (W.baseChange (AlgebraicClosure K)) C

  obtain ⟨eB⟩ := WeierstrassCurve.nonempty_addEquiv_affine_point_zero_of_charZero
    (AlgebraicClosure K)

  let e : (W⁄(AlgebraicClosure K)).Point ≃+ (AlgebraicClosure K) :=
    eC.symm.trans (hCeq ▸ eB)

  suffices hBot :
      Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point (n:ℤ) = ⊥ by
    exact hBot ▸ inferInstanceAs (Subsingleton (⊥ : Submodule ℤ _))
  rw [Submodule.eq_bot_iff]
  intro P hP
  rw [Submodule.mem_torsionBy_iff] at hP

  apply e.injective
  rw [_root_.map_zero]
  have heP : (n:ℤ) • (e P : AlgebraicClosure K) = 0 := by
    rw [← map_zsmul e (n:ℤ) P, hP, _root_.map_zero]
  have hn' : ((n:ℤ) : AlgebraicClosure K) ≠ 0 := by
    exact_mod_cast hn
  rw [zsmul_eq_mul] at heP
  exact (mul_eq_zero.mp heP).resolve_left hn'

end S_WeierstrassCurve_subsingleton_torsionBy_algClosure_point_of_not_isElliptic_of_charZero_of_c4_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_subsingleton_torsionBy_algClosure_point_of_not_isElliptic_of_charZero_of_c4_eq_zero (solution)
