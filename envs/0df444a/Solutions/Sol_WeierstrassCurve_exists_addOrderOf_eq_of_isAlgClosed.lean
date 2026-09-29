-- Prove2me | solution 1 for WeierstrassCurve.exists_addOrderOf_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/dadf216b-2620-5baf-b18c-ffd4e43a8d2a

import Mathlib
import Theorems.Thm_WeierstrassCurve_exists_addOrderOf_eq_prime_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_nsmul_eq_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_addOrderOf_eq_of_isAlgClosed
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

namespace ExordAssembly

private theorem tower {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ℕ) (hp : p.Prime) (hpK : (p : K) ≠ 0) :
    ∀ n : ℕ, 0 < n → ∃ T : W.toAffine.Point, addOrderOf T = p ^ n := by
  intro n hn
  induction n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      simpa using WeierstrassCurve.exists_addOrderOf_eq_prime_of_isAlgClosed W p hp hpK
    · obtain ⟨Tn, hTn⟩ := ih hnpos
      obtain ⟨S, hS⟩ := WeierstrassCurve.exists_nsmul_eq_of_isAlgClosed W p hpK Tn
      refine ⟨S, ?_⟩
      have hdiv : addOrderOf (p • S) = addOrderOf S / Nat.gcd (addOrderOf S) p :=
        addOrderOf_nsmul' S hp.ne_zero
      have h1 : addOrderOf S / Nat.gcd (addOrderOf S) p = p ^ n := by
        rw [← hdiv, hS, hTn]
      by_cases hpd : p ∣ addOrderOf S
      · have hg : Nat.gcd (addOrderOf S) p = p := by
          rw [Nat.gcd_comm]; exact Nat.gcd_eq_left hpd
        rw [hg] at h1
        exact (Nat.eq_mul_of_div_eq_right hpd h1).trans (by rw [pow_succ, mul_comm])
      · have hg : Nat.gcd (addOrderOf S) p = 1 := by
          rw [Nat.gcd_comm]; exact hp.coprime_iff_not_dvd.mpr hpd
        exfalso
        rw [hg, Nat.div_one] at h1
        exact hpd (h1 ▸ dvd_pow_self p hnpos.ne')

end ExordAssembly

theorem solution {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (M : ℕ) (hM : (M : K) ≠ 0) :
    ∃ T : W.toAffine.Point, addOrderOf T = M := by
  revert hM
  induction M using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro hM
    have hpK : (p : K) ≠ 0 := fun h0 => hM (by rw [Nat.cast_pow, h0, zero_pow hn.ne'])
    exact ExordAssembly.tower W p hp hpK n hn
  | zero => intro hM; exact absurd Nat.cast_zero hM
  | one => intro _; exact ⟨0, addOrderOf_zero⟩
  | coprime a b ha hb hab iha ihb =>
    intro hM
    rw [Nat.cast_mul] at hM
    obtain ⟨hMa, hMb⟩ := mul_ne_zero_iff.mp hM
    obtain ⟨Ta, hTa⟩ := iha hMa
    obtain ⟨Tb, hTb⟩ := ihb hMb
    refine ⟨Ta + Tb, ?_⟩
    have hco : (addOrderOf Ta).Coprime (addOrderOf Tb) := by rw [hTa, hTb]; exact hab
    rw [(AddCommute.all Ta Tb).addOrderOf_add_eq_mul_addOrderOf_of_coprime hco, hTa, hTb]

end S_WeierstrassCurve_exists_addOrderOf_eq_of_isAlgClosed
end P2MW
export P2MW.S_WeierstrassCurve_exists_addOrderOf_eq_of_isAlgClosed (solution)
