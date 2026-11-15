-- Prove2me | solution 1 for PrimeLocal.exists_originParam_evalSeries_nthSeries_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T02:22:50.200797+00:00
-- url     : https://prove2.me/submissions/7cbf4716-2a98-4cb6-990c-116355f1f75d

import Mathlib
import Definitions.Def_WeierstrassCurve_TorsionIntegral
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroup

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine NNReal
universe u v

open PowerSeries MvPowerSeries

namespace PrimeLocal
theorem _root_.solution (p : ℕ) [Fact p.Prime] [DecidableEq ℂ_[p]] (D : WeierstrassCurve 𝓞_ℂ_[p]) (hΔ : D.Δ ≠ 0) (F : FormalGroup 𝓞_ℂ_[p]) [F.IsComm] (hF : F.toPowerSeries = D.formalGroupLawFixed) (x y : ℂ_[p]) (h : (D.map (PadicComplexInt p).subtype).toAffine.Nonsingular x y) (hx : 1 < ‖x‖) {n : ℕ} (hn : n • (WeierstrassCurve.Affine.Point.some x y h) = 0) : ∃ t : 𝓞_ℂ_[p], (t : ℂ_[p]) = -x / y ∧ t ≠ 0 ∧ ‖(t : ℂ_[p])‖ < 1 ∧ FormalGroup.evalSeries (F.nthSeries n) t = 0 := by
  -- Establish the comparisons before specializing to the p-adic integer ring.
  revert p
  revert n
  have evaluated_origin_chart {R K σ : Type} [CommRing R] [IsDomain R] [Field K]
      (D : WeierstrassCurve R) (f : R →+* K) [(D.map f).IsElliptic]
      (e : MvPowerSeries σ R →+* K) (heC : ∀ r, e (MvPowerSeries.C r) = f r)
      (a : MvPowerSeries σ R) (ha : MvPowerSeries.constantCoeff a = 0) :
      (e (D.fgGenW a) = 0 ↔ e a = 0) ∧
      (e a ≠ 0 → (D.map f).toAffine.Nonsingular
        (e a / e (D.fgGenW a)) (-1 / e (D.fgGenW a))) := by
    set_option backward.isDefEq.respectTransparency.types true in
      have hC : ∀ r, e (MvPowerSeries.C r) = f r := heC
      have has : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
      have hw : e (D.fgGenW a) = (e a)^3 + f D.a₁ * e a * e (D.fgGenW a) +
          f D.a₂ * (e a)^2 * e (D.fgGenW a) + f D.a₃ * e (D.fgGenW a)^2 +
          f D.a₄ * e a * e (D.fgGenW a)^2 + f D.a₆ * e (D.fgGenW a)^3 := by
        have hh := congrArg (PowerSeries.substAlgHom (R := R) has) D.formalW_eq
        simp only [_root_.map_add, _root_.map_mul, _root_.map_pow, PowerSeries.substAlgHom_X,
          PowerSeries.coe_substAlgHom, PowerSeries.subst_C] at hh
        have hh' := congrArg e hh
        simpa only [_root_.map_add, _root_.map_mul, _root_.map_pow, hC, fgGenW] using hh'
      have hz : e (D.fgGenW a) = 0 ↔ e a = 0 := by
        constructor
        · intro h
          rw [h] at hw
          have hp : e a ^ 3 = 0 := by simpa using hw.symm
          exact (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hp
        · intro h
          obtain ⟨g, hg⟩ := D.X_pow_three_dvd_formalW
          have hh := congrArg (PowerSeries.substAlgHom (R := R) has) hg
          simp only [_root_.map_mul, _root_.map_pow, PowerSeries.substAlgHom_X,
            PowerSeries.coe_substAlgHom] at hh
          have hh' := congrArg e hh
          simpa only [_root_.map_mul, _root_.map_pow, h, zero_pow (by decide : 3 ≠ 0), zero_mul, fgGenW]
            using hh'
      refine ⟨hz, fun ha0 => ?_⟩
      have hw0 : e (D.fgGenW a) ≠ 0 := fun hh => ha0 (hz.mp hh)
      apply (WeierstrassCurve.Affine.equation_iff_nonsingular).mp
      rw [WeierstrassCurve.Affine.equation_iff]
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
        WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
      field_simp
      linear_combination hw

  have evaluated_formal_law {R K : Type} [CommRing R] [IsDomain R] [Field K] [DecidableEq K]
      (D : WeierstrassCurve R) (f : R →+* K) [(D.map f).IsElliptic]
      (e : MvPowerSeries (Fin 2) R →+* K) (heC : ∀ r, e (MvPowerSeries.C r) = f r)
      (hzchart : ∀ (g : MvPowerSeries (Fin 2) R) (hg : MvPowerSeries.constantCoeff g = 0),
        e (D.fgGenW g) = 0 ↔ e g = 0)
      (hnchart : ∀ (g : MvPowerSeries (Fin 2) R) (hg : MvPowerSeries.constantCoeff g = 0),
        e g ≠ 0 → (D.map f).toAffine.Nonsingular
          (e g / e (D.fgGenW g)) (-1 / e (D.fgGenW g)))
      (ha0 : e (MvPowerSeries.X (0 : Fin 2)) ≠ 0)
      (hb0 : e (MvPowerSeries.X (1 : Fin 2)) ≠ 0) :
      (if hz : e D.formalGroupLawFixed=0 then 0 else
        Affine.Point.some (e D.formalGroupLawFixed/e (D.fgGenW D.formalGroupLawFixed))
          (-1/e (D.fgGenW D.formalGroupLawFixed))
          (hnchart D.formalGroupLawFixed D.constantCoeff_formalGroupLawFixed hz)) =
        Affine.Point.some (e (MvPowerSeries.X 0)/e (D.fgGenW (MvPowerSeries.X 0)))
          (-1/e (D.fgGenW (MvPowerSeries.X 0)))
          (hnchart (MvPowerSeries.X 0) (MvPowerSeries.constantCoeff_X 0) ha0) +
        Affine.Point.some (e (MvPowerSeries.X 1)/e (D.fgGenW (MvPowerSeries.X 1)))
          (-1/e (D.fgGenW (MvPowerSeries.X 1)))
          (hnchart (MvPowerSeries.X 1) (MvPowerSeries.constantCoeff_X 1) hb0) := by
    set_option backward.isDefEq.respectTransparency.types true in
      rename' D => ambientCurve
      rename' f => ambientMap
      rename' e => ambientEvaluation
      have evaluated_chart_chord  (E : WeierstrassCurve K)
          (a b c wa wb wc S Nu : K) (hwa : wa ≠ 0) (hwb : wb ≠ 0) (hwc : wc ≠ 0) (hNu : Nu ≠ 0)
          (hRa : wa = S*a+Nu) (hRb : wb = S*b+Nu) (hRc : wc = S*c+Nu)
          (hax : E.toAffine.addX (a/wa) (b/wb) (S/Nu)=c/wc)
          (hx : a/wa ≠ b/wb)
          (ha : E.toAffine.Nonsingular (a/wa) (-1/wa))
          (hb : E.toAffine.Nonsingular (b/wb) (-1/wb))
          (hc : E.toAffine.Nonsingular (c/wc) (-1/wc)) :
          Point.some (a/wa) (-1/wa) ha + Point.some (b/wb) (-1/wb) hb =
            -Point.some (c/wc) (-1/wc) hc := by
        clear! ambientCurve ambientMap ambientEvaluation
        have hs : E.toAffine.slope (a/wa) (b/wb) (-1/wa) (-1/wb) = S/Nu := by
          rw [Affine.slope_of_X_ne hx]
          apply (div_eq_div_iff (sub_ne_zero.mpr hx) hNu).mpr
          field_simp
          rw [hRa,hRb]
          ring
        have hcol : -1/wc-(-1/wa)=(S/Nu)*(c/wc-a/wa) := by
          field_simp
          rw [hRa,hRc]
          ring
        rw [Point.add_some (by intro hh; exact hx hh.1),Point.neg_some,Point.some.injEq,hs]
        refine ⟨hax,?_⟩
        simp only [Affine.addY,Affine.negAddY,Affine.negY]
        rw [hax]
        linear_combination hcol
      have evaluated_inverse 
          (D : WeierstrassCurve R) (f : R →+* K)
          (e : MvPowerSeries (Fin 2) R →+* K)
          (heC : ∀ r, e (MvPowerSeries.C r) = f r)
          (c' : MvPowerSeries (Fin 2) R)
          (hc' : MvPowerSeries.constantCoeff c' = 0)
          (hw : e (D.fgGenW c') ≠ 0)
          (hwi : e (D.fgGenW (PowerSeries.subst c' D.fgInv)) ≠ 0)
          (hnc : (D.map f).toAffine.Nonsingular
            (e c' / e (D.fgGenW c')) (-1 / e (D.fgGenW c')))
          (hni : (D.map f).toAffine.Nonsingular
            (e (PowerSeries.subst c' D.fgInv) /
              e (D.fgGenW (PowerSeries.subst c' D.fgInv)))
            (-1 / e (D.fgGenW (PowerSeries.subst c' D.fgInv)))) :
          WeierstrassCurve.Affine.Point.some _ _ hni =
            -WeierstrassCurve.Affine.Point.some _ _ hnc := by
        clear! ambientCurve ambientMap ambientEvaluation
        classical
        have hc's : PowerSeries.HasSubst c' := PowerSeries.HasSubst.of_constantCoeff_zero hc'
        set ic' := PowerSeries.subst c' D.fgInv with hicdef
        set w := D.fgGenW c' with hwdef
        have hccw : MvPowerSeries.constantCoeff w = 0 :=
          PowerSeries.constantCoeff_subst_eq_zero hc' D.formalW D.constantCoeff_formalW
        have hccic : MvPowerSeries.constantCoeff ic' = 0 := D.constantCoeff_subst_fgInv hc'

        have heq_c : w = c' ^ 3 + MvPowerSeries.C D.a₁ * c' * w + MvPowerSeries.C D.a₂ * c' ^ 2 * w
            + MvPowerSeries.C D.a₃ * w ^ 2 + MvPowerSeries.C D.a₄ * c' * w ^ 2
            + MvPowerSeries.C D.a₆ * w ^ 3 := by
          have h := congrArg (PowerSeries.substAlgHom (R := R) hc's) D.formalW_eq
          simp only [_root_.map_add, _root_.map_mul, _root_.map_pow, PowerSeries.substAlgHom_X,
            PowerSeries.coe_substAlgHom, PowerSeries.subst_C] at h
          rw [show PowerSeries.subst c' D.formalW = D.fgGenW c' from rfl, ← hwdef] at h
          exact h

        set Dc' := PowerSeries.subst c' D.fgInvDenom with hDcdef
        have hDcexp : Dc' = 1 - MvPowerSeries.C D.a₁ * c' - MvPowerSeries.C D.a₃ * w := by
          have h := congrArg (PowerSeries.substAlgHom (R := R) hc's)
            (show D.fgInvDenom
              = 1 - PowerSeries.C D.a₁ * PowerSeries.X - PowerSeries.C D.a₃ * D.formalW from rfl)
          simp only [_root_.map_sub, _root_.map_mul, _root_.map_one, PowerSeries.substAlgHom_X,
            PowerSeries.coe_substAlgHom, PowerSeries.subst_C] at h
          rw [← hDcdef, show PowerSeries.subst c' D.formalW = D.fgGenW c' from rfl, ← hwdef] at h
          exact h
        have hccDc' : MvPowerSeries.constantCoeff Dc' = 1 := by
          rw [hDcexp]
          simp only [_root_.map_sub, _root_.map_mul, _root_.map_one, MvPowerSeries.constantCoeff_C, hc', hccw,
            mul_zero, sub_zero]
        set iD := MvPowerSeries.invOfUnit Dc' 1 with hiDdef
        have hinv_raw : Dc' * iD = 1 := MvPowerSeries.mul_invOfUnit Dc' 1 (by rw [hccDc']; simp)
        have hinv_c : (1 - MvPowerSeries.C D.a₁ * c' - MvPowerSeries.C D.a₃ * w) * iD = 1 := by
          rw [← hDcexp]; exact hinv_raw

        have hIrel_c : ic' * Dc' = -c' := by
          have h := congrArg (PowerSeries.substAlgHom (R := R) hc's) D.fgInv_mul_fgInvDenom
          simp only [_root_.map_mul, _root_.map_neg, PowerSeries.substAlgHom_X, PowerSeries.coe_substAlgHom] at h
          rw [hicdef, hDcdef]; exact h
        have hic : ic' = -c' * iD := by
          rw [← mul_one ic', ← hinv_raw, ← mul_assoc, hIrel_c, neg_mul]

        have hccU : MvPowerSeries.constantCoeff (-w * iD) = 0 := by
          simp only [_root_.map_mul, _root_.map_neg, hccw, neg_zero, zero_mul]
        have hUeq : (-w * iD) = ic' ^ 3 + MvPowerSeries.C D.a₁ * ic' * (-w * iD)
            + MvPowerSeries.C D.a₂ * ic' ^ 2 * (-w * iD) + MvPowerSeries.C D.a₃ * (-w * iD) ^ 2
            + MvPowerSeries.C D.a₄ * ic' * (-w * iD) ^ 2 + MvPowerSeries.C D.a₆ * (-w * iD) ^ 3 := by
          rw [hic]
          linear_combination (iD * w * (iD + 1)) * hinv_c + (-(iD) ^ 3) * heq_c

        have hWic : D.fgGenW ic' = -w * iD := by
          have huniq := D.eq_subst_formalW hccic hccU hUeq
          rw [fgGenW]; exact huniq.symm

        have h0y : D.fgGenW ic' * (1 - MvPowerSeries.C D.a₁ * c' - MvPowerSeries.C D.a₃ * w) = -w := by
          rw [hWic, mul_assoc,
            mul_comm iD (1-MvPowerSeries.C D.a₁*c'-MvPowerSeries.C D.a₃*w), hinv_c, mul_one]
        have h0x : ic' * w = c' * D.fgGenW ic' := by
          rw [hWic, hic]; ring

        rw [WeierstrassCurve.Affine.Point.neg_some,
          WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · rw [div_eq_div_iff hwi hw]
          have h := congrArg e h0x
          simpa only [_root_.map_mul] using h
        · simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁,
            WeierstrassCurve.map_a₃]
          have h := congrArg e h0y
          simp only [_root_.map_mul, _root_.map_sub, _root_.map_one, _root_.map_neg, heC] at h
          change -1 / e (D.fgGenW ic') = -(-1 / e w) - f D.a₁ * (e c' / e w) - f D.a₃
          have hw' : e w ≠ 0 := hw
          have hwi' : e (D.fgGenW ic') ≠ 0 := hwi
          field_simp [hw', hwi']
          linear_combination -h
      have universal_chart_quadratic {R : Type} [CommRing R] [NoZeroDivisors R] (E : WeierstrassCurve R)
          (a b S Nu : R) (hab : a ≠ b)
          (ha : S*a+Nu = a^3 + E.a₁*a*(S*a+Nu) + E.a₂*a^2*(S*a+Nu) + E.a₃*(S*a+Nu)^2 + E.a₄*a*(S*a+Nu)^2 + E.a₆*(S*a+Nu)^3)
          (hb : S*b+Nu = b^3 + E.a₁*b*(S*b+Nu) + E.a₂*b^2*(S*b+Nu) + E.a₃*(S*b+Nu)^2 + E.a₄*b*(S*b+Nu)^2 + E.a₆*(S*b+Nu)^3) :
          (1+E.a₂*S+E.a₄*S^2+E.a₆*S^3)*(a^2+a*b+b^2) +
            (E.a₁*S+E.a₂*Nu+E.a₃*S^2+2*E.a₄*S*Nu+3*E.a₆*S^2*Nu)*(a+b) +
            (E.a₁*Nu+2*E.a₃*S*Nu+E.a₄*Nu^2+3*E.a₆*Nu^2*S-S) = 0 := by
        clear! ambientCurve ambientMap ambientEvaluation
        clear evaluated_chart_chord evaluated_inverse
        apply (mul_eq_zero.mp (show (a-b) * ((1+E.a₂*S+E.a₄*S^2+E.a₆*S^3)*(a^2+a*b+b^2) +
            (E.a₁*S+E.a₂*Nu+E.a₃*S^2+2*E.a₄*S*Nu+3*E.a₆*S^2*Nu)*(a+b) +
            (E.a₁*Nu+2*E.a₃*S*Nu+E.a₄*Nu^2+3*E.a₆*Nu^2*S-S)) = 0 by
          linear_combination hb-ha)).resolve_left (sub_ne_zero.mpr hab)
      -- The product identity survives arbitrary specialization, including a=b.

      have chart_product_relation  (E : WeierstrassCurve K) (a b c S Nu : K)
          (hr : S*a+Nu = a^3 + E.a₁*a*(S*a+Nu) + E.a₂*a^2*(S*a+Nu) + E.a₃*(S*a+Nu)^2 + E.a₄*a*(S*a+Nu)^2 + E.a₆*(S*a+Nu)^3)
          (hq : (1+E.a₂*S+E.a₄*S^2+E.a₆*S^3)*(a^2+a*b+b^2) +
            (E.a₁*S+E.a₂*Nu+E.a₃*S^2+2*E.a₄*S*Nu+3*E.a₆*S^2*Nu)*(a+b) +
            (E.a₁*Nu+2*E.a₃*S*Nu+E.a₄*Nu^2+3*E.a₆*Nu^2*S-S) = 0)
          (hv : (1+E.a₂*S+E.a₄*S^2+E.a₆*S^3)*(c+a+b) +
            (E.a₁*S+E.a₂*Nu+E.a₃*S^2+2*E.a₄*S*Nu+3*E.a₆*S^2*Nu) = 0) :
          (1+E.a₂*S+E.a₄*S^2+E.a₆*S^3)*a*b*c = Nu-E.a₃*Nu^2-E.a₆*Nu^3 := by
        clear! ambientCurve ambientMap ambientEvaluation
        clear evaluated_chart_chord evaluated_inverse universal_chart_quadratic
        linear_combination a*b*hv-a*hq-hr

      have evaluated_chart_zero_sum (E : WeierstrassCurve K) (a b wa wb s d : K)
          (hwa : wa≠0) (hwb : wb≠0) (hRa : wa=s*a) (hRb : wb=s*b)
          (hv : d*(a+b)+(E.a₁*s+E.a₃*s^2)=0) (hp : d*a*b = -s)
          (hna : E.toAffine.Nonsingular (a/wa) (-1/wa))
          (hnb : E.toAffine.Nonsingular (b/wb) (-1/wb)) :
          Affine.Point.some _ _ hna + Affine.Point.some _ _ hnb = 0 := by
        clear! ambientCurve ambientMap ambientEvaluation
        have hx : a/wa=b/wb := by
          apply (div_eq_div_iff hwa hwb).mpr
          rw [hRa,hRb]
          ring
        have hy : -1/wa=E.toAffine.negY (b/wb) (-1/wb) := by
          change -1/wa = -(-1/wb)-E.a₁*(b/wb)-E.a₃
          field_simp [hwa,hwb]
          rw [hRa,hRb]
          linear_combination a*b*hv-(a+b)*hp
        exact Affine.Point.add_of_Y_eq hx hy
      have evaluated_chart_doubling  (E : WeierstrassCurve K)
          (a c wa wc S Nu : K) (hwa : wa ≠ 0) (hwc : wc ≠ 0) (hNu : Nu ≠ 0)
          (hRa : wa = S * a + Nu) (hRc : wc = S * c + Nu)
          (hroot : wa = a ^ 3 + E.a₁ * a * wa + E.a₂ * a ^ 2 * wa + E.a₃ * wa ^ 2 +
            E.a₄ * a * wa ^ 2 + E.a₆ * wa ^ 3)
          (hQ : 3 * (1 + E.a₂ * S + E.a₄ * S ^ 2 + E.a₆ * S ^ 3) * a ^ 2 +
            2 * (E.a₁ * S + E.a₂ * Nu + E.a₃ * S ^ 2 + 2 * E.a₄ * S * Nu + 3 * E.a₆ * S ^ 2 * Nu) * a +
            (E.a₁ * Nu + 2 * E.a₃ * S * Nu + E.a₄ * Nu ^ 2 + 3 * E.a₆ * Nu ^ 2 * S - S) = 0)
          (hax : E.toAffine.addX (a/wa) (a/wa) (S/Nu)=c/wc)
          (ha : E.toAffine.Nonsingular (a / wa) (-1 / wa))
          (hc : E.toAffine.Nonsingular (c / wc) (-1 / wc)) :
          Point.some (a / wa) (-1 / wa) ha + Point.some (a / wa) (-1 / wa) ha =
            -Point.some (c / wc) (-1 / wc) hc := by
        clear! ambientCurve ambientMap ambientEvaluation
        have htan : (2 * (-1 / wa) + E.a₁ * (a / wa) + E.a₃) * S =
            (3 * (a / wa) ^ 2 + 2 * E.a₂ * (a / wa) + E.a₄ - E.a₁ * (-1 / wa)) * Nu := by
          field_simp
          rw [hRa] at hroot ⊢
          linear_combination -3 * S * hroot - (a * S + Nu) * hQ
        have hden : 2 * (-1 / wa) + E.a₁ * (a / wa) + E.a₃ ≠ 0 := by
          intro hz
          have hnum : 3 * (a / wa) ^ 2 + 2 * E.a₂ * (a / wa) + E.a₄ - E.a₁ * (-1 / wa) = 0 := by
            apply (mul_eq_zero.mp (show (3 * (a / wa) ^ 2 + 2 * E.a₂ * (a / wa) + E.a₄ - E.a₁ * (-1 / wa)) * Nu = 0 by
              rw [← htan, hz, zero_mul])).resolve_right hNu
          rcases ha.2 with hnx | hny
          · apply hnx
            rw [Affine.evalEval_polynomialX]
            change E.a₁ * (-1 / wa) - (3 * (a / wa) ^ 2 + 2 * E.a₂ * (a / wa) + E.a₄) = 0
            linear_combination -hnum
          · apply hny
            rw [Affine.evalEval_polynomialY]
            exact hz
        have hy : -1 / wa ≠ E.toAffine.negY (a / wa) (-1 / wa) := by
          intro hh
          apply hden
          change -1 / wa = -(-1 / wa) - E.a₁ * (a / wa) - E.a₃ at hh
          linear_combination hh
        have hs : E.toAffine.slope (a / wa) (a / wa) (-1 / wa) (-1 / wa) = S / Nu := by
          rw [Affine.slope_of_Y_ne rfl hy]
          have hd : -1 / wa - E.toAffine.negY (a / wa) (-1 / wa) =
              2 * (-1 / wa) + E.a₁ * (a / wa) + E.a₃ := by
            change -1 / wa - (-(-1 / wa) - E.a₁ * (a / wa) - E.a₃) = _
            ring
          rw [hd]
          apply (div_eq_div_iff hden hNu).mpr
          simpa only [mul_comm] using htan.symm
        have hcol : -1 / wc - (-1 / wa) = (S / Nu) * (c / wc - a / wa) := by
          field_simp
          rw [hRa, hRc]
          ring
        rw [Point.add_some (by intro hh; exact hy hh.2), Point.neg_some, Point.some.injEq, hs]
        refine ⟨hax, ?_⟩
        simp only [Affine.addY, Affine.negAddY, Affine.negY]
        rw [hax]
        linear_combination hcol
      have chart_product_of_vieta 
          (E : WeierstrassCurve K) (a b c s n d wa wb wc : K)
          (hD : d=1+E.a₂*s+E.a₄*s^2+E.a₆*s^3)
          (hWa : wa=s*a+n) (hWb : wb=s*b+n) (hWc : wc=s*c+n)
          (hv : d*(a+b+c)+(E.a₁*s+E.a₂*n+E.a₃*s^2+2*E.a₄*s*n+3*E.a₆*s^2*n)=0)
          (hpair : d*(a*b+a*c+b*c)=E.a₁*n+2*E.a₃*s*n+E.a₄*n^2+3*E.a₆*n^2*s-s)
          (hp : d*a*b*c=n-E.a₃*n^2-E.a₆*n^3) :
          d*(wa*wb*wc)=n^3 := by
        clear! ambientCurve ambientMap ambientEvaluation
        rw [hWa,hWb,hWc]
        linear_combination s^3*hp+s^2*n*hpair+s*n^2*hv+n^3*hD
      have chart_addX_of_vieta 
          (E : WeierstrassCurve K) (a b c s n d wa wb wc : K)
          (hd : d ≠ 0) (hn : n ≠ 0) (hwa0 : wa ≠ 0) (hwb0 : wb ≠ 0) (hwc0 : wc ≠ 0)
          (hD : d=1+E.a₂*s+E.a₄*s^2+E.a₆*s^3)
          (hWa : wa=s*a+n) (hWb : wb=s*b+n) (hWc : wc=s*c+n)
          (hv : d*(a+b+c)+(E.a₁*s+E.a₂*n+E.a₃*s^2+2*E.a₄*s*n+3*E.a₆*s^2*n)=0)
          (hpair : d*(a*b+a*c+b*c)=E.a₁*n+2*E.a₃*s*n+E.a₄*n^2+3*E.a₆*n^2*s-s)
          (hp : d*a*b*c=n-E.a₃*n^2-E.a₆*n^3) :
          E.toAffine.addX (a/wa) (b/wb) (s/n) = c/wc := by
        clear! ambientCurve ambientMap ambientEvaluation
        let J := s^2+E.a₁*s*n-E.a₂*n^2
        have hprod := chart_product_of_vieta E a b c s n d wa wb wc hD hWa hWb hWc hv hpair hp
        have hweighted : d*(a*wb*wc+b*wa*wc+c*wa*wb)=n*J := by
          rw [hWa,hWb,hWc]
          dsimp only [J]
          linear_combination 3*s^2*hp+2*s*n*hpair+n^2*hv
        have hcommon : a/wa+b/wb+c/wc =
            (a*wb*wc+b*wa*wc+c*wa*wb)/(wa*wb*wc) := by
          field_simp [hwa0,hwb0,hwc0]
          <;> ring
        have hsum : a/wa+b/wb+c/wc = J/n^2 := by
          rw [hcommon]
          apply (div_eq_div_iff (mul_ne_zero (mul_ne_zero hwa0 hwb0) hwc0) (pow_ne_zero 2 hn)).mpr
          apply mul_left_cancel₀ hd
          calc
            _ = (d*(a*wb*wc+b*wa*wc+c*wa*wb))*n^2 :=
              (mul_assoc d (a*wb*wc+b*wa*wc+c*wa*wb) (n^2)).symm
            _ = (n*J)*n^2 := congrArg (fun z => z*n^2) hweighted
            _ = J*n^3 := by ring
            _ = J*(d*(wa*wb*wc)) := by rw [hprod]
            _ = _ := by ac_rfl
        have hJ : J/n^2=(s/n)^2+E.a₁*(s/n)-E.a₂ := by
          dsimp only [J]
          field_simp [hn]
          <;> ring
        rw [hJ] at hsum
        unfold WeierstrassCurve.Affine.addX
        linear_combination -hsum
      rename' ambientCurve => D
      rename' ambientMap => f
      rename' ambientEvaluation => e
      classical
      let A : MvPowerSeries (Fin 2) R := MvPowerSeries.X 0
      let B : MvPowerSeries (Fin 2) R := MvPowerSeries.X 1
      let C := D.fgZ3Fixed
      let S := D.fgSlope
      let N := D.fgNu
      let Q := D.fgZ3Denom
      let E := D.map f
      let a := e A
      let b := e B
      let c := e C
      let s := e S
      let n := e N
      let d := e Q
      let wa := e (D.fgGenW A)
      let wb := e (D.fgGenW B)
      let wc := e (D.fgGenW C)
      have hA : MvPowerSeries.constantCoeff A = 0 := MvPowerSeries.constantCoeff_X 0
      have hB : MvPowerSeries.constantCoeff B = 0 := MvPowerSeries.constantCoeff_X 1
      have hC : MvPowerSeries.constantCoeff C = 0 := D.constantCoeff_fgZ3Fixed
      have ha : a ≠ 0 := ha0
      have hb : b ≠ 0 := hb0
      have hwa : wa ≠ 0 := fun hh => ha ((hzchart A hA).mp hh)
      have hwb : wb ≠ 0 := fun hh => hb ((hzchart B hB).mp hh)
      have hna := (hnchart A hA) ha
      have hnb := (hnchart B hB) hb
      have hroot : ∀ (g : MvPowerSeries (Fin 2) R), MvPowerSeries.constantCoeff g = 0 →
          D.fgGenW g = g^3 + MvPowerSeries.C D.a₁*g*D.fgGenW g +
          MvPowerSeries.C D.a₂*g^2*D.fgGenW g + MvPowerSeries.C D.a₃*(D.fgGenW g)^2 +
          MvPowerSeries.C D.a₄*g*(D.fgGenW g)^2 + MvPowerSeries.C D.a₆*(D.fgGenW g)^3 := by
        intro g hg
        have hh := congrArg (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero hg)) D.formalW_eq
        simpa only [_root_.map_add,_root_.map_mul,_root_.map_pow,PowerSeries.substAlgHom_X,
          PowerSeries.coe_substAlgHom,PowerSeries.subst_C,fgGenW] using hh
      have hRaP : D.fgGenW A = S*A+N := by
        simpa only [A,B,MvPowerSeries.subst_X_pair_eq_self] using D.kwB_Ra hA hB
      have hRbP : D.fgGenW B = S*B+N := by
        simpa only [A,B,MvPowerSeries.subst_X_pair_eq_self] using D.kwB_Rb hA hB
      have hAB : A ≠ B := by
        intro hh
        have hh' := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) hh
        have heq : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) = Finsupp.single 1 1 := by
          simpa [A,B,MvPowerSeries.coeff_X] using hh'
        have := congrArg (fun z : Fin 2 →₀ ℕ => z 0) heq
        norm_num at this
      have hRcP : D.fgGenW C = S*C+N := by
        simpa only [A,B,MvPowerSeries.subst_X_pair_eq_self] using D.kwB_Rc hA hB hAB
      have hRa : wa=s*a+n := by simpa only [wa,s,a,n,_root_.map_add,_root_.map_mul] using congrArg e hRaP
      have hRb : wb=s*b+n := by simpa only [wb,s,b,n,_root_.map_add,_root_.map_mul] using congrArg e hRbP
      have hRc : wc=s*c+n := by simpa only [wc,s,c,n,_root_.map_add,_root_.map_mul] using congrArg e hRcP
      have hroota : wa=a^3+E.a₁*a*wa+E.a₂*a^2*wa+E.a₃*wa^2+E.a₄*a*wa^2+E.a₆*wa^3 := by
        simpa only [wa,a,E,WeierstrassCurve.map_a₁,WeierstrassCurve.map_a₂,
          WeierstrassCurve.map_a₃,WeierstrassCurve.map_a₄,WeierstrassCurve.map_a₆,
          _root_.map_add,_root_.map_mul,_root_.map_pow,heC] using congrArg e (hroot A hA)
      have hqp := universal_chart_quadratic (D.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R)) A B S N hAB
        (by rw [←hRaP]; simpa only [WeierstrassCurve.map_a₁,WeierstrassCurve.map_a₂,
          WeierstrassCurve.map_a₃,WeierstrassCurve.map_a₄,WeierstrassCurve.map_a₆] using hroot A hA)
        (by rw [←hRbP]; simpa only [WeierstrassCurve.map_a₁,WeierstrassCurve.map_a₂,
          WeierstrassCurve.map_a₃,WeierstrassCurve.map_a₄,WeierstrassCurve.map_a₆] using hroot B hB)
      have hq : (1+E.a₂*s+E.a₄*s^2+E.a₆*s^3)*(a^2+a*b+b^2) +
          (E.a₁*s+E.a₂*n+E.a₃*s^2+2*E.a₄*s*n+3*E.a₆*s^2*n)*(a+b) +
          (E.a₁*n+2*E.a₃*s*n+E.a₄*n^2+3*E.a₆*n^2*s-s)=0 := by
        simpa only [a,b,s,n,E,WeierstrassCurve.map_a₁,WeierstrassCurve.map_a₂,
          WeierstrassCurve.map_a₃,WeierstrassCurve.map_a₄,WeierstrassCurve.map_a₆,
          _root_.map_add,_root_.map_sub,_root_.map_mul,_root_.map_pow,_root_.map_one,_root_.map_ofNat,_root_.map_zero,heC] using congrArg e hqp
      have hDexp : d=1+E.a₂*s+E.a₄*s^2+E.a₆*s^3 := by
        simp only [d,Q,fgZ3Denom,_root_.map_add,_root_.map_one,_root_.map_mul,_root_.map_pow,heC,E,
          WeierstrassCurve.map_a₂,WeierstrassCurve.map_a₄,WeierstrassCurve.map_a₆,s,S]
      have hDunit : IsUnit Q := by
        apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
        have : MvPowerSeries.constantCoeff Q = 1 := by
          simp [Q,fgZ3Denom,D.constantCoeff_fgSlope]
        rw [this]; exact isUnit_one
      have hd : d ≠ 0 := (hDunit.map e).ne_zero
      have hvi : Q * MvPowerSeries.invOfUnit Q 1 = 1 :=
        MvPowerSeries.mul_invOfUnit Q 1 (by simp [Q,fgZ3Denom,D.constantCoeff_fgSlope])
      have hVp : Q*(C+A+B) + (MvPowerSeries.C D.a₁*S+MvPowerSeries.C D.a₂*N+
          MvPowerSeries.C D.a₃*S^2+2*MvPowerSeries.C D.a₄*S*N+3*MvPowerSeries.C D.a₆*S^2*N)=0 := by
        have hn : D.fgZ3NumFixed = -(MvPowerSeries.C D.a₁*S+MvPowerSeries.C D.a₂*N+
            MvPowerSeries.C D.a₃*S^2+2*MvPowerSeries.C D.a₄*S*N+3*MvPowerSeries.C D.a₆*S^2*N) := by
          simp only [fgZ3NumFixed,S,N,_root_.map_mul,_root_.map_ofNat]
          ring
        dsimp only [C,fgZ3Fixed]
        linear_combination D.fgZ3NumFixed * hvi + hn
      have hv : (1+E.a₂*s+E.a₄*s^2+E.a₆*s^3)*(c+a+b)+
          (E.a₁*s+E.a₂*n+E.a₃*s^2+2*E.a₄*s*n+3*E.a₆*s^2*n)=0 := by
        rw [←hDexp]
        simpa only [a,b,c,s,n,d,E,WeierstrassCurve.map_a₁,WeierstrassCurve.map_a₂,
          WeierstrassCurve.map_a₃,WeierstrassCurve.map_a₄,WeierstrassCurve.map_a₆,
          _root_.map_add,_root_.map_mul,_root_.map_pow,_root_.map_ofNat,_root_.map_zero,heC] using congrArg e hVp
      have hp : d*a*b*c=n-E.a₃*n^2-E.a₆*n^3 := by
        rw [hDexp]
        apply chart_product_relation E a b c s n
          (by rw [←hRa]; exact hroota) hq hv
      have hvs : d*(a+b+c)+(E.a₁*s+E.a₂*n+E.a₃*s^2+2*E.a₄*s*n+3*E.a₆*s^2*n)=0 := by
        rw [hDexp]
        convert hv using 1 <;> ring
      have hpair : d*(a*b+a*c+b*c)=E.a₁*n+2*E.a₃*s*n+E.a₄*n^2+3*E.a₆*n^2*s-s := by
        have hq' := hq
        have hv' := hv
        rw [←hDexp] at hq' hv'
        linear_combination (a+b)*hv'-hq'
      have hprodw : d*(wa*wb*wc)=n^3 :=
        chart_product_of_vieta E a b c s n d wa wb wc hDexp hRa hRb hRc hvs hpair hp
      have hcn : c=0 ↔ n=0 := by
        constructor
        · intro hc0
          have hwc0 : wc=0 := (hzchart C hC).mpr hc0
          have hh : n^3=0 := by simpa only [hwc0,mul_zero] using hprodw.symm
          exact (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hh
        · intro hn0
          have hh : d*wa*wb*wc=0 := by
            simpa only [hn0,zero_pow (by decide : 3 ≠ 0),mul_assoc] using hprodw
          apply (hzchart C hC).mp
          exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero (mul_ne_zero hd hwa) hwb)
      let T := PowerSeries.subst C D.fgInvDenom
      have hFi : D.formalGroupLawFixed*T = -C := by
        have hh := congrArg (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero hC)) D.fgInv_mul_fgInvDenom
        simpa only [formalGroupLawFixed,C,T,_root_.map_mul,_root_.map_neg,PowerSeries.substAlgHom_X,PowerSeries.coe_substAlgHom] using hh
      have hF0 : e D.formalGroupLawFixed=0 ↔ c=0 := by
        have hh := congrArg e hFi
        simp only [_root_.map_mul,_root_.map_neg] at hh
        constructor
        · intro hz
          rw [hz,zero_mul] at hh
          exact neg_eq_zero.mp hh.symm
        · intro hz
          have hfac : D.formalGroupLawFixed = -C * PowerSeries.subst C
              (PowerSeries.invOfUnit D.fgInvDenom (1 : Rˣ)) := by
            have hf := congrArg (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero hC))
              (show D.fgInv = -PowerSeries.X * PowerSeries.invOfUnit D.fgInvDenom (1 : Rˣ) from rfl)
            simpa only [formalGroupLawFixed,C,_root_.map_mul,_root_.map_neg,PowerSeries.substAlgHom_X,PowerSeries.coe_substAlgHom] using hf
          rw [hfac,_root_.map_mul,_root_.map_neg]
          change -c * _ = 0
          rw [hz,neg_zero,zero_mul]
      have hsum0 : c=0 → Affine.Point.some _ _ hna + Affine.Point.some _ _ hnb=0 := by
        intro hc0
        change Affine.Point.some (a/wa) (-1/wa) hna + Affine.Point.some (b/wb) (-1/wb) hnb=0
        have hn0 := hcn.mp hc0
        have hRa0 : wa=s*a := by simpa only [hn0,add_zero] using hRa
        have hRb0 : wb=s*b := by simpa only [hn0,add_zero] using hRb
        have hv0 : d*(a+b)+(E.a₁*s+E.a₃*s^2)=0 := by
          simpa only [hc0,hn0,zero_pow (by decide : 2≠0),zero_mul,mul_zero,add_zero] using hvs
        have hp0 : d*a*b = -s := by
          simpa only [hc0,hn0,zero_pow (by decide : 2≠0),zero_mul,mul_zero,add_zero,zero_add,zero_sub,mul_assoc] using hpair
        exact evaluated_chart_zero_sum E a b wa wb s d hwa hwb hRa0 hRb0 hv0 hp0 hna hnb
      have hsumnonzero : ∀ hc0 : c≠0,
          Affine.Point.some _ _ hna + Affine.Point.some _ _ hnb =
          -Affine.Point.some (c/wc) (-1/wc) ((hnchart C hC) hc0) := by
        intro hc0
        change Affine.Point.some (a/wa) (-1/wa) hna + Affine.Point.some (b/wb) (-1/wb) hnb = -Affine.Point.some (c/wc) (-1/wc) _
        have hn0 : n≠0 := fun hh => hc0 (hcn.mpr hh)
        have hwc : wc≠0 := fun hh => hc0 ((hzchart C hC).mp hh)
        have hnc := (hnchart C hC) hc0
        have hax := chart_addX_of_vieta E a b c s n d wa wb wc hd hn0 hwa hwb hwc
          hDexp hRa hRb hRc hvs hpair hp
        by_cases hxy : a/wa≠b/wb
        · exact evaluated_chart_chord E a b c wa wb wc s n hwa hwb hwc hn0
            hRa hRb hRc hax hxy hna hnb hnc
        · have hxy' : a/wa=b/wb := not_not.mp hxy
          have hab : a=b := by
            by_contra hab
            have hh := (div_eq_div_iff hwa hwb).mp hxy'
            rw [hRa,hRb] at hh
            exact hn0 ((mul_eq_zero.mp (show (a-b)*n=0 by linear_combination hh)).resolve_left (sub_ne_zero.mpr hab))
          have hwab : wb=wa := by rw [hRa,hRb,hab]
          have hqd : 3*(1+E.a₂*s+E.a₄*s^2+E.a₆*s^3)*a^2 +
              2*(E.a₁*s+E.a₂*n+E.a₃*s^2+2*E.a₄*s*n+3*E.a₆*s^2*n)*a +
              (E.a₁*n+2*E.a₃*s*n+E.a₄*n^2+3*E.a₆*n^2*s-s)=0 := by
            rw [←hab] at hq
            convert hq using 1 <;> ring
          have haxd : E.toAffine.addX (a/wa) (a/wa) (s/n)=c/wc := by
            simpa only [←hab,hwab] using hax
          have hh := evaluated_chart_doubling E a c wa wc s n hwa hwc hn0 hRa hRc hroota hqd haxd hna hnc
          simpa only [←hab,hwab] using hh
      split_ifs with hz
      · exact (hsum0 (hF0.mp hz)).symm
      · have hc0 : c≠0 := fun hh => hz (hF0.mpr hh)
        have hwc : wc≠0 := fun hh => hc0 ((hzchart C hC).mp hh)
        have hwF : e (D.fgGenW D.formalGroupLawFixed)≠0 := fun hh =>
          hz ((hzchart D.formalGroupLawFixed D.constantCoeff_formalGroupLawFixed).mp hh)
        exact (evaluated_inverse D f e heC C hC hwc hwF
          ((hnchart C hC) hc0)
          ((hnchart D.formalGroupLawFixed D.constantCoeff_formalGroupLawFixed) hz)).trans
          (hsumnonzero hc0).symm

  have evaluation_substitution
      {R S : Type} [CommRing R] [UniformSpace R] [DiscreteUniformity R]
      [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [CompleteSpace S]
      [T2Space S] [IsTopologicalRing S] [IsLinearTopology S S]
      (φ : R →+* S) (hφ : Continuous φ) (t : S) (ht : IsTopologicallyNilpotent t)
      (a b : PowerSeries R) (ha : PowerSeries.constantCoeff a = 0)
      (hb : PowerSeries.constantCoeff b = 0) (f : MvPowerSeries (Fin 2) R) :
      PowerSeries.eval₂Hom hφ ht (MvPowerSeries.subst ![a,b] f) =
        MvPowerSeries.eval₂ φ
          ![PowerSeries.eval₂Hom hφ ht a, PowerSeries.eval₂Hom hφ ht b] f := by
    clear evaluated_origin_chart evaluated_formal_law
    set_option backward.isDefEq.respectTransparency.types true in
      classical
      letI : Algebra R S := φ.toAlgebra
      have hab : MvPowerSeries.HasSubst (![a,b] : Fin 2 → PowerSeries R) := by
        apply MvPowerSeries.hasSubst_of_constantCoeff_zero
        intro s
        fin_cases s
        · exact ha
        · exact hb
      have he : ∀ g, PowerSeries.eval₂Hom hφ ht g = PowerSeries.eval₂ φ t g := by
        intro g
        exact congrFun (PowerSeries.coe_eval₂Hom hφ ht) g
      simp only [he]
      change MvPowerSeries.eval₂ φ (fun _ : Unit => t) (MvPowerSeries.subst ![a,b] f) = _
      have h := MvPowerSeries.eval₂_subst (R := R) (S := R) (T := S)
        hab (PowerSeries.hasEval ht) f
      have hpair : (fun s : Fin 2 => MvPowerSeries.eval₂ φ (fun _ : Unit => t) (![a,b] s)) =
          ![PowerSeries.eval₂ φ t a, PowerSeries.eval₂ φ t b] := by
        funext s
        fin_cases s <;> rfl
      simpa only [show algebraMap R S = φ from rfl, hpair] using h

  have evaluation_nth_step_of_zero
      {R S : Type} [CommRing R] [UniformSpace R] [DiscreteUniformity R]
      [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [CompleteSpace S]
      [T2Space S] [IsTopologicalRing S] [IsLinearTopology S S]
      (φ : R →+* S) (hφ : Continuous φ) (t : S) (ht : IsTopologicallyNilpotent t)
      (F : FormalGroup R) (a : PowerSeries R) (ha : PowerSeries.constantCoeff a = 0)
      (haz : PowerSeries.eval₂Hom hφ ht a = 0) :
      PowerSeries.eval₂Hom hφ ht
        (MvPowerSeries.subst ![a,PowerSeries.X] F.toPowerSeries) = t := by
    clear evaluated_origin_chart evaluated_formal_law
    set_option backward.isDefEq.respectTransparency.types true in
      have heX : PowerSeries.eval₂Hom hφ ht PowerSeries.X = t := by
        calc
          _ = PowerSeries.eval₂ φ t PowerSeries.X :=
            congrFun (PowerSeries.coe_eval₂Hom hφ ht) PowerSeries.X
          _ = t := PowerSeries.eval₂_X φ t
      rw [evaluation_substitution φ hφ t ht a PowerSeries.X ha (PowerSeries.constantCoeff_X),
        haz, heX]
      have hzero := evaluation_substitution φ hφ t ht 0 PowerSeries.X
        (by simp) PowerSeries.constantCoeff_X F.toPowerSeries
      have hzF : MvPowerSeries.subst ![(0 : PowerSeries R),PowerSeries.X] F.toPowerSeries =
          PowerSeries.X := F.zero_add
            (PowerSeries.HasSubst.of_constantCoeff_zero PowerSeries.constantCoeff_X)
      rw [hzF, _root_.map_zero, heX] at hzero
      exact hzero.symm

  have norm_evaluation_hom {R : Type} [CommRing R]
      [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
      [CompleteSpace R] [T2Space R] [IsLinearTopology R R]
      (t : R) (ht : IsTopologicallyNilpotent t) :
      ∃ e : PowerSeries R →+* R,
        (∀ g, FormalGroup.evalSeries g t = e g) ∧ e PowerSeries.X = t ∧
        (∀ r, e (PowerSeries.C r) = r) ∧
        (∀ (F : FormalGroup R) (a : PowerSeries R), PowerSeries.constantCoeff a = 0 →
          e a = 0 → e (MvPowerSeries.subst ![a,PowerSeries.X] F.toPowerSeries) = t) := by
    clear evaluated_origin_chart evaluated_formal_law evaluation_substitution
    set_option backward.isDefEq.respectTransparency.types true in
      have hdisc : @IsTopologicalSemiring R (⊥ : UniformSpace R).toTopologicalSpace _ := by
        letI : UniformSpace R := ⊥
        letI : TopologicalSpace R := (⊥ : UniformSpace R).toTopologicalSpace
        letI : DiscreteTopology R := discreteTopology_bot _
        infer_instance
      have hcont : @Continuous R R
          (⊥ : UniformSpace R).toTopologicalSpace inferInstance (algebraMap _ _) := by
        exact continuous_bot
      let e : PowerSeries R →+* R :=
        @PowerSeries.eval₂Hom R _ R _ (algebraMap _ _) t
          ⊥ inferInstance inferInstance hdisc inferInstance inferInstance inferInstance
          inferInstance inferInstance hcont ht
      have he : ∀ f, FormalGroup.evalSeries f t = e f := by
        intro f
        exact congrFun (@PowerSeries.coe_eval₂Hom R _ R _
          (algebraMap _ _) t ⊥ inferInstance inferInstance hdisc inferInstance
          inferInstance inferInstance inferInstance inferInstance hcont ht).symm f
      have heXO : e PowerSeries.X = t := by
        rw [← he]
        simp [FormalGroup.evalSeries]
      have heC : ∀ r : R, e (PowerSeries.C r) = r := by
        intro r
        rw [← he]
        simp [FormalGroup.evalSeries]
      refine ⟨e, he, heXO, heC, ?_⟩
      intro F a ha haz
      exact @evaluation_nth_step_of_zero R R
        _ ⊥ inferInstance _ inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance (algebraMap _ _) hcont t ht F a ha haz

  have eval_nthSeries_zero_of_nsmul
      {R K : Type} [CommRing R] [IsDomain R] [Field K] [DecidableEq K]
      (D : WeierstrassCurve R) (f : R →+* K) [(D.map f).IsElliptic]
      (F : FormalGroup R) (hF : F.toPowerSeries = D.formalGroupLawFixed)
      (e : PowerSeries R →+* K) (heC : ∀ r, e (PowerSeries.C r) = f r)
      (hX : e PowerSeries.X ≠ 0)
      (hzero : ∀ a : PowerSeries R, PowerSeries.constantCoeff a = 0 → e a = 0 →
        e (MvPowerSeries.subst ![a, PowerSeries.X] F.toPowerSeries) = e PowerSeries.X)
      (hchart : ∀ (a : PowerSeries R) (ha : PowerSeries.constantCoeff a = 0),
        e a ≠ 0 → (D.map f).toAffine.Nonsingular
          (e a / e (D.fgGenW a)) (-1 / e (D.fgGenW a)))
      (hP : (D.map f).toAffine.Nonsingular
        (e PowerSeries.X / e (D.fgGenW PowerSeries.X))
        (-1 / e (D.fgGenW PowerSeries.X)))
      (n : ℕ)
      (hn : n • WeierstrassCurve.Affine.Point.some _ _ hP = 0) :
      e (F.nthSeries n) = 0 := by
    clear evaluation_substitution evaluation_nth_step_of_zero norm_evaluation_hom
    set_option backward.isDefEq.respectTransparency.types true in
      classical
      let point (a : PowerSeries R) (ha : PowerSeries.constantCoeff a = 0) :
          (D.map f).toAffine.Point :=
        if hz : e a = 0 then 0 else WeierstrassCurve.Affine.Point.some
          (e a / e (D.fgGenW a)) (-1 / e (D.fgGenW a))
          (hchart a ha hz)
      have pzero (a : PowerSeries R) (ha : PowerSeries.constantCoeff a = 0) :
          point a ha = 0 ↔ e a = 0 := by
        dsimp only [point]
        split_ifs with hz
        · exact iff_of_true rfl hz
        · constructor
          · intro hh
            cases hh
          · intro hh
            exact (hz hh).elim
      have pcongr (a b : PowerSeries R) (ha : PowerSeries.constantCoeff a = 0)
          (hb : PowerSeries.constantCoeff b = 0) (hab : e a = e b) : point a ha = point b hb := by
        have hw : e (D.fgGenW a) = e (D.fgGenW b) := by
          have hwa := congrArg e (D.kwB_Ra ha hb)
          have hwb := congrArg e (D.kwB_Rb ha hb)
          simp only [_root_.map_add, _root_.map_mul] at hwa hwb
          rw [hwa, hwb, hab]
        dsimp only [point]
        by_cases hza : e a = 0
        · have hzb : e b = 0 := hab.symm.trans hza
          rw [dif_pos hza, dif_pos hzb]
        · have hzb : e b ≠ 0 := fun hh => hza (hab.trans hh)
          rw [dif_neg hza, dif_neg hzb, WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨by rw [hab, hw], by rw [hw]⟩
      have padd (a b : PowerSeries R) (ha : PowerSeries.constantCoeff a = 0)
          (hb : PowerSeries.constantCoeff b = 0) (ha0 : e a ≠ 0) (hb0 : e b ≠ 0) :
          point (MvPowerSeries.subst ![a,b] F.toPowerSeries)
            (by rw [hF]; exact WeierstrassCurve.kwB_constantCoeff_subst_pair ha hb D.constantCoeff_formalGroupLawFixed) =
          point a ha + point b hb := by
        let hs : MvPowerSeries.HasSubst (![a,b] : Fin 2 → PowerSeries R) :=
          WeierstrassCurve.kwB_hasSubst_pair ha hb
        let e' : MvPowerSeries (Fin 2) R →+* K :=
          e.comp (MvPowerSeries.substAlgHom hs).toRingHom
        have he' (g : MvPowerSeries (Fin 2) R) : e' g = e (MvPowerSeries.subst ![a,b] g) := by
          change e ((MvPowerSeries.substAlgHom hs) g) = _
          rw [MvPowerSeries.coe_substAlgHom]
        have he'C : ∀ r, e' (MvPowerSeries.C r) = f r := by
          intro r
          rw [he', MvPowerSeries.subst_C]
          exact heC r
        have hXa : e' (MvPowerSeries.X 0) = e a := by rw [he', MvPowerSeries.subst_X hs]; rfl
        have hXb : e' (MvPowerSeries.X 1) = e b := by rw [he', MvPowerSeries.subst_X hs]; rfl
        have hW (g : MvPowerSeries (Fin 2) R) (hg : MvPowerSeries.constantCoeff g = 0) :
            e' (D.fgGenW g) = e (D.fgGenW (MvPowerSeries.subst ![a,b] g)) := by
          rw [he']
          unfold WeierstrassCurve.fgGenW
          rw [WeierstrassCurve.subst_pair_bridge hs (PowerSeries.HasSubst.of_constantCoeff_zero hg)]
        have hWF := hW D.formalGroupLawFixed D.constantCoeff_formalGroupLawFixed
        have hWA := hW (MvPowerSeries.X 0) (MvPowerSeries.constantCoeff_X 0)
        have hWB := hW (MvPowerSeries.X 1) (MvPowerSeries.constantCoeff_X 1)
        have hzchart' (g : MvPowerSeries (Fin 2) R) (hg : MvPowerSeries.constantCoeff g = 0) :
            e' (D.fgGenW g)=0 ↔ e' g=0 :=
          (evaluated_origin_chart D f e' he'C g hg).1
        have hnchart' (g : MvPowerSeries (Fin 2) R) (hg : MvPowerSeries.constantCoeff g = 0)
            (hne : e' g ≠ 0) : (D.map f).toAffine.Nonsingular
            (e' g / e' (D.fgGenW g)) (-1/e' (D.fgGenW g)) := by
          rw [he',hW g hg]
          apply hchart
          · exact WeierstrassCurve.kwB_constantCoeff_subst_pair ha hb hg
          · rwa [he'] at hne
        have hh := @evaluated_formal_law R K _ _ _ _ D f _ e' he'C hzchart' hnchart'
          (by rwa [hXa]) (by rwa [hXb])
        simpa only [point, hF, hWF, hWA, hWB, he', MvPowerSeries.subst_X hs,
          Matrix.cons_val_zero, Matrix.cons_val_one, dif_neg ha0, dif_neg hb0] using hh
      have hind : ∀ k : ℕ, point (F.nthSeries k) (F.constantCoeff_nthSeries k) =
          k • point PowerSeries.X PowerSeries.constantCoeff_X := by
        intro k
        induction k with
        | zero =>
          apply (pzero _ (F.constantCoeff_nthSeries 0)).mpr
          exact _root_.map_zero e
        | succ k ih =>
          rw [succ_nsmul, ← ih]
          by_cases hk : e (F.nthSeries k) = 0
          · rw [(pzero _ (F.constantCoeff_nthSeries k)).mpr hk, zero_add]
            exact pcongr _ _ (F.constantCoeff_nthSeries (k + 1)) PowerSeries.constantCoeff_X
              (hzero _ (F.constantCoeff_nthSeries k) hk)
          · exact padd _ _ (F.constantCoeff_nthSeries k) PowerSeries.constantCoeff_X hk hX
      apply (pzero _ (F.constantCoeff_nthSeries n)).mp
      rw [hind]
      have hpx : point PowerSeries.X PowerSeries.constantCoeff_X =
          WeierstrassCurve.Affine.Point.some _ _
            hP := dif_neg hX
      rw [hpx]
      exact hn

  have integer_norm_linear_topology (p : ℕ) [Fact p.Prime] :
      IsLinearTopology (PadicComplexInt p) (PadicComplexInt p) := by
    clear evaluated_origin_chart evaluated_formal_law evaluation_substitution evaluation_nth_step_of_zero norm_evaluation_hom eval_nthSeries_zero_of_nsmul
    set_option backward.isDefEq.respectTransparency.types true in
      let B : {r : ℝ // 0 < r} → Ideal (PadicComplexInt p) := fun r =>
        { carrier := {x | ‖(x : ℂ_[p])‖ < r.val}
          zero_mem' := by simpa using r.property
          add_mem' := by
            intro x y hx hy
            exact lt_of_le_of_lt (PadicComplex.isNonarchimedean p _ _) (max_lt (show ‖(x : ℂ_[p])‖ < r.val from hx) (show ‖(y : ℂ_[p])‖ < r.val from hy))
          smul_mem' := by
            intro a x hx
            change ‖(a : ℂ_[p]) * (x : ℂ_[p])‖ < r.val
            rw [norm_mul]
            exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (by
              rw [PadicComplex.norm_eq_norm]
              exact (Valued.toNormedField.norm_le_one_iff).mpr a.property)) hx }
      apply IsLinearTopology.mk_of_hasBasis (PadicComplexInt p)
        (s := B) (p := fun _ => True)
      have h := (Metric.nhds_basis_ball (x := (0 : PadicComplexInt p)))
      refine h.to_hasBasis ?_ ?_
      · intro r hr
        refine ⟨⟨r, hr⟩, True.intro, ?_⟩
        intro x hx
        simpa [B, Metric.mem_ball, dist_zero_right] using hx
      · intro r _
        refine ⟨r.val, r.property, ?_⟩
        intro x hx
        simpa [B, Metric.mem_ball, dist_zero_right] using hx

  have origin_chart_evaluation {R : Type} [CommRing R] [IsLocalRing R]
      [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
      [CompleteSpace R] [T2Space R] [IsLinearTopology R R]
      (D : WeierstrassCurve R) (t w : R) (ht : IsTopologicallyNilpotent t)
      (htm : t ∈ IsLocalRing.maximalIdeal R) (hwm : w ∈ IsLocalRing.maximalIdeal R)
      (hw : w = t ^ 3 + D.a₁ * t * w + D.a₂ * t ^ 2 * w + D.a₃ * w ^ 2 +
        D.a₄ * t * w ^ 2 + D.a₆ * w ^ 3) : FormalGroup.evalSeries D.formalW t = w := by
    clear evaluated_origin_chart evaluated_formal_law evaluation_substitution evaluation_nth_step_of_zero eval_nthSeries_zero_of_nsmul integer_norm_linear_topology
    set_option backward.isDefEq.respectTransparency.types true in
      obtain ⟨e, he, heX, heC, _⟩ := norm_evaluation_hom t ht
      let v := e D.formalW
      have hv : v = t ^ 3 + D.a₁ * t * v + D.a₂ * t ^ 2 * v + D.a₃ * v ^ 2 +
          D.a₄ * t * v ^ 2 + D.a₆ * v ^ 3 := by
        have hh := congrArg e D.formalW_eq
        simpa only [_root_.map_add, _root_.map_mul, _root_.map_pow, heX, heC] using hh
      let I := IsLocalRing.maximalIdeal (R)
      have hvm : v ∈ I := by
        obtain ⟨f, hf⟩ := D.X_pow_three_dvd_formalW
        change e D.formalW ∈ I
        rw [hf, _root_.map_mul, _root_.map_pow, heX]
        exact I.mul_mem_right _ (by rw [pow_succ]; exact I.mul_mem_left (t ^ 2) htm)
      let M := D.a₁ * t + D.a₂ * t ^ 2 + D.a₃ * (w + v) +
        D.a₄ * t * (w + v) + D.a₆ * (w ^ 2 + w * v + v ^ 2)
      have hM : M ∈ I := by
        dsimp [M]
        apply I.add_mem
        · apply I.add_mem
          · apply I.add_mem
            · exact I.add_mem (I.mul_mem_left _ htm)
                (I.mul_mem_left _ (by simpa only [pow_two] using I.mul_mem_left t htm))
            · exact I.mul_mem_left _ (I.add_mem hwm hvm)
          · exact I.mul_mem_left _ (I.add_mem hwm hvm)
        · apply I.mul_mem_left
          exact I.add_mem (I.add_mem (by simpa only [pow_two] using I.mul_mem_left w hwm)
            (I.mul_mem_right _ hwm)) (by simpa only [pow_two] using I.mul_mem_left v hvm)
      have hprod : (1 - M) * (w - v) = 0 := by
        dsimp [M]
        linear_combination hw - hv
      have hu : IsUnit (1 - M) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits M hM
      rw [he]
      exact (sub_eq_zero.mp ((IsUnit.mul_right_eq_zero hu).mp hprod)).symm

  have origin_chart_parameter (p : ℕ) [Fact p.Prime] (D : WeierstrassCurve (PadicComplexInt p))
      (x y : ℂ_[p]) (h : (D.map (PadicComplexInt p).subtype).toAffine.Nonsingular x y)
      (hx : 1 < ‖x‖) :
      ∃ t : PadicComplexInt p, (t : ℂ_[p]) = -x / y ∧ t ≠ 0 ∧ ‖(t : ℂ_[p])‖ < 1 ∧
        ((FormalGroup.evalSeries D.formalW t : PadicComplexInt p) : ℂ_[p]) = -1 / y := by
    clear evaluated_origin_chart evaluated_formal_law evaluation_substitution evaluation_nth_step_of_zero norm_evaluation_hom eval_nthSeries_zero_of_nsmul
    set_option backward.isDefEq.respectTransparency.types true in
      classical
      haveI : CompleteSpace 𝓞_ℂ_[p] := (Valued.isClosed_valuationSubring ℂ_[p]).completeSpace_coe
      haveI : IsLinearTopology 𝓞_ℂ_[p] 𝓞_ℂ_[p] := integer_norm_linear_topology p
      have chart := origin_chart_evaluation D
      have hmem : ∀ z : ℂ_[p], z ∈ PadicComplexInt p ↔ ‖z‖ ≤ 1 := by
        intro z
        rw [PadicComplex.norm_eq_norm]
        exact (Valued.toNormedField.norm_le_one_iff (L := ℂ_[p]) (Γ₀ := NNReal) (x := z)).symm
      have hxn : x ∉ PadicComplexInt p := fun hh => (not_le.mpr hx) ((hmem x).mp hh)
      have hx0 : x ≠ 0 := fun hh => hxn (hh ▸ (PadicComplexInt p).zero_mem)
      have hy0 : y ≠ 0 := Affine.Y_ne_zero_of_X_notMem D h.1 hxn
      have ht0 : -x / y ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx0) hy0
      have htn : -x / y ∈ (PadicComplexInt p).nonunits := by
        simpa only [neg_div] using
          (PadicComplexInt p).nonunits.neg_mem (Affine.X_div_Y_mem_nonunits D h.1 hxn)
      have hti : -x / y ∈ PadicComplexInt p := (PadicComplexInt p).nonunits_subset htn
      let t : PadicComplexInt p := ⟨-x / y, hti⟩
      have ht1 : ‖(t : ℂ_[p])‖ < 1 := by
        have hinv : (-x / y)⁻¹ ∉ PadicComplexInt p :=
          ((PadicComplexInt p).mem_nonunits_iff_or.mp htn).resolve_left ht0
        by_contra hge
        apply hinv
        rw [hmem, norm_inv]
        exact inv_le_one_of_one_le₀ (le_of_not_gt hge)
      have hwn : -1 / y ∈ (PadicComplexInt p).nonunits := by
        simpa only [neg_div, one_div] using (PadicComplexInt p).nonunits.neg_mem
          ((PadicComplexInt p).inv_mem_nonunits_of_notMem (Affine.Y_notMem_of_X_notMem D h.1 hxn))
      let w : PadicComplexInt p := ⟨-1 / y, (PadicComplexInt p).nonunits_subset hwn⟩
      have htm : t ∈ IsLocalRing.maximalIdeal (PadicComplexInt p) :=
        (PadicComplexInt p).coe_mem_nonunits_iff.mp htn
      have hwm : w ∈ IsLocalRing.maximalIdeal (PadicComplexInt p) :=
        (PadicComplexInt p).coe_mem_nonunits_iff.mp hwn
      have hw : w = t ^ 3 + D.a₁ * t * w + D.a₂ * t ^ 2 * w + D.a₃ * w ^ 2 +
          D.a₄ * t * w ^ 2 + D.a₆ * w ^ 3 := by
        apply Subtype.ext
        change -1 / y = (-x / y)^3 + (D.a₁ : ℂ_[p]) * (-x / y) * (-1 / y) +
          (D.a₂ : ℂ_[p]) * (-x / y)^2 * (-1 / y) + (D.a₃ : ℂ_[p]) * (-1 / y)^2 +
          (D.a₄ : ℂ_[p]) * (-x / y) * (-1 / y)^2 + (D.a₆ : ℂ_[p]) * (-1 / y)^3
        have heq := (WeierstrassCurve.Affine.equation_iff _ _).mp h.1
        simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
          WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at heq
        change y ^ 2 + (D.a₁ : ℂ_[p]) * x * y + (D.a₃ : ℂ_[p]) * y =
          x ^ 3 + (D.a₂ : ℂ_[p]) * x ^ 2 + (D.a₄ : ℂ_[p]) * x + (D.a₆ : ℂ_[p]) at heq
        field_simp
        linear_combination -heq
      refine ⟨t, rfl, ?_, ht1, ?_⟩
      · intro hh
        exact ht0 (congrArg Subtype.val hh)
      · exact congrArg Subtype.val (chart t w
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ht1) htm hwm hw)

  intro n p _ _ D hΔ F _ hF x y h hx hn
  clear evaluated_formal_law evaluation_substitution evaluation_nth_step_of_zero origin_chart_evaluation
  classical
  obtain ⟨t, ht, ht0, ht1, hwt⟩ := origin_chart_parameter p D x y h hx
  haveI : CompleteSpace 𝓞_ℂ_[p] := (Valued.isClosed_valuationSubring ℂ_[p]).completeSpace_coe
  haveI : IsLinearTopology 𝓞_ℂ_[p] 𝓞_ℂ_[p] := integer_norm_linear_topology p
  have hΔK : (D.map (PadicComplexInt p).subtype).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]
    intro hz
    exact hΔ (Subtype.ext hz)
  haveI : (D.map (PadicComplexInt p).subtype).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔK⟩
  have htt : IsTopologicallyNilpotent t :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one ht1
  obtain ⟨e, he, heXO, heCO, hstepO⟩ := norm_evaluation_hom t htt
  let eK : PowerSeries 𝓞_ℂ_[p] →+* ℂ_[p] := (PadicComplexInt p).subtype.comp e
  have heKC : ∀ r : 𝓞_ℂ_[p], eK (PowerSeries.C r) = (r : ℂ_[p]) := by
    intro r
    change ((e (PowerSeries.C r) : 𝓞_ℂ_[p]) : ℂ_[p]) = _
    rw [heCO]
  have heKX : eK PowerSeries.X = (t : ℂ_[p]) := by
    change ((e PowerSeries.X : 𝓞_ℂ_[p]) : ℂ_[p]) = _
    rw [heXO]
  have heKXne : eK PowerSeries.X ≠ 0 := by
    rw [heKX]
    exact fun hz => ht0 (Subtype.ext hz)
  have heKW : eK (D.fgGenW PowerSeries.X) = -1 / y := by
    change ((e (PowerSeries.subst PowerSeries.X D.formalW) : 𝓞_ℂ_[p]) : ℂ_[p]) = _
    rw [PowerSeries.X_subst, ← he]
    exact hwt
  have hy : y ≠ 0 := by
    intro hz
    apply ht0
    apply Subtype.ext
    simpa only [ht, hz, div_zero, ZeroMemClass.coe_zero]
  have hzero : ∀ a : PowerSeries 𝓞_ℂ_[p], PowerSeries.constantCoeff a = 0 → eK a = 0 →
      eK (MvPowerSeries.subst ![a, PowerSeries.X] F.toPowerSeries) = eK PowerSeries.X := by
    intro a ha haz
    have hazO : e a = 0 := Subtype.ext haz
    have hstep := hstepO F a ha hazO
    change ((e (MvPowerSeries.subst ![a, PowerSeries.X] F.toPowerSeries) : 𝓞_ℂ_[p]) : ℂ_[p]) = _
    rw [hstep, heKX]
  have hpoint : WeierstrassCurve.Affine.Point.some
      (eK PowerSeries.X / eK (D.fgGenW PowerSeries.X))
      (-1 / eK (D.fgGenW PowerSeries.X))
      ((evaluated_origin_chart D (PadicComplexInt p).subtype eK heKC
        PowerSeries.X PowerSeries.constantCoeff_X).2 heKXne) =
      WeierstrassCurve.Affine.Point.some x y h := by
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · rw [heKX, heKW, ht]
      field_simp [hy]
    · rw [heKW]
      field_simp [hy]
  have hzK := eval_nthSeries_zero_of_nsmul D (PadicComplexInt p).subtype F hF eK heKC
    heKXne hzero
    (fun a ha hz => (evaluated_origin_chart D (PadicComplexInt p).subtype eK heKC a ha).2 hz)
    ((evaluated_origin_chart D (PadicComplexInt p).subtype eK heKC PowerSeries.X
      PowerSeries.constantCoeff_X).2 heKXne)
    n (by rw [hpoint]; exact hn)
  refine ⟨t, ht, ht0, ht1, ?_⟩
  rw [he]
  exact Subtype.ext hzK
end PrimeLocal
