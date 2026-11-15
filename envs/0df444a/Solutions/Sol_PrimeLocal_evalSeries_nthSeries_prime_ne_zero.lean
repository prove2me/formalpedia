-- Prove2me | solution 1 for PrimeLocal.evalSeries_nthSeries_prime_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T02:22:51.090796+00:00
-- url     : https://prove2.me/submissions/37b98120-7d60-4c10-aa38-90e4a6f54639

import Mathlib
import Theorems.Thm_FormalGroup_exists_nthSeries_eq_qfold_of_isUnit
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine
import Definitions.Def_FormalGroup_NSeries

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal
universe u v

namespace PrimeLocal
theorem _root_.solution (p : ℕ) [Fact p.Prime] (F : FormalGroup 𝓞_ℂ_[p]) [F.IsComm] (t : 𝓞_ℂ_[p]) (ht0 : t ≠ 0) (ht1 : ‖(t : ℂ_[p])‖ < 1) (hsmall : ‖(t : ℂ_[p])‖ ^ (p - 1) < ‖(p : ℂ_[p])‖) : FormalGroup.evalSeries (F.nthSeries p) t ≠ 0 := by
  classical
  letI : CompleteSpace 𝓞_ℂ_[p] := (Valued.isClosed_valuationSubring ℂ_[p]).completeSpace_coe
  letI : IsLinearTopology 𝓞_ℂ_[p] 𝓞_ℂ_[p] := by
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
  have hbound : ∀ a : 𝓞_ℂ_[p], ‖(a : ℂ_[p])‖ ≤ 1 := by
    intro a
    rw [PadicComplex.norm_eq_norm]
    exact (Valued.toNormedField.norm_le_one_iff).mpr a.property
  have hunit : ∀ k : ℕ, 1 ≤ k → ¬ p ∣ k → IsUnit (k : 𝓞_ℂ_[p]) := by
    intro k _ hk
    apply (PadicComplexInt.integers p).isUnit_iff_valuation_eq_one.mpr
    simp only [map_natCast]
    have hnorm : ‖(k : ℂ_[p])‖ = 1 := by
      have hc : p.Coprime k := (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hk
      have hn := PadicComplex.norm_extends' p (k : ℚ_[p])
      norm_cast at hn
      exact hn.trans ((Padic.norm_natCast_eq_one_iff (p := p) (n := k)).mpr hc)
    rw [PadicComplex.norm_eq_norm, Valuation.norm_def,
      PadicComplex.RankOne.hom_eq_embedding] at hnorm
    simpa only [Valuation.embedding_restrict, NNReal.coe_eq_one] using hnorm
  have ht : IsTopologicallyNilpotent t :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one ht1
  have hdisc : @IsTopologicalSemiring 𝓞_ℂ_[p] (⊥ : UniformSpace 𝓞_ℂ_[p]).toTopologicalSpace _ := by
    letI : UniformSpace 𝓞_ℂ_[p] := ⊥
    letI : TopologicalSpace 𝓞_ℂ_[p] := (⊥ : UniformSpace 𝓞_ℂ_[p]).toTopologicalSpace
    letI : DiscreteTopology 𝓞_ℂ_[p] := discreteTopology_bot _
    infer_instance
  have hcont : @Continuous 𝓞_ℂ_[p] 𝓞_ℂ_[p]
      (⊥ : UniformSpace 𝓞_ℂ_[p]).toTopologicalSpace inferInstance (algebraMap _ _) := by
    exact continuous_bot
  let e : PowerSeries 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p] :=
    @PowerSeries.eval₂Hom 𝓞_ℂ_[p] _ 𝓞_ℂ_[p] _ (algebraMap _ _) t
      ⊥ inferInstance inferInstance hdisc inferInstance inferInstance inferInstance
      inferInstance inferInstance hcont ht
  have he : ∀ f, FormalGroup.evalSeries f t = e f := by
    intro f
    exact congrFun (@PowerSeries.coe_eval₂Hom 𝓞_ℂ_[p] _ 𝓞_ℂ_[p] _
      (algebraMap _ _) t ⊥ inferInstance inferInstance hdisc inferInstance
      inferInstance inferInstance inferInstance inferInstance hcont ht).symm f
  have heX : e PowerSeries.X = t := by
    rw [← he]
    simp [FormalGroup.evalSeries]
  obtain ⟨h, g, hfg⟩ := F.exists_nthSeries_eq_qfold_of_isUnit
    (Fact.out : p.Prime).two_le hunit
  have hev : e (F.nthSeries p) = (p : 𝓞_ℂ_[p]) * t +
      (p : 𝓞_ℂ_[p]) * (t ^ 2 * e h) + t ^ p * e g := by
    rw [hfg]
    have heC : ∀ a : 𝓞_ℂ_[p], e (PowerSeries.C a) = a := by
      intro a
      rw [← he]
      simp [FormalGroup.evalSeries]
    simp only [nsmul_eq_mul, Algebra.smul_def, map_add, map_mul, map_pow, map_natCast, heX,
      PowerSeries.algebraMap_eq, heC]
  have htpos : 0 < ‖(t : ℂ_[p])‖ := norm_pos_iff.mpr (by exact_mod_cast ht0)
  have hppos : 0 < ‖(p : ℂ_[p])‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr
    (Fact.out : p.Prime).ne_zero)
  have hlow : ‖(p : ℂ_[p]) * ((t : ℂ_[p]) ^ 2 * (e h : ℂ_[p]))‖ <
      ‖(p : ℂ_[p]) * (t : ℂ_[p])‖ := by
    simp only [norm_mul, norm_pow]
    rw [← mul_assoc]
    calc
      _ ≤ ‖(p : ℂ_[p])‖ * ‖(t : ℂ_[p])‖ ^ 2 :=
        mul_le_of_le_one_right (mul_nonneg hppos.le (sq_nonneg _)) (hbound (e h))
      _ < _ := mul_lt_mul_of_pos_left (by nlinarith) hppos
  have hhigh : ‖(t : ℂ_[p]) ^ p * (e g : ℂ_[p])‖ <
      ‖(p : ℂ_[p]) * (t : ℂ_[p])‖ := by
    rw [norm_mul, norm_pow, norm_mul]
    have hpow : ‖(t : ℂ_[p])‖ ^ p = ‖(t : ℂ_[p])‖ ^ (p - 1) * ‖(t : ℂ_[p])‖ := by
      rw [← pow_succ]
      congr 1
      have hpge := (Fact.out : p.Prime).two_le
      omega
    rw [hpow]
    calc
      _ ≤ ‖(t : ℂ_[p])‖ ^ (p - 1) * ‖(t : ℂ_[p])‖ :=
        mul_le_of_le_one_right (mul_nonneg (pow_nonneg htpos.le _) htpos.le) (hbound (e g))
      _ < _ := mul_lt_mul_of_pos_right hsmall htpos
  intro hz
  rw [he] at hz
  have hz' := congrArg (fun a : 𝓞_ℂ_[p] => (a : ℂ_[p])) (hev.symm.trans hz)
  change (p : ℂ_[p]) * (t : ℂ_[p]) +
    (p : ℂ_[p]) * ((t : ℂ_[p]) ^ 2 * (e h : ℂ_[p])) +
    (t : ℂ_[p]) ^ p * (e g : ℂ_[p]) = 0 at hz'
  have hzero : (p : ℂ_[p]) * (t : ℂ_[p]) =
      -((p : ℂ_[p]) * ((t : ℂ_[p]) ^ 2 * (e h : ℂ_[p])) +
        (t : ℂ_[p]) ^ p * (e g : ℂ_[p])) := by
    linear_combination hz'
  have hle := PadicComplex.isNonarchimedean p
    ((p : ℂ_[p]) * ((t : ℂ_[p]) ^ 2 * (e h : ℂ_[p])))
    ((t : ℂ_[p]) ^ p * (e g : ℂ_[p]))
  have heq : ‖(p : ℂ_[p]) * (t : ℂ_[p])‖ =
      ‖(p : ℂ_[p]) * ((t : ℂ_[p]) ^ 2 * (e h : ℂ_[p])) +
        (t : ℂ_[p]) ^ p * (e g : ℂ_[p])‖ := by
    conv_lhs => rw [hzero, norm_neg]
  have hlt := hle.trans_lt (max_lt hlow hhigh)
  rw [← heq] at hlt
  exact (lt_irrefl _) hlt

end PrimeLocal
