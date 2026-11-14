-- Prove2me | solution 1 for PGDRevision20261113.affine_loss_nonattainment
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T10:02:49.743272+00:00
-- url     : https://prove2.me/submissions/032e23e8-e289-42f2-b529-2fabacb7921e

import Definitions.Def_PGDRevision20261113_Examples
import Mathlib.Tactic

set_option autoImplicit false
open PGDRevision20261113
open scoped ENNReal

private lemma power_ge_one (c t : ℝ) (hc : 0 ≤ c)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) : 1 ≤ powerCurvature c t := by
  have hp : 0 < 1 + t := by linarith [ht.1]
  have hm : 0 < 1 - t := by linarith [ht.2]
  have ha : 0 < Real.rpow (1 + t) (-c) := Real.rpow_pos_of_pos hp (-c)
  have hb : 0 < Real.rpow (1 - t) (-c) := Real.rpow_pos_of_pos hm (-c)
  have hprod : 1 ≤ Real.rpow (1 + t) (-c) * Real.rpow (1 - t) (-c) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.mul_rpow hp.le hm.le]
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos (mul_pos hp hm)
    · nlinarith [sq_nonneg t]
    · linarith
  unfold powerCurvature
  by_contra hn
  have hs : Real.rpow (1 + t) (-c) + Real.rpow (1 - t) (-c) < 2 := by linarith
  have hmul := mul_pos
    (by linarith : 0 < 2 - (Real.rpow (1 + t) (-c) + Real.rpow (1 - t) (-c)))
    (by linarith : 0 < 2 + (Real.rpow (1 + t) (-c) + Real.rpow (1 - t) (-c)))
  nlinarith [sq_nonneg (Real.rpow (1 + t) (-c) - Real.rpow (1 - t) (-c))]

theorem solution : AffineLossNonattainmentClaim := by
  intro family b lam hlam hfamily
  let G : GeometryData := ⟨family, (fun _ => 0), b, lam⟩
  change
    (∀ c p : ℝ, 0 ≤ c → 0 < p → 0 < geometryRho G c p) ∧
    (∀ p : ℝ, 0 < p → geometryRho G 0 p = ENNReal.ofReal (p / (p + lam))) ∧
    (∀ eps : ℝ, 0 < eps → ∃ p > (0 : ℝ), geometryRho G 0 p < ENNReal.ofReal eps) ∧
    ¬ ∃ z, GeometryOptimum G z
  have hzero : (0 : ℝ) ∈ geometryDomain G := by
    cases family <;> norm_num [geometryDomain, G]
  have hb0 : b 0 = 1 := by
    cases family with
    | interval beta =>
      rw [hfamily.2]
      simp [powerCurvature, Real.rpow_eq_pow]
    | realLine => exact hfamily.2
  have hb1 (t : ℝ) (ht : t ∈ geometryDomain G) : 1 ≤ b t := by
    cases family with
    | interval beta =>
      rw [hfamily.2]
      exact power_ge_one beta t (by linarith [hfamily.1]) ht
    | realLine => exact hfamily.1 t
  have hk0 (t : ℝ) : geometryKernel G 0 t = 1 := by
    cases family <;> simp [geometryKernel, G, powerCurvature, Real.rpow_eq_pow]
  have hkzero (c : ℝ) : geometryKernel G c 0 = 1 := by
    cases family <;> simp [geometryKernel, G, powerCurvature, hb0, Real.rpow_eq_pow]
  have hezero (c p : ℝ) : geometryError G c p 0 = p / (p + lam) := by
    simp [geometryError, hkzero, G, hb0]
  have hlower (c p : ℝ) (hp : 0 < p) :
      ENNReal.ofReal (p / (p + lam)) ≤ geometryRho G c p := by
    have he : |geometryError G c p 0| = p / (p + lam) := by
      rw [hezero, abs_of_pos (div_pos hp (by linarith))]
    rw [← he]
    exact le_iSup_of_le 0 (le_iSup_of_le hzero le_rfl)
  have hpositive (c p : ℝ) (hp : 0 < p) : 0 < geometryRho G c p :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (div_pos hp (by linarith))) (hlower c p hp)
  have hrho (p : ℝ) (hp : 0 < p) :
      geometryRho G 0 p = ENNReal.ofReal (p / (p + lam)) := by
    apply le_antisymm
    · refine iSup_le fun t => iSup_le fun ht => ENNReal.ofReal_le_ofReal ?_
      have hbt : 1 ≤ b t := hb1 t ht
      have hden : 0 < p + lam * b t := by nlinarith
      have hd0 : 0 < p + lam := by linarith
      have he : geometryError G 0 p t = p / (p + lam * b t) := by
        simp [geometryError, hk0, G]
      rw [he, abs_of_pos (div_pos hp hden)]
      apply (div_le_div_iff₀ hden hd0).mpr
      nlinarith [mul_nonneg (mul_nonneg hp.le hlam.le) (sub_nonneg.mpr hbt)]
    · exact hlower 0 p hp
  have hsmall (eps : ℝ) (heps : 0 < eps) :
      ∃ p > (0 : ℝ), geometryRho G 0 p < ENNReal.ofReal eps := by
    let p := eps * lam
    have hp : 0 < p := mul_pos heps hlam
    refine ⟨p, hp, ?_⟩
    rw [hrho p hp]
    apply (ENNReal.ofReal_lt_ofReal_iff heps).mpr
    calc
      p / (p + lam) < p / lam := div_lt_div_of_pos_left hp hlam (by linarith)
      _ = eps := by dsimp [p]; field_simp
  refine ⟨fun _ p _ hp => hpositive _ p hp, hrho, hsmall, ?_⟩
  rintro ⟨z, hz⟩
  have hzlower := hlower z.1 z.2 hz.1.2
  obtain ⟨p, hp, hpr⟩ := hsmall (z.2 / (z.2 + lam)) (div_pos hz.1.2 (by linarith [hz.1.2]))
  have hopt := hz.2 (0, p) ⟨le_rfl, hp⟩
  exact not_lt_of_ge (hzlower.trans hopt) hpr
