-- Prove2me | solution 1 for SysRiskPortfolio.CoER.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T06:56:13.78341+00:00
-- url     : https://prove2.me/submissions/0a3ede23-8b60-4203-b7a4-093df5c7bee0

import Mathlib
import Theorems.Thm_SysRiskPortfolio_CoER_eq_A4
import Definitions.Def_SysRiskPortfolio_CoER_Portfolio

open Matrix SysRiskPortfolio.CoER

theorem solution {m : ℕ} (d : PortfolioData m) (hd : Standing d) (w : Fin (m + 1) → ℝ) (hw : ∑ i, w i = 1) : coerPort d w = w ⬝ᵥ d.mu + (PhiInv d.qm / d.sigM) * (w ⬝ᵥ d.sig) - (phi (PhiInv d.qp) / d.qp) * Real.sqrt (w ⬝ᵥ (d.Sig *ᵥ w) - (1 / d.sigM ^ 2) * (w ⬝ᵥ d.sig) ^ 2) := by
  obtain ⟨hm1, hqm0, hqm1, hqp0, hqp1, hsm, hJ⟩ := hd
  have hsm2 : (0:ℝ) < d.sigM ^ 2 := by positivity
  have hquad : ∀ (x : Fin (m + 1) → ℝ) (t : ℝ),
      star (Sum.elim x (fun _ : Unit => t)) ⬝ᵥ (jointCov d *ᵥ Sum.elim x (fun _ : Unit => t))
        = x ⬝ᵥ (d.Sig *ᵥ x) + 2 * t * (x ⬝ᵥ d.sig) + t ^ 2 * d.sigM ^ 2 := by
    intro x t
    simp only [jointCov, fromBlocks, of_apply, star_trivial, dotProduct, mulVec, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr,
      replicateCol_apply, replicateRow_apply, Fintype.univ_unit, Finset.sum_singleton]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    have h1 : ∑ i, 2 * t * (x i * d.sig i)
        = ∑ i, x i * (d.sig i * t) + ∑ i, t * (d.sig i * x i) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [h1]; ring
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hz : Sum.elim w (fun _ : Unit => -(w ⬝ᵥ d.sig) / d.sigM ^ 2) ≠ 0 := by
    intro h; apply hw0; funext i; exact congrFun h (Sum.inl i)
  have hz0 : Sum.elim w (fun _ : Unit => (0:ℝ)) ≠ 0 := by
    intro h; apply hw0; funext i; exact congrFun h (Sum.inl i)
  have hA := hJ.dotProduct_mulVec_pos hz
  have hB := hJ.dotProduct_mulVec_pos hz0
  rw [hquad] at hA hB
  set V := w ⬝ᵥ (d.Sig *ᵥ w) with hV
  set c := w ⬝ᵥ d.sig with hc
  have hVpos : 0 < V := by nlinarith
  have hK : V - (1 / d.sigM ^ 2) * c ^ 2 > 0 := by
    have e : V + 2 * (-c / d.sigM ^ 2) * c + (-c / d.sigM ^ 2) ^ 2 * d.sigM ^ 2
        = V - (1 / d.sigM ^ 2) * c ^ 2 := by field_simp; ring
    linarith
  have hsp : 0 < sigP d w := Real.sqrt_pos.mpr hVpos
  have hsp2 : sigP d w ^ 2 = V := Real.sq_sqrt hVpos.le
  have hrho : |rhoP d w| < 1 := by
    rw [abs_lt]
    have hr2 : rhoP d w ^ 2 < 1 := by
      unfold rhoP
      rw [div_pow, mul_pow, hsp2, div_lt_one (by positivity)]
      have : c ^ 2 < d.sigM ^ 2 * V := by
        have := mul_lt_mul_of_pos_left hK hsm2
        field_simp at this
        nlinarith
      exact this
    constructor <;> nlinarith [sq_nonneg (rhoP d w)]
  have key := eq_A4 (muP d w) d.muM (sigP d w) d.sigM (rhoP d w) d.qm d.qp hsp hsm hrho
    ⟨hqm0, by linarith⟩ ⟨hqp0, by linarith⟩
  unfold coerPort
  rw [key]
  have e1 : sigP d w * rhoP d w = c / d.sigM := by
    unfold rhoP; field_simp; rw [hc]
  have e2 : sigP d w * Real.sqrt (1 - rhoP d w ^ 2) = Real.sqrt (V - (1 / d.sigM ^ 2) * c ^ 2) := by
    rw [← Real.sqrt_sq hsp.le, ← Real.sqrt_mul (sq_nonneg _), hsp2]
    congr 1
    unfold rhoP
    rw [div_pow, mul_pow, hsp2]
    field_simp
    rw [← hc]
  have : sigP d w * (rhoP d w * PhiInv d.qm - 1 / d.qp * √(1 - rhoP d w ^ 2) * phi (PhiInv d.qp))
      = (sigP d w * rhoP d w) * PhiInv d.qm
        - (phi (PhiInv d.qp) / d.qp) * (sigP d w * √(1 - rhoP d w ^ 2)) := by ring
  rw [this, e1, e2]
  unfold muP
  ring
