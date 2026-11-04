-- Prove2me | solution 1 for SysRiskPortfolio.CoER.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T06:55:08.510221+00:00
-- url     : https://prove2.me/submissions/40aad507-a070-4f50-a7cb-69dbd278ab9b

import Mathlib
import Theorems.Thm_SysRiskPortfolio_CoER_proposition_1
import Theorems.Thm_SysRiskPortfolio_CoER_landsman_step

open Matrix SysRiskPortfolio.CoER

theorem solution {m : ℕ} (d : PortfolioData m) (hd : Standing d) (hlam : Real.sqrt (Del (optimData d) ⬝ᵥ ((Qm (optimData d))⁻¹ *ᵥ Del (optimData d))) < (optimData d).lam) : (∑ i, wStar (optimData d) i) = 1 ∧ (∀ w : Fin (m + 1) → ℝ, (∑ i, w i) = 1 → coerPort d w ≤ coerPort d (wStar (optimData d))) ∧ (∀ w : Fin (m + 1) → ℝ, (∑ i, w i) = 1 → coerPort d w = coerPort d (wStar (optimData d)) → w = wStar (optimData d)) := by
  obtain ⟨hm1, hqm0, hqm1, hqp0, hqp1, hsm, hJ⟩ := hd
  have hsm2 : (0:ℝ) < d.sigM ^ 2 := by positivity
  -- quadratic form of the joint covariance on a block vector
  have hquad : ∀ (x : Fin (m + 1) → ℝ) (t : ℝ),
      star (Sum.elim x (fun _ : Unit => t)) ⬝ᵥ (jointCov d *ᵥ Sum.elim x (fun _ : Unit => t))
        = x ⬝ᵥ (d.Sig *ᵥ x) + 2 * t * (x ⬝ᵥ d.sig) + t ^ 2 * d.sigM ^ 2 := by
    intro x t
    have hsym : ∀ i j, d.Sig j i = d.Sig i j := by
      intro i j
      have := hJ.isHermitian.apply (Sum.inl i) (Sum.inl j)
      simpa [jointCov, fromBlocks] using this
    simp only [jointCov, fromBlocks, of_apply, star_trivial, dotProduct, mulVec, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr,
      replicateCol_apply, replicateRow_apply, Fintype.univ_unit, Finset.sum_singleton]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    have h1 : ∑ i, 2 * t * (x i * d.sig i)
        = ∑ i, x i * (d.sig i * t) + ∑ i, t * (d.sig i * x i) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [h1]; ring
  have hsym : ∀ i j, d.Sig j i = d.Sig i j := by
    intro i j
    have := hJ.isHermitian.apply (Sum.inl i) (Sum.inl j)
    simpa [jointCov, fromBlocks] using this
  -- the quadratic form of Σ̂
  have hSq : ∀ x : Fin (m + 1) → ℝ, x ⬝ᵥ ((optimData d).SigHat *ᵥ x)
      = x ⬝ᵥ (d.Sig *ᵥ x) - (1 / d.sigM ^ 2) * (x ⬝ᵥ d.sig) ^ 2 := by
    intro x
    simp only [optimData, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]
    congr 2
    simp [dotProduct, mulVec, vecMulVec, Finset.mul_sum, sq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hS : (optimData d).SigHat.PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · ext i j
      simp [optimData, hsym, vecMulVec, mul_comm]
    · intro x hx
      rw [star_trivial, hSq]
      have hz : Sum.elim x (fun _ : Unit => -(x ⬝ᵥ d.sig) / d.sigM ^ 2) ≠ 0 := by
        intro h; apply hx; funext i; exact congrFun h (Sum.inl i)
      have := hJ.dotProduct_mulVec_pos hz
      rw [hquad] at this
      have e : x ⬝ᵥ (d.Sig *ᵥ x) + 2 * (-(x ⬝ᵥ d.sig) / d.sigM ^ 2) * (x ⬝ᵥ d.sig)
          + (-(x ⬝ᵥ d.sig) / d.sigM ^ 2) ^ 2 * d.sigM ^ 2
          = x ⬝ᵥ (d.Sig *ᵥ x) - (1 / d.sigM ^ 2) * (x ⬝ᵥ d.sig) ^ 2 := by
        field_simp; ring
      linarith
  have hobj : ∀ w : Fin (m + 1) → ℝ, (∑ i, w i) = 1 →
      coerPort d w = objective (optimData d) w := by
    intro w hw
    rw [proposition_1 d ⟨hm1, hqm0, hqm1, hqp0, hqp1, hsm, hJ⟩ w hw, objective, hSq]
    have : w ⬝ᵥ (optimData d).muHat = w ⬝ᵥ d.mu + (PhiInv d.qm / d.sigM) * (w ⬝ᵥ d.sig) := by
      simp [optimData, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this]; rfl
  obtain ⟨h1, h2, h3⟩ := landsman_step hm1 (optimData d) hS hlam
  refine ⟨h1, fun w hw => ?_, fun w hw he => ?_⟩
  · rw [hobj w hw, hobj _ h1]; exact h2 w hw
  · rw [hobj w hw, hobj _ h1] at he; exact h3 w hw he
