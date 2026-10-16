-- Prove2me | solution 1 for RobustPoA.Tight.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-16T04:59:38.022393+00:00
-- url     : https://prove2.me/submissions/2e86c608-dadf-4118-b389-6b6a91c67b9c

import Definitions.Def_RobustPoA_Tight_Classes
import Mathlib

set_option autoImplicit false

open RobustPoA.Tight
open CongestionPoA.AsymSum
open scoped BigOperators
open scoped ENNReal

theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (lam mu : ℝ)
    (hcost : ∀ A, IsProfile G A → 0 ≤ sumCost G A)
    (hsmooth : IsSmoothCG G lam mu) (hmu : mu < 1) :
    purePoA G ≤ ENNReal.ofReal (lam / (1 - mu)) := by
  have h1mu : (0 : ℝ) < 1 - mu := sub_pos.mpr hmu
  -- Key real inequality: Nash cost vs any profile cost, via smoothness + Nash.
  have key : ∀ A A' : ι → Finset E, IsPureNash G A → IsProfile G A' →
      sumCost G A ≤ (lam / (1 - mu)) * sumCost G A' := by
    intro A A' hNash hA'
    obtain ⟨hAprof, hNash'⟩ := hNash
    have hsum : sumCost G A ≤ ∑ i, cost G (Function.update A i (A' i)) i := by
      show (∑ i, cost G A i) ≤ _
      exact Finset.sum_le_sum fun i _ => hNash' i (A' i) (hA' i)
    have hsm := hsmooth A A' hAprof hA'
    have hle : (1 - mu) * sumCost G A ≤ lam * sumCost G A' := by linarith [hsum, hsm]
    have hle2 : sumCost G A ≤ lam * sumCost G A' / (1 - mu) :=
      (le_div_iff₀ h1mu).mpr (by linarith [hle])
    have hconv : lam * sumCost G A' / (1 - mu) = (lam / (1 - mu)) * sumCost G A' := by ring
    rwa [hconv] at hle2
  show (⨆ A, ⨆ _ : IsPureNash G A, ENNReal.ofReal (sumCost G A) / optCost G) ≤
    ENNReal.ofReal (lam / (1 - mu))
  apply iSup_le
  intro A
  apply iSup_le
  intro hNash
  have hNashC := hNash
  obtain ⟨hAprof, _⟩ := hNashC
  set sA := sumCost G A with hsA
  set r := lam / (1 - mu) with hr
  have hsA0 : 0 ≤ sA := hcost A hAprof
  by_cases hsAeq : sA = 0
  · -- Zero Nash cost: 0 / optCost = 0 ≤ ofReal r.
    rw [hsAeq, ENNReal.ofReal_zero, ENNReal.zero_div]
    exact zero_le
  · have hsApos : 0 < sA := lt_of_le_of_ne hsA0 (Ne.symm hsAeq)
    -- At A' = A, key gives sA ≤ r * sA, hence 1 ≤ r (so r > 0).
    have hkeyAA : sA ≤ r * sA := key A A hNash hAprof
    have hr1 : (1 : ℝ) ≤ r := by
      apply le_of_mul_le_mul_left _ hsApos
      rw [mul_one, mul_comm]
      exact hkeyAA
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
    -- optCost is positive: every profile costs ≥ sA / r > 0.
    have hOPTpos : 0 < optCost G := by
      have hlow : ENNReal.ofReal (sA / r) ≤ optCost G := by
        show ENNReal.ofReal (sA / r) ≤
          ⨅ A', ⨅ _ : IsProfile G A', ENNReal.ofReal (sumCost G A')
        apply le_iInf
        intro A'
        apply le_iInf
        intro hA'
        apply ENNReal.ofReal_le_ofReal
        have hk := key A A' hNash hA'
        rw [div_le_iff₀ hrpos, mul_comm]
        exact hk
      have hpos2 : 0 < ENNReal.ofReal (sA / r) :=
        ENNReal.ofReal_pos.mpr (div_pos hsApos hrpos)
      exact lt_of_lt_of_le hpos2 hlow
    have hOPTtop : optCost G ≠ ⊤ := by
      have hle : optCost G ≤ ENNReal.ofReal sA := by
        apply iInf_le_of_le A
        apply iInf_le_of_le hAprof
        exact le_rfl
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    have hOPTne : optCost G ≠ 0 := ne_of_gt hOPTpos
    rw [ENNReal.div_le_iff_le_mul (Or.inl hOPTne) (Or.inl hOPTtop)]
    -- ofReal sA ≤ ofReal r * optCost, via distributing the product over the iInf.
    calc ENNReal.ofReal sA
        ≤ ⨅ A', ⨅ _ : IsProfile G A',
            (ENNReal.ofReal r * ENNReal.ofReal (sumCost G A')) := by
          apply le_iInf
          intro A'
          apply le_iInf
          intro hA'
          have hk := ENNReal.ofReal_le_ofReal (key A A' hNash hA')
          rwa [ENNReal.ofReal_mul hrpos.le] at hk
      _ = ENNReal.ofReal r * optCost G := by
          show (⨅ A', ⨅ _ : IsProfile G A',
              (ENNReal.ofReal r * ENNReal.ofReal (sumCost G A'))) =
            ENNReal.ofReal r *
              (⨅ A', ⨅ _ : IsProfile G A', ENNReal.ofReal (sumCost G A'))
          simp only [← ENNReal.mul_iInf_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr hrpos))
            ENNReal.ofReal_ne_top]

theorem RobustPoA.Tight.weak_duality {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (G : CongestionGame ι E) (lam mu : ℝ)
    (hcost : ∀ A, IsProfile G A → 0 ≤ sumCost G A)
    (hsmooth : IsSmoothCG G lam mu) (hmu : mu < 1) :
    purePoA G ≤ ENNReal.ofReal (lam / (1 - mu)) :=
  solution G lam mu hcost hsmooth hmu
