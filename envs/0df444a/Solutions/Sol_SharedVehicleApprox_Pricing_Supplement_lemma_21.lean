-- Prove2me | solution 1 for SharedVehicleApprox.Pricing.Supplement.lemma_21
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:41.174659+00:00
-- url     : https://prove2.me/submissions/96a556b7-f4ad-4601-aea8-ad41d203e3fc

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_SupplyRedirection
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm3

open Finset QueueingFundamentals.Networks

open SharedVehicleApprox
open SharedVehicleApprox.Pricing
open SharedVehicleApprox.Pricing.Supplement

/-- Lemma 21, p. 25 (corrected: the induced routing is strongly connected, and the denominator
misprint in `r̃` is repaired): under `q̃` and `r̃` returned by Algorithm 3 the induced demand `φ̄` is
balanced and every availability in the infinite-unit system equals one. -/
theorem solution {n : ℕ} [NeZero n] (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I : Fin n → Fin n → ℝ → ℝ)
    (hR : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve I i j))
    (c qt zt : Fin n → Fin n → ℝ) (hopt : IsAlg3Optimal φ I c qt zt)
    (hconn : SupportConnected (inducedDemand φ qt (redirectProb φ qt zt)) (fun _ _ => 1)) :
    IsBalanced (inducedDemand φ qt (redirectProb φ qt zt)) (fun _ _ => 1) ∧
      ∀ r : Fin n → ℝ, (∀ i, 0 < r i) →
        IsTraffic (inducedDemand φ qt (redirectProb φ qt zt)) (fun _ _ => 1) r →
          ∀ i, availInf r i = 1 := by
            obtain ⟨⟨hq, hz, hcirc, hzle⟩, -⟩ := hopt
            set D : Fin n → ℝ := fun i => ∑ k, φ k i * qt k i with hD
            have hDnn : ∀ i, 0 ≤ D i := fun i =>
              Finset.sum_nonneg (fun k _ => mul_nonneg (hφ k i) (hq k i).1)
            set rr := redirectProb φ qt zt with hrr
            have hrrD : ∀ i l, rr i l * D i = zt i l := by
              intro i l
              by_cases h0 : D i = 0
              · have h1 : zt i l ≤ ∑ k, zt i k :=
                  Finset.single_le_sum (fun k _ => hz i k) (Finset.mem_univ l)
                have h2 := hzle i
                have : zt i l = 0 := le_antisymm (by simp only [hD] at h0; linarith) (hz i l)
                rw [h0, this, mul_zero]
              · show zt i l / D i * D i = zt i l
                exact div_mul_cancel₀ _ h0
            have hrrnn : ∀ i l, 0 ≤ rr i l := fun i l => div_nonneg (hz i l) (hDnn i)
            have hrrle : ∀ i, ∑ l, rr i l ≤ 1 := by
              intro i
              show ∑ l, zt i l / D i ≤ 1
              rw [← Finset.sum_div]
              exact div_le_one_of_le₀ (hzle i) (hDnn i)
            set A := inducedDemand φ qt rr with hA
            have hAnn : ∀ i j, 0 ≤ A i j := by
              intro i j
              show 0 ≤ φ i j * qt i j * (1 - ∑ k, rr j k) + ∑ k, φ i k * qt i k * rr k j
              have := hrrle j
              apply add_nonneg
              · exact mul_nonneg (mul_nonneg (hφ i j) (hq i j).1) (by linarith)
              · exact Finset.sum_nonneg (fun k _ => mul_nonneg (mul_nonneg (hφ i k) (hq i k).1) (hrrnn k j))
            have hout : ∀ i, ∑ j, A i j = ∑ j, φ i j * qt i j := by
              intro i
              simp only [hA, inducedDemand, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib,
                Finset.mul_sum]
              rw [Finset.sum_comm (f := fun j k => φ i k * qt i k * rr k j)]
              ring
            have hin : ∀ i, ∑ k, A k i = ∑ j, φ i j * qt i j := by
              intro i
              have e : ∑ k, A k i = D i * (1 - ∑ l, rr i l) + ∑ l, rr l i * D l := by
                simp only [hA, inducedDemand, Finset.sum_add_distrib, hD]
                rw [← Finset.sum_mul, Finset.sum_comm]
                congr 1
                refine Finset.sum_congr rfl (fun l _ => ?_)
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun k _ => ?_)
                ring
              rw [e, mul_sub, mul_one, Finset.mul_sum]
              simp only [fun l => mul_comm (D i) (rr i l), hrrD]
              have := hcirc i
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
              linarith
            have hbal : IsBalanced A (fun _ _ => 1) := by
              intro i
              simp only [mul_one]
              rw [hin, hout]
            refine ⟨hbal, ?_⟩
            intro r hr htr i
            set M := rmax r with hM
            have hle : ∀ j, r j ≤ M := fun j => Finset.le_sup' r (Finset.mem_univ j)
            obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin n)) r
            have hi0' : r i0 = M := hi0.symm
            have hpred : ∀ a c, 0 < A a c → r c = M → r a = M := by
              intro a c hac hc
              have ht := htr c
              have hb := hbal c
              simp only [mul_one] at ht hb
              rw [hc] at ht
              have hsum : ∑ j, (M - r j) * A j c = 0 := by
                simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
                rw [hb, ← ht]
                ring
              have hnn : ∀ j ∈ Finset.univ, 0 ≤ (M - r j) * A j c :=
                fun j _ => mul_nonneg (by linarith [hle j]) (hAnn j c)
              have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum a (Finset.mem_univ a)
              rcases mul_eq_zero.1 this with h | h
              · linarith
              · linarith
            have hall : r i = M := by
              have hpath := hconn i i0
              induction hpath using Relation.ReflTransGen.head_induction_on with
              | refl => exact hi0'
              | head hab _ ih =>
                obtain ⟨-, hpos⟩ := hab
                exact hpred _ _ (by simpa using hpos) ih
            have hMpos : 0 < M := hi0' ▸ hr i0
            show r i / M = 1
            rw [hall, div_self hMpos.ne']
