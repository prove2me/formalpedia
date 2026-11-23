-- Prove2me | solution 1 for ProcurementPoA.DeterministicCap.Supplement.remark_4_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:31:46.449432+00:00
-- url     : https://prove2.me/submissions/1d07748a-22a2-4b2f-8ff5-37757a94dc9e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FirstPrice_ValueAuction
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_StandardAuction
import Definitions.Def_ProcurementPoA_DeterministicCap_CapFormula
import Theorems.Thm_FirstPrice_tight_family
import Theorems.Thm_FirstPrice_affine_procurement
import Theorems.Thm_ProcurementPoA_DeterministicCap_Supplement_tight_ratio_limit

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Classical ENNReal
open ProcurementPoA.DeterministicCap

namespace ProcurementPoA.DeterministicCap.Supplement.Remark42Final

lemma tie_sum {n : ℕ} (τ : TieRule n) (b : Suppliers n → ℝ) :
    ∑ i, τ.select b {i} = 1 := by
  rw [sum_measure_singleton]
  simp

noncomputable def constProfile {n : ℕ} (b : ℝ) : MixedProfile n where
  bid _ := Kernel.const ℝ (Measure.dirac b)
  markov _ := inferInstance

noncomputable def tieZero : TieRule 0 where
  select := Kernel.const _ (Measure.dirac 0)
  markov := inferInstance
  lowest_only b := by
    simp only [Kernel.const_apply, ae_dirac_eq]
    filter_upwards [Filter.eventually_pure.2 (rfl : (0 : Suppliers 0) = 0)] with i hi
    intro j
    subst i
    rw [Fin.fin_one_eq_zero j]

lemma degenerate_costs (L : ℝ) {n : ℕ} (τ : TieRule n) :
    standardSocialCost (deterministicTypes (fun _ : Suppliers n => L)) τ (constProfile L) =
      ENNReal.ofReal L ∧
    optimalSocialCost (deterministicTypes (fun _ : Suppliers n => L)) = ENNReal.ofReal L := by
  let D : IndependentTypes n := deterministicTypes (fun _ : Suppliers n => L)
  haveI : IsProbabilityMeasure (playLaw D (constProfile L)) := by
    unfold playLaw
    infer_instance
  haveI : IsProbabilityMeasure (typeLaw D) := by
    unfold typeLaw
    infer_instance
  have hae : ∀ᵐ x ∂(playLaw D (constProfile L)), ∀ i, x i = (L, L) := by
    rw [ae_all_iff]
    intro i
    have hq := (measurePreserving_eval (fun i => D.law i ⊗ₘ (constProfile L).bid i) i).quasiMeasurePreserving
    unfold playLaw
    apply hq.ae (p := fun y : ℝ × ℝ => y = (L, L))
    apply (Measure.ae_compProd_iff (p := fun x : ℝ × ℝ => x = (L, L))
      (measurableSet_singleton (L, L))).2
    filter_upwards [mem_ae_iff.2 (D.concentrated i)] with c hc
    simp only [D, deterministicTypes, Set.mem_singleton_iff] at hc
    subst c
    simp [constProfile]
  have haeT : ∀ᵐ c ∂(typeLaw D), ∀ i, c i = L := by
    rw [ae_all_iff]
    intro i
    have hq := (measurePreserving_eval D.law i).quasiMeasurePreserving
    unfold typeLaw
    apply hq.ae (p := fun y : ℝ => y = L)
    exact mem_ae_iff.2 (D.concentrated i)
  have hSC : standardSocialCost D τ (constProfile L) = ENNReal.ofReal L := by
    unfold standardSocialCost
    have heq : ∫⁻ x, winnerCost τ x ∂(playLaw D (constProfile L)) =
        ∫⁻ _x, ENNReal.ofReal L ∂(playLaw D (constProfile L)) := by
      apply lintegral_congr_ae
      filter_upwards [hae] with x hx
      simp only [winnerCost, hx]
      rw [← Finset.mul_sum, tie_sum, mul_one]
    rw [heq]
    simp
  have hOPT : optimalSocialCost D = ENNReal.ofReal L := by
    unfold optimalSocialCost
    have heq : ∫⁻ c, ENNReal.ofReal (lowest c) ∂(typeLaw D) =
        ∫⁻ _c, ENNReal.ofReal L ∂(typeLaw D) := by
      apply lintegral_congr_ae
      filter_upwards [haeT] with c hc
      simp [lowest, hc]
    rw [heq]
    simp
  exact ⟨hSC, hOPT⟩

lemma degenerate_bne (L : ℝ) {n : ℕ} (τ : TieRule n) :
    IsBidSetBNE (deterministicTypes (fun _ : Suppliers n => L)) τ (constProfile L)
      (Set.Icc L L) := by
  let D : IndependentTypes n := deterministicTypes (fun _ : Suppliers n => L)
  change IsBidSetBNE D τ (constProfile L) (Set.Icc L L)
  refine ⟨?_, ?_, ?_⟩
  · intro i c hc
    have hcL : c = L := hc
    subst c
    simp [constProfile]
  · intro i c hc
    have hcL : c = L := hc
    subst c
    simp [constProfile]
  · intro i c hc
    have hcL : c = L := hc
    subst c
    simp only [constProfile, Kernel.const_apply, ae_dirac_eq]
    filter_upwards [Filter.eventually_pure.2 (rfl : L = L)] with b hb
    subst b
    intro a ha
    have haL : a = L := by simpa using ha
    subst a
    exact le_rfl

end ProcurementPoA.DeterministicCap.Supplement.Remark42Final

open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Remark42Final

theorem solution (L U : ℝ) (hL : 0 < L) (hLU : L ≤ U) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n),
      InCostInterval D L U ∧ IsBidSetBNE D τ σ (Set.Icc L U) ∧
      ENNReal.ofReal (1 + epsilon * (U / L - 1) - δ) ≤
        standardSocialCost D τ σ / optimalSocialCost D := by
  rcases hLU.eq_or_lt with hEq | hLT
  · subst U
    let D : IndependentTypes 0 := deterministicTypes (fun _ : Suppliers 0 => L)
    let σ : MixedProfile 0 := constProfile L
    refine ⟨0, D, tieZero, σ, ?_, degenerate_bne L tieZero, ?_⟩
    · intro i c hc
      have hcL : c = L := hc
      subst c
      exact ⟨le_rfl, le_rfl⟩
    · have hcosts := degenerate_costs L tieZero
      change ENNReal.ofReal (1 + epsilon * (L / L - 1) - δ) ≤
        standardSocialCost D tieZero σ / optimalSocialCost D
      change standardSocialCost D tieZero σ = ENNReal.ofReal L ∧
        optimalSocialCost D = ENNReal.ofReal L at hcosts
      rw [hcosts.1, hcosts.2]
      rw [ENNReal.div_self (ENNReal.ofReal_pos.2 hL).ne' ENNReal.ofReal_ne_top]
      have hsimple : 1 + epsilon * (L / L - 1) - δ = 1 - δ := by
        rw [div_self hL.ne']
        ring
      rw [hsimple]
      exact (ENNReal.ofReal_le_one).2 (by linarith)
  · obtain ⟨N, D, τ, σ, hval, heq, hoptlim, hwellim⟩ := FirstPrice.tight_family
    let opt : ℕ → ℝ := fun k => (FirstPrice.optimalWelfare (D k)).toReal
    let wel : ℕ → ℝ := fun k => (FirstPrice.welfare (D k) (τ k) (σ k)).toReal
    have hlim : Tendsto (fun k => (U - (U - L) * wel k) / (U - (U - L) * opt k)) atTop
        (𝓝 (1 + epsilon * (U / L - 1))) := by
      exact tight_ratio_limit L U hL hLU opt wel hoptlim hwellim
    have htarget : 1 + epsilon * (U / L - 1) - δ < 1 + epsilon * (U / L - 1) := by
      linarith
    obtain ⟨k, hk⟩ := (((tendsto_order.1 hlim).1 _ htarget)).exists
    obtain ⟨Dp, τp, σp, hcost, hbne, hSCtop, hOPTtop, hOPTpos, hSCreal, hOPTreal⟩ :=
      FirstPrice.affine_procurement L U hL hLT (D k) (τ k) (σ k) (hval k) (heq k)
    refine ⟨N k, Dp, τp, σp, hcost, hbne, ?_⟩
    have hratio : 1 + epsilon * (U / L - 1) - δ <
        (standardSocialCost Dp τp σp).toReal / (optimalSocialCost Dp).toReal := by
      rw [hSCreal, hOPTreal]
      exact hk
    calc
      ENNReal.ofReal (1 + epsilon * (U / L - 1) - δ) ≤
          ENNReal.ofReal ((standardSocialCost Dp τp σp).toReal /
            (optimalSocialCost Dp).toReal) := ENNReal.ofReal_le_ofReal hratio.le
      _ = standardSocialCost Dp τp σp / optimalSocialCost Dp := by
        rw [ENNReal.ofReal_div_of_pos hOPTpos, ENNReal.ofReal_toReal hSCtop,
          ENNReal.ofReal_toReal hOPTtop]
