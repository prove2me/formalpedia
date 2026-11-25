-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_polynomial_dvd_of_eval_eq_mul_near_roots_56a9bd694800
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:09:23.35351+00:00
-- url     : https://prove2.me/submissions/5d458cd4-6cd8-4cd7-8cb3-f6ec245f6c78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassRemainderUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {U : Set ℂ} (hU : IsOpen U) :
    ∀ (n : ℕ) (W P : ℂ[X]) (g : ℂ → ℂ), W.Monic → W.natDegree = n → ContinuousOn g U →
      (∀ t ∈ U, P.eval t = g t * W.eval t) → (∀ t, W.IsRoot t → t ∈ U) → W ∣ P := by
  intro n
  induction n with
  | zero =>
    intro W P g hW hn _ _ _
    rw [hW.natDegree_eq_zero.1 hn]
    exact one_dvd P
  | succ n ih =>
    intro W P g hW hn hg hPW hroots
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root W (by
      rw [degree_eq_natDegree hW.ne_zero, hn]; exact_mod_cast Nat.succ_ne_zero n)
    have hαU : α ∈ U := hroots α hα
    have hPα : P.IsRoot α := by
      show P.eval α = 0
      rw [hPW α hαU, show W.eval α = 0 from hα, mul_zero]
    have hW₁ : (X - C α) * (W /ₘ (X - C α)) = W := mul_divByMonic_eq_iff_isRoot.2 hα
    have hP₁ : (X - C α) * (P /ₘ (X - C α)) = P := mul_divByMonic_eq_iff_isRoot.2 hPα
    have hW₁m : (W /ₘ (X - C α)).Monic := (monic_X_sub_C α).of_mul_monic_left (by rw [hW₁]; exact hW)
    have hW₁n : (W /ₘ (X - C α)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C α), hn, natDegree_X_sub_C]; rfl
    have hcont : ContinuousOn (fun t => g t * (W /ₘ (X - C α)).eval t) U :=
      hg.mul (W /ₘ (X - C α)).continuous.continuousOn
    have hoff : ∀ s ∈ U, s ≠ α → (P /ₘ (X - C α)).eval s = g s * (W /ₘ (X - C α)).eval s := by
      intro s hsU hs
      have h := hPW s hsU
      rw [← hP₁, ← hW₁, eval_mul, eval_mul] at h
      have hne : (X - C α).eval s ≠ 0 := by
        simp only [eval_sub, eval_X, eval_C]; exact sub_ne_zero.2 hs
      exact mul_left_cancel₀ hne (by rw [h]; ring)
    have hP₁eq : ∀ t ∈ U, (P /ₘ (X - C α)).eval t = g t * (W /ₘ (X - C α)).eval t := by
      intro t ht
      by_cases htα : t = α
      · have h1 : Tendsto (fun s => (P /ₘ (X - C α)).eval s) (𝓝[≠] t) (𝓝 ((P /ₘ (X - C α)).eval t)) :=
          (P /ₘ (X - C α)).continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        have h2 : Tendsto (fun s => g s * (W /ₘ (X - C α)).eval s) (𝓝[≠] t)
            (𝓝 (g t * (W /ₘ (X - C α)).eval t)) :=
          (hcont.continuousAt (hU.mem_nhds ht)).tendsto.mono_left nhdsWithin_le_nhds
        refine tendsto_nhds_unique (h1.congr' ?_) h2
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds ht)] with s hs hsU
        exact hoff s hsU (htα ▸ hs)
      · exact hoff t ht htα
    have hdvd := ih _ _ g hW₁m hW₁n hg hP₁eq (fun t ht => hroots t (by
      rw [← hW₁]; show ((X - C α) * (W /ₘ (X - C α))).eval t = 0
      rw [eval_mul, show (W /ₘ (X - C α)).eval t = 0 from ht, mul_zero]))
    rw [← hW₁, ← hP₁]
    exact mul_dvd_mul_left _ hdvd
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
