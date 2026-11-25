-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_Conductor_proof_360c8994b5ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:20:34.370483+00:00
-- url     : https://prove2.me/submissions/1968c740-7ead-4bdd-82bc-409e50320061

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_domSub_iff_f130a9a451ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_fg_domSub_2df31f735772
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_exists_clear_7e98f59cc546
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mul_mem_secs_of_pullSecs_875330939677
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_ne_zero_of_isBirationalPt_026f5142f832
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_birational_clear_005110b90e73

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.Domination
namespace GroundTheory.Heights₂.Heights.Kleiman.Domination
namespace Conductor
theorem _root_.solution (hF : FiniteSections.Statement.{w, w}) : Conductor.Statement.{u, w} := by
  intro S _ _ Ω _ _ N N' x x' _ hbir hbir'
  classical
  have hx' : x' ≠ 0 := ne_zero_of_isBirationalPt hbir'
  have key : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∃ (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧
      aeval x f ≠ 0 ∧ ∀ b ∈ domRing S x x' i, aeval x f / x i ^ e * b ∈ chartRing S x (singleChart hi) := by
    intro i hi
    obtain ⟨d, ⟨f, e, hf, hf0, rfl⟩, hd⟩ := exists_clear (A := chartRing S x (singleChart hi))
      (fg_domSub hi hF hx')
      {y | ∃ (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ aeval x f ≠ 0 ∧ aeval x f / x i ^ e = y}
      ⟨1, 0, isHomogeneous_one _ _, by simp, by simp⟩
      (by
        rintro _ ⟨f, e, hf, hf0, rfl⟩ _ ⟨f', e', hf', hf0', rfl⟩
        refine ⟨f * f', e + e', hf.mul hf', by rw [map_mul]; exact mul_ne_zero hf0 hf0', ?_⟩
        rw [map_mul, pow_add, div_mul_div_comm])
      (by
        rintro _ ⟨f, e, hf, -, rfl⟩
        exact ⟨f, X i ^ e, e, pow_mem (X_mem_monos (Finset.mem_singleton_self i)) e, hf,
          isHomogeneous_X_pow i e, by rw [map_pow, aeval_X]⟩)
      (fun g _ => birational_clear hbir hi g)
    exact ⟨f, e, hf, hf0, fun b hb => hd b ((mem_domSub_iff hi b).mpr hb)⟩
  choose f e hf hf0 hfb using key
  have hG : (∏ j : {i // x i ≠ 0}, f j.1 j.2).IsHomogeneous (∑ j : {i // x i ≠ 0}, e j.1 j.2) :=
    IsHomogeneous.prod _ _ _ fun j _ => hf j.1 j.2
  have hsplit : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∃ w ∈ chartRing S x (singleChart hi),
      aeval x (∏ j : {i // x i ≠ 0}, f j.1 j.2) / x i ^ (∑ j : {i // x i ≠ 0}, e j.1 j.2) =
        aeval x (f i hi) / x i ^ e i hi * w := by
    intro i hi
    have hmem := Finset.mem_univ (⟨i, hi⟩ : {i // x i ≠ 0})
    refine ⟨aeval x (∏ j ∈ Finset.univ.erase (⟨i, hi⟩ : {i // x i ≠ 0}), f j.1 j.2) /
      x i ^ (∑ j ∈ Finset.univ.erase (⟨i, hi⟩ : {i // x i ≠ 0}), e j.1 j.2),
      ⟨_, X i ^ _, _, pow_mem (X_mem_monos (Finset.mem_singleton_self i)) _,
        IsHomogeneous.prod _ _ _ fun (j : {i // x i ≠ 0}) _ => hf j.1 j.2, isHomogeneous_X_pow i _,
        by rw [map_pow, aeval_X]⟩, ?_⟩
    rw [← Finset.mul_prod_erase _ (fun j : {i // x i ≠ 0} => f j.1 j.2) hmem,
      ← Finset.add_sum_erase _ (fun j : {i // x i ≠ 0} => e j.1 j.2) hmem, map_mul, pow_add,
      div_mul_div_comm]
  refine ⟨∑ j : {i // x i ≠ 0}, e j.1 j.2, aeval x (∏ j : {i // x i ≠ 0}, f j.1 j.2), ?_, ?_, ?_⟩
  · simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]
    intro I
    exact Submodule.subset_span ⟨_, 1, 0, _, one_mem _, hG, isHomogeneous_one _ _, by simp,
      by rw [map_one, div_one]⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hf0 j.1 j.2
  · intro L n z hz
    refine mul_mem_secs_of_pullSecs (fun i hi b hb l hl => ?_) z hz
    refine Submodule.subset_span ⟨_ * b, ?_, l, hl, by rw [smul_eq_mul, mul_assoc]⟩
    change _ ∈ twistMod S x _ (singleChart hi)
    rw [twistMod_eq_span _ (singleChart hi) (Finset.mem_singleton_self i), Submodule.mem_span_singleton]
    obtain ⟨w, hw, hw'⟩ := hsplit i hi
    have hmem : aeval x (∏ j : {i // x i ≠ 0}, f j.1 j.2) / x i ^ (∑ j : {i // x i ≠ 0}, e j.1 j.2) * b ∈
        chartRing S x (singleChart hi) := by
      rw [hw', show ∀ p q r : Ω, p * q * r = q * (p * r) from fun p q r => by ring]
      exact mul_mem hw (hfb i hi b hb)
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [chartRing_smul_def, zpow_natCast]
    field_simp
end Conductor
end GroundTheory.Heights₂.Heights.Kleiman.Domination
