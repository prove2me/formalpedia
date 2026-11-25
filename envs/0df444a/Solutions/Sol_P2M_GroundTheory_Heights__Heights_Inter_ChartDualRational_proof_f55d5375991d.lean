-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_proof_f55d5375991d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:51:39.94539+00:00
-- url     : https://prove2.me/submissions/798ff5bd-2573-45d9-a472-023d888a90b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartDualRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDualRational
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_exists_uniform_cde85cdc1d96
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_pow_mul_mem_mono_5061ec5b9960
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_mem_of_cover_10a84b863bcf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_mem_adjoin_of_mem_chartRing_2994c878a15e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open ChartDualRational
namespace GroundTheory.Heights₂.Heights.Inter
namespace ChartDualRational
theorem _root_.solution : ChartDualRational.Statement := by
  intro Ω _ _ ι κ _ _ E _ _ x B φ i₀ hx hsec hgen
  obtain ⟨r, f, c, hf, hc, hsum, hfr⟩ := B.frame i₀ hx
  choose b hbli hbsp hbiff using hfr
  obtain ⟨l₀, hl₀⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hsum
  have hn1 : ∀ l p, ∃ m : ℕ, f l ^ m • b l p ∈ B.lat i₀ := fun l p ↦
    (hbiff l (b l p)).2 ⟨Pi.single p 1, fun q ↦ ⟨0, by by_cases hq : q = p <;> simp [hq, one_mem, zero_mem]⟩,
      by simp [Pi.single_apply]⟩
  choose n hn using fun l ↦ exists_uniform (fun p m ↦ f l ^ m • b l p ∈ B.lat i₀)
    (fun p m m' hmm' h ↦ by
      rw [← pow_mul_pow_sub (f l) hmm', mul_comm, mul_smul]
      exact B.stable i₀ _ (pow_mem (hf l) _) _ h) (hn1 l)
  obtain ⟨bb, hbb⟩ : ∃ bb : Module.Basis (Fin 2) Ω E, ∀ q, bb q = b l₀ q :=
    ⟨Module.Basis.mk (hbli l₀) (hbsp l₀).ge, fun q ↦ by simp⟩
  have hcoord : ∀ v ∈ B.lat i₀, ∀ q, ∃ t : ℕ, f l₀ ^ t * bb.coord q v ∈ chartRing ℤ x i₀ := by
    intro v hv q
    obtain ⟨a, ha, rfl⟩ := (hbiff l₀ v).1 ⟨0, by simpa using hv⟩
    obtain ⟨t, ht⟩ := ha q
    refine ⟨t, ?_⟩
    have : bb.coord q (∑ p, a p • b l₀ p) = a q := by
      fin_cases q <;> simp [← hbb, Module.Basis.coord_apply, Module.Basis.repr_self]
    rwa [this]
  obtain ⟨M, hM⟩ := exists_uniform
    (fun (a : Fin r × Fin 2 × Fin 2) t ↦ f l₀ ^ t * bb.coord a.2.2 (f a.1 ^ n a.1 • b a.1 a.2.1) ∈ chartRing ℤ x i₀)
    (fun _ _ _ h h' ↦ pow_mul_mem_mono (hf l₀) h h') (fun a ↦ hcoord _ (hn a.1 a.2.1) _)
  have hdual : ∀ q, f l₀ ^ M • bb.coord q ∈ T.dualLat B i₀ := by
    intro q
    simp only [T.dualLat, Set.mem_ofPred_eq]
    intro v hv
    rw [LinearMap.smul_apply, smul_eq_mul]
    refine mem_of_cover hf hc hsum fun l ↦ ?_
    obtain ⟨a, ha, rfl⟩ := (hbiff l v).1 ⟨0, by simpa using hv⟩
    obtain ⟨m, hm⟩ := exists_uniform (fun p t ↦ f l ^ t * a p ∈ chartRing ℤ x i₀)
      (fun p _ _ h h' ↦ pow_mul_mem_mono (hf l) h h') ha
    refine ⟨m + n l, ?_⟩
    have : f l ^ (m + n l) * (f l₀ ^ M * bb.coord q (∑ p, a p • b l p)) =
        ∑ p, (f l ^ m * a p) * (f l₀ ^ M * bb.coord q (f l ^ n l • b l p)) := by
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, pow_add]
      exact Finset.sum_congr rfl fun p _ ↦ by ring
    rw [this]
    exact sum_mem fun p _ ↦ mul_mem (hm p) (hM (l, p, q))
  choose d hdR hd using fun q ↦ hgen i₀ hx _ (hdual q)
  refine ⟨bb, fun k q ↦ φ k (bb q) / x i₀, fun k q ↦ by field_simp, fun k q ↦ ?_, ?_⟩
  · have hs : f l₀ ^ n l₀ • bb q ∈ B.lat i₀ := by rw [hbb]; exact hn l₀ q
    obtain ⟨a, ha, hae⟩ := (mem_lineLat x 1 i₀ _).1 (hsec i₀ hx k _ hs)
    rw [map_smul, smul_eq_mul, pow_one] at hae
    have : φ k (bb q) / x i₀ = a / f l₀ ^ n l₀ := by
      rw [div_eq_div_iff hx (pow_ne_zero _ hl₀), hae]
      ring
    show φ k (bb q) / x i₀ ∈ _
    rw [this]
    exact div_mem (mem_adjoin_of_mem_chartRing x i₀ ha) (pow_mem (mem_adjoin_of_mem_chartRing x i₀ (hf l₀)) _)
  · by_contra hmin
    push Not at hmin
    have hm : ∀ k k', φ k (bb 0) / x i₀ * (φ k' (bb 1) / x i₀) - φ k (bb 1) / x i₀ * (φ k' (bb 0) / x i₀) = 0 :=
      fun k k' ↦ hmin k k'
    have hrow : ∀ q p, ∑ k, d q k * (φ k (bb p) / x i₀) = f l₀ ^ M * if p = q then 1 else 0 := by
      intro q p
      have h := LinearMap.congr_fun (hd q) (bb p)
      simp only [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
        LinearMap.sum_apply, smul_eq_mul] at h
      rw [h]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    have hdet : (∑ k, d 0 k * (φ k (bb 0) / x i₀)) * (∑ k, d 1 k * (φ k (bb 1) / x i₀)) -
        (∑ k, d 0 k * (φ k (bb 1) / x i₀)) * (∑ k, d 1 k * (φ k (bb 0) / x i₀)) = 0 := by
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun k' _ ↦ ?_
      linear_combination (d 0 k * d 1 k') * hm k k'
    rw [hrow 0 0, hrow 1 1, hrow 0 1, hrow 1 0] at hdet
    simp [hl₀] at hdet
end ChartDualRational
end GroundTheory.Heights₂.Heights.Inter
