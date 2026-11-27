-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartFormsRational_proof_da76d67b59ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:07:39.106051+00:00
-- url     : https://prove2.me/submissions/f163b49a-0b95-4079-bf16-5b560033732a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartFormsRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDualRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDetRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartFormsRational
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartFormsRational_mem_of_mem_chartRing_7697125cad1f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_detE_ne_zero_9a848b44ec1c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_detE_sum_a71ef09db231
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_exists_uniform_cde85cdc1d96
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_mem_of_cover_10a84b863bcf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_pow_mul_mem_mono_5061ec5b9960


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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ChartDualRational
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace ChartFormsRational
theorem _root_.solution : ChartFormsRational.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ x B e φ δ hsec hgen hδ i hx
  set K := chartFunField x i with hKdef
  have hR : ∀ a ∈ chartRing ℤ x i, a ∈ K := fun a ha ↦ ChartFormsRational.mem_of_mem_chartRing x i ha
  obtain ⟨r, f, c, hf, hc, hsum, hfr⟩ := B.frame i hx
  choose b hbli hbsp hbiff using hfr
  obtain ⟨lf, hlf⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hsum
  have hn1 : ∀ l p, ∃ m : ℕ, f l ^ m • b l p ∈ B.lat i := fun l p ↦
    (hbiff l (b l p)).2 ⟨Pi.single p 1, fun q ↦ ⟨0, by by_cases hq : q = p <;> simp [hq, one_mem, zero_mem]⟩,
      by simp [Pi.single_apply]⟩
  choose n hn using fun l ↦ exists_uniform (fun p m ↦ f l ^ m • b l p ∈ B.lat i)
    (fun p m m' hmm' h ↦ by
      rw [← pow_mul_pow_sub (f l) hmm', mul_comm, mul_smul]
      exact B.stable i _ (pow_mem (hf l) _) _ h) (hn1 l)
  obtain ⟨bb, hbb⟩ : ∃ bb : Module.Basis (Fin 2) Ω E, ∀ q, bb q = b lf q :=
    ⟨Module.Basis.mk (hbli lf) (hbsp lf).ge, fun q ↦ by simp⟩
  have hcoord : ∀ v ∈ B.lat i, ∀ q, ∃ t : ℕ, f lf ^ t * bb.coord q v ∈ chartRing ℤ x i := by
    intro v hv q
    obtain ⟨a, ha, rfl⟩ := (hbiff lf v).1 ⟨0, by simpa using hv⟩
    obtain ⟨t, ht⟩ := ha q
    refine ⟨t, ?_⟩
    have : bb.coord q (∑ p, a p • b lf p) = a q := by
      fin_cases q <;> simp [← hbb, Module.Basis.coord_apply, Module.Basis.repr_self]
    rwa [this]
  obtain ⟨M, hM⟩ := exists_uniform
    (fun (a : Fin r × Fin 2 × Fin 2) t ↦ f lf ^ t * bb.coord a.2.2 (f a.1 ^ n a.1 • b a.1 a.2.1) ∈ chartRing ℤ x i)
    (fun _ _ _ h h' ↦ pow_mul_mem_mono (hf lf) h h') (fun a ↦ hcoord _ (hn a.1 a.2.1) _)
  have hdual : ∀ q, f lf ^ M • bb.coord q ∈ T.dualLat B i := by
    intro q
    simp only [T.dualLat, Set.mem_ofPred_eq]
    intro v hv
    rw [LinearMap.smul_apply, smul_eq_mul]
    refine mem_of_cover hf hc hsum fun l ↦ ?_
    obtain ⟨a, ha, rfl⟩ := (hbiff l v).1 ⟨0, by simpa using hv⟩
    obtain ⟨m, hm⟩ := exists_uniform (fun p t ↦ f l ^ t * a p ∈ chartRing ℤ x i)
      (fun p _ _ h h' ↦ pow_mul_mem_mono (hf l) h h') ha
    refine ⟨m + n l, ?_⟩
    have : f l ^ (m + n l) * (f lf ^ M * bb.coord q (∑ p, a p • b l p)) =
        ∑ p, (f l ^ m * a p) * (f lf ^ M * bb.coord q (f l ^ n l • b l p)) := by
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, pow_add]
      exact Finset.sum_congr rfl fun p _ ↦ by ring
    rw [this]
    exact sum_mem fun p _ ↦ mul_mem (hm p) (hM (l, p, q))
  choose d hdR hd using fun q ↦ hgen i hx _ (hdual q)

  obtain ⟨g, hgdef⟩ : ∃ g : κ → Fin 2 → Ω, ∀ k q, g k q = φ k (bb q) / x i := ⟨_, fun _ _ ↦ rfl⟩
  have hφg : ∀ k q, φ k (bb q) = x i * g k q := fun k q ↦ by rw [hgdef]; field_simp
  have hfK : f lf ∈ K := hR _ (hf lf)
  have hgK : ∀ k q, g k q ∈ K := by
    intro k q
    have hs : f lf ^ n lf • bb q ∈ B.lat i := by rw [hbb]; exact hn lf q
    obtain ⟨a, ha, hae⟩ := (mem_lineLat x 1 i _).1 (hsec i hx k _ hs)
    rw [map_smul, smul_eq_mul, pow_one] at hae
    have : g k q = a / f lf ^ n lf := by
      rw [hgdef, div_eq_div_iff hx (pow_ne_zero _ hlf), hae]
      ring
    rw [this]
    exact div_mem (hR _ ha) (pow_mem hfK _)
  obtain ⟨k₀, k₁, hm⟩ : ∃ k₀ k₁, g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0 := by
    by_contra hmin
    push Not at hmin
    have hrow : ∀ q p, ∑ k, d q k * g k p = f lf ^ M * if p = q then 1 else 0 := by
      intro q p
      have h := LinearMap.congr_fun (hd q) (bb p)
      simp only [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
        LinearMap.sum_apply, smul_eq_mul] at h
      rw [h]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [hgdef]; ring
    have hdet : (∑ k, d 0 k * g k 0) * (∑ k, d 1 k * g k 1) - (∑ k, d 0 k * g k 1) * (∑ k, d 1 k * g k 0) = 0 := by
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun k' _ ↦ ?_
      linear_combination (d 0 k * d 1 k') * hmin k k'
    rw [hrow 0 0, hrow 1 1, hrow 0 1, hrow 1 0] at hdet
    simp [hlf] at hdet
  set m := g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 with hmdef
  have hmK : m ∈ K := sub_mem (mul_mem (hgK _ _) (hgK _ _)) (mul_mem (hgK _ _) (hgK _ _))

  set Db := T.detE e (bb 0) (bb 1) with hDbdef
  have hDb : Db ≠ 0 := ChartDetRatio.detE_ne_zero e bb bb.linearIndependent (by rw [bb.span_eq])
  have hexp : ∀ k q, φ k (bb q) = e.repr (bb q) 0 * φ k (e 0) + e.repr (bb q) 1 * φ k (e 1) := by
    intro k q
    have h := congrArg (φ k) (e.sum_repr (bb q))
    rw [Fin.sum_univ_two, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    exact h.symm
  have hDD : (φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1)) * Db = x i ^ 2 * m := by
    have h2 : x i ^ 2 * m = φ k₀ (bb 0) * φ k₁ (bb 1) - φ k₀ (bb 1) * φ k₁ (bb 0) := by
      rw [hmdef, hφg k₀ 0, hφg k₁ 1, hφg k₀ 1, hφg k₁ 0]
      ring
    rw [h2, hexp k₀ 0, hexp k₁ 1, hexp k₀ 1, hexp k₁ 0, hDbdef, T.detE]
    ring
  have hDne : φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hDD
    exact mul_ne_zero (pow_ne_zero 2 hx) hm hDD.symm

  have hcoordK : ∀ u ∈ B.lat i, ∃ a : Fin 2 → Ω, (∀ q, a q ∈ K) ∧ u = ∑ q, a q • bb q := by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := (hbiff lf u).1 ⟨0, by simpa using hu⟩
    refine ⟨a, fun q ↦ ?_, by simp only [hbb]⟩
    obtain ⟨t, ht⟩ := ha q
    have h2 : a q = (f lf ^ t)⁻¹ * (f lf ^ t * a q) := by
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hlf), one_mul]
    rw [h2]
    exact mul_mem (inv_mem (pow_mem hfK t)) (hR _ ht)
  have hdet : ∀ u ∈ B.lat i, ∀ w ∈ B.lat i, ∃ s ∈ K, T.detE e u w = Db * s := by
    intro u hu w hw
    obtain ⟨a, ha, rfl⟩ := hcoordK u hu
    obtain ⟨a', ha', rfl⟩ := hcoordK w hw
    refine ⟨a 0 * a' 1 - a 1 * a' 0, sub_mem (mul_mem (ha 0) (ha' 1)) (mul_mem (ha 1) (ha' 0)), ?_⟩
    rw [ChartDetRatio.detE_sum, mul_comm]
  have hspan : ∀ y ∈ Submodule.span (chartRing ℤ x i)
      {d | ∃ u ∈ B.lat i, ∃ w ∈ B.lat i, d = x i * T.detE e u w}, ∃ s ∈ K, y = x i * Db * s := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, w, hw, rfl⟩ := hy
      obtain ⟨s, hs, h⟩ := hdet u hu w hw
      exact ⟨s, hs, by rw [h]; ring⟩
    | zero => exact ⟨0, zero_mem _, by ring⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, hs, rfl⟩ := hy
      obtain ⟨t, ht, rfl⟩ := hz
      exact ⟨s + t, add_mem hs ht, by ring⟩
    | smul a y _ hy =>
      obtain ⟨s, hs, rfl⟩ := hy
      refine ⟨(a : Ω) * s, mul_mem (hR _ a.2) hs, ?_⟩
      rw [Subalgebra.smul_def, smul_eq_mul]
      ring
  have hδs : ∀ l, ∃ s ∈ K, δ l = x i * Db * s := fun l ↦ hspan _ ((hδ i hx).1 l)
  have h0 : f lf ^ n lf • bb 0 ∈ B.lat i := by rw [hbb]; exact hn lf 0
  have h1 : f lf ^ n lf • bb 1 ∈ B.lat i := by rw [hbb]; exact hn lf 1
  obtain ⟨l₀, hl₀⟩ : ∃ l₀, δ l₀ ≠ 0 := by
    by_contra h
    push Not at h
    have hmem := (hδ i hx).2 _ h0 _ h1
    have hbot : Submodule.span (chartRing ℤ x i) (Set.range fun l ↦ (x i)⁻¹ * δ l) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨l, rfl⟩
      simp [h l]
    rw [hbot, Submodule.mem_bot] at hmem
    have hsm : T.detE e (f lf ^ n lf • bb 0) (f lf ^ n lf • bb 1) = f lf ^ n lf * f lf ^ n lf * Db := by
      simp only [T.detE, map_smul, Finsupp.smul_apply, smul_eq_mul, hDbdef]
      ring
    rw [hsm] at hmem
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hlf) (pow_ne_zero _ hlf)) hDb hmem
  obtain ⟨s₀, hs₀, hδ₀⟩ := hδs l₀
  have hs₀ne : s₀ ≠ 0 := by
    rintro rfl
    exact hl₀ (by rw [hδ₀, mul_zero])
  refine ⟨l₀, k₀, k₁, hl₀, hDne, fun l ↦ ?_, ?_, ?_⟩
  · obtain ⟨s, hs, hδl⟩ := hδs l
    rw [hδl, hδ₀, mul_div_mul_left _ _ (mul_ne_zero hx hDb)]
    exact div_mem hs hs₀
  ·
    refine ⟨fun k ↦ (g k 0 * g k₁ 1 - g k 1 * g k₁ 0) / m, fun k ↦ (g k₀ 0 * g k 1 - g k₀ 1 * g k 0) / m,
      fun k ↦ div_mem (sub_mem (mul_mem (hgK _ _) (hgK _ _)) (mul_mem (hgK _ _) (hgK _ _))) hmK,
      fun k ↦ div_mem (sub_mem (mul_mem (hgK _ _) (hgK _ _)) (mul_mem (hgK _ _) (hgK _ _))) hmK, fun k ↦ ?_⟩
    have key : ∀ q : Fin 2, g k q = (g k 0 * g k₁ 1 - g k 1 * g k₁ 0) / m * g k₀ q +
        (g k₀ 0 * g k 1 - g k₀ 1 * g k 0) / m * g k₁ q := by
      rw [Fin.forall_fin_two]
      constructor <;>
        (rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hm, hmdef]; ring)
    refine bb.ext fun q ↦ ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hφg k q, hφg k₀ q, hφg k₁ q, key q]
    ring
  · have : (φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1)) * δ l₀ / x i ^ 3 = m * s₀ := by
      rw [hδ₀, show (φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1)) * (x i * Db * s₀) =
        (φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1)) * Db * x i * s₀ by ring, hDD,
        div_eq_iff (pow_ne_zero 3 hx)]
      ring
    rw [this]
    exact mul_mem hmK hs₀
end ChartFormsRational
end GroundTheory.Heights₂.Heights.Inter
