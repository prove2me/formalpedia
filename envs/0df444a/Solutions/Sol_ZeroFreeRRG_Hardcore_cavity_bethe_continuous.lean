-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.cavity_bethe_continuous
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:55:04.167625+00:00
-- url     : https://prove2.me/submissions/182e3c3e-2aef-498f-b098-5622816b988d

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

private theorem bounded_ext {Y : Type} [TopologicalSpace Y] (K : Set Y) (hK : IsCompact K)
    (f : Y → ℝ) (hf : Continuous f) (c : Y → Y) (hc : Continuous c)
    (hck : ∀ y, c y ∈ K) : ∃ F : BoundedContinuousFunction Y ℝ, ∀ y, F y = f (c y) := by
  have hi : IsCompact (f '' K) := hK.image hf
  obtain ⟨C,hC⟩ := hi.isBounded.exists_norm_le
  let F : BoundedContinuousFunction Y ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun y => f (c y), hf.comp hc⟩ (2*C) (by
      intro x y
      have hx := hC _ ⟨c x,hck x,rfl⟩
      have hy := hC _ ⟨c y,hck y,rfl⟩
      change dist (f (c x)) (f (c y)) ≤ 2*C
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith))
  exact ⟨F,fun _ => rfl⟩

theorem solution (m : Model) (t : ℝ) (d : ℕ) :
    ContinuousOn (betheK m t d) (cavityLaws m t) := by
  classical
  let X := m.Spin → ℝ
  let clip : X → X := fun x a => max 0 (min (x a) 1)
  have hclipcont : Continuous clip := by
    apply continuous_pi
    intro a
    exact continuous_const.max ((continuous_apply a).min continuous_const)
  have hclip (x : X) : clip x ∈ Icc (0 : X) 1 := by
    constructor <;> intro a
    · change (0:ℝ) ≤ max 0 (min (x a) 1)
      exact le_max_left _ _
    · change max 0 (min (x a) 1) ≤ (1:ℝ)
      exact max_le (by norm_num) (min_le_right _ _)
  have hclipid (x : X) (hx : x ∈ stdSimplex ℝ m.Spin) : clip x = x := by
    funext a
    have h := mem_Icc_of_mem_stdSimplex hx a
    change max 0 (min (x a) 1) = x a
    rw [min_eq_left h.2, max_eq_right h.1]
  let V : (Fin d → X) → ℝ := fun xs => xlogx (vertexFactor m t d xs)
  have hV : Continuous V := by
    change Continuous (fun xs : Fin d → X => vertexFactor m t d xs * Real.log (vertexFactor m t d xs))
    apply Real.continuous_mul_log.comp
    unfold vertexFactor
    apply continuous_finset_sum
    intro a ha
    apply Continuous.const_mul
    apply continuous_finset_prod
    intro i hi
    dsimp [Mmul]
    apply continuous_finset_sum
    intro b hb
    have hi : Continuous (fun xs : Fin d → X => xs i) := continuous_apply i
    exact ((continuous_apply b).comp hi).const_mul _
  let Vclip : (Fin d → X) → (Fin d → X) := fun xs i => clip (xs i)
  have hVc : Continuous Vclip := by
    apply continuous_pi
    intro i
    exact hclipcont.comp (continuous_apply i)
  have hVck (xs : Fin d → X) : Vclip xs ∈ Icc (0 : Fin d → X) 1 := by
    constructor
    · intro i
      exact (hclip (xs i)).1
    · intro i
      exact (hclip (xs i)).2
  obtain ⟨FV,hFV⟩ := bounded_ext (Icc (0 : Fin d → X) 1) isCompact_Icc V hV Vclip hVc hVck
  have hVprob : Continuous (fun ν : ProbabilityMeasure X =>
      ∫ xs, FV xs ∂(ProbabilityMeasure.pi (fun _ : Fin d => ν) : Measure (Fin d → X))) := by
    have hpi : Continuous (fun ν : ProbabilityMeasure X => ProbabilityMeasure.pi (fun _ : Fin d => ν)) :=
      ProbabilityMeasure.continuous_pi.comp (continuous_pi (fun _ => continuous_id))
    exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction FV).comp hpi
  have hVactual : ContinuousOn (fun ν : ProbabilityMeasure X =>
      ∫ xs, V xs ∂(Measure.pi fun _ : Fin d => (ν : Measure X))) (cavityLaws m t) := by
    apply hVprob.continuousOn.congr
    intro ν hν
    change (∫ xs, V xs ∂(Measure.pi fun _ : Fin d => (ν : Measure X))) =
      (∫ xs, FV xs ∂(ProbabilityMeasure.pi (fun _ : Fin d => ν) : Measure (Fin d → X)))
    rw [ProbabilityMeasure.toMeasure_pi]
    apply integral_congr_ae
    have hs : ∀ᵐ x ∂(ν : Measure X), x ∈ stdSimplex ℝ m.Spin := ae_iff.mpr hν.1
    have hss : ∀ᵐ xs ∂(Measure.pi fun _ : Fin d => (ν : Measure X)),
        ∀ i, xs i ∈ stdSimplex ℝ m.Spin := by
      apply Measure.ae_pi_le_pi
      exact Filter.eventually_pi (fun _ => hs)
    filter_upwards [hss] with xs hx
    rw [hFV]
    congr 1
    funext i
    exact (hclipid (xs i) (hx i)).symm
  let E : X × X → ℝ := fun p => xlogx (edgeFactor m t p.1 p.2)
  have hE : Continuous E := by
    apply Real.continuous_mul_log.comp
    dsimp [edgeFactor]
    apply continuous_finset_sum
    intro a ha
    apply continuous_finset_sum
    intro b hb
    exact (((continuous_apply a).comp continuous_fst).mul continuous_const).mul
      ((continuous_apply b).comp continuous_snd)
  let Eclip : X × X → X × X := fun p => (clip p.1,clip p.2)
  have hEc : Continuous Eclip := (hclipcont.comp continuous_fst).prodMk (hclipcont.comp continuous_snd)
  have hEck (p : X × X) : Eclip p ∈ Icc (0:X) 1 ×ˢ Icc (0:X) 1 := ⟨hclip p.1,hclip p.2⟩
  obtain ⟨FE,hFE⟩ := bounded_ext (Icc (0:X) 1 ×ˢ Icc (0:X) 1)
    (isCompact_Icc.prod isCompact_Icc) E hE Eclip hEc hEck
  have hEprob : Continuous (fun ν : ProbabilityMeasure X =>
      ∫ p, FE p ∂(ν.prod ν : Measure (X × X))) := by
    have hp : Continuous (fun ν : ProbabilityMeasure X => ν.prod ν) :=
      ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_id)
    exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction FE).comp hp
  have hEactual : ContinuousOn (fun ν : ProbabilityMeasure X =>
      ∫ p, E p ∂((ν : Measure X).prod (ν : Measure X))) (cavityLaws m t) := by
    apply hEprob.continuousOn.congr
    intro ν hν
    change (∫ p, E p ∂((ν : Measure X).prod (ν : Measure X))) =
      (∫ p, FE p ∂(ν.prod ν : Measure (X × X)))
    rw [ProbabilityMeasure.toMeasure_prod]
    apply integral_congr_ae
    have hs : ∀ᵐ x ∂(ν : Measure X), x ∈ stdSimplex ℝ m.Spin := ae_iff.mpr hν.1
    have hfst := (Measure.quasiMeasurePreserving_fst (μ := (ν : Measure X)) (ν := (ν : Measure X))).ae hs
    have hsnd := (Measure.quasiMeasurePreserving_snd (μ := (ν : Measure X)) (ν := (ν : Measure X))).ae hs
    filter_upwards [hfst,hsnd] with p hp1 hp2
    rw [hFE]
    congr 1
    exact Prod.ext (hclipid p.1 hp1).symm (hclipid p.2 hp2).symm
  unfold betheK
  exact hVactual.sub (hEactual.const_mul _)
