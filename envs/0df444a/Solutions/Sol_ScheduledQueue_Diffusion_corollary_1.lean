-- Prove2me | solution 1 for ScheduledQueue.Diffusion.corollary_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:32:36.936369+00:00
-- url     : https://prove2.me/submissions/427d60dc-c708-4534-b27b-42ca357b2eca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting
import Theorems.Thm_ScheduledQueue_Diffusion_reversed_representation
import Theorems.Thm_ScheduledQueue_Diffusion_op_reduction
import Theorems.Thm_ScheduledQueue_Diffusion_donsker_limit

open MeasureTheory ProbabilityTheory Set Filter Topology NNReal
open ScheduledQueue.Diffusion

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U)
    (V : ℕ → Ω → ℝ) (hV : ServiceInput P ξ U V) (hmean : ∫ ω, V 1 ω ∂P = h)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') :
    TendstoInDistribution (fun t : ℝ => fun ω => (Real.sqrt t)⁻¹ * workload h ξ U V t ω) atTop
      (fun ω' => Real.sqrt (variance (V 1) P / h) * reflectedAtOne B ω') (fun _ => P) P' := by
  -- the reflected perturbations `-ξ`
  set ξ' : ℤ → Ω → ℝ := fun j ω => -ξ j ω with hξ'
  have hin' : ScheduledQueue.Stability.ScheduledInput P ξ' U :=
    { measurable := fun j => (hin.measurable j).neg
      indep := hin.indep.comp (fun _ x => -x) (fun _ => measurable_neg)
      identDistrib := fun j => (hin.identDistrib j).comp measurable_neg
      integrable := hin.integrable.neg
      uniform := hin.uniform
      indep_shift := by
        have hm : Measurable (fun (f : ℤ → ℝ) (j : ℤ) => -f j) :=
          measurable_pi_lambda _ (fun j => (measurable_pi_apply j).neg)
        exact hin.indep_shift.comp measurable_id hm }
  have hV' : ServiceInput P ξ' U V :=
    { measurable := hV.measurable
      indep := hV.indep
      identDistrib := hV.identDistrib
      memLp := hV.memLp
      indep_input := by
        have hm : Measurable (fun (p : ℝ × (ℤ → ℝ)) => (p.1, fun j => -p.2 j)) :=
          measurable_fst.prodMk
            (measurable_pi_lambda _ (fun j => ((measurable_pi_apply j).comp measurable_snd).neg))
        exact hV.indep_input.comp measurable_id hm }
  -- the reversed-time process
  set R : ℝ → Ω → ℝ := fun t ω => ⨆ s : Icc 0 t,
      ((∑ i ∈ Finset.Icc 1 (ScheduledQueue.Stability.count h ξ' U s ω), V i ω) - s) with hR
  set D : ℝ → Ω → ℝ := fun t ω => (Real.sqrt t)⁻¹ *
      ⨆ s : Icc (0 : ℝ) 1, ∑ i ∈ Finset.Icc 1 (ScheduledQueue.Stability.count h ξ' U (s * t) ω),
        (V i ω - h) with hD
  have hrev := reversed_representation P h hh ξ U hin V hV
  have hop := op_reduction P h hh ξ' U hin' V hV' hmean
  have hdon := donsker_limit P h hh ξ' U hin' V hV' hmean P' B hB
  -- measurability of `R t`
  have hRmeas : ∀ t, AEMeasurable (R t) P := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact (hrev t ht).aemeasurable_snd
    · have : IsEmpty (Icc (0 : ℝ) t) := by
        rw [isEmpty_coe_sort, Set.Icc_eq_empty_iff]; exact not_le.mpr ht
      have hc : R t = fun _ => 0 := by
        funext ω; simp only [hR]; exact Real.iSup_of_isEmpty _
      rw [hc]; exact aemeasurable_const
  -- Slutsky: `t^{-1/2} R(t) ⇒ limit`
  have hY : TendstoInDistribution (fun t ω => (Real.sqrt t)⁻¹ * R t ω) atTop
      (fun ω' => Real.sqrt (variance (V 1) P / h) * reflectedAtOne B ω') (fun _ => P) P' := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hdon ?_ ?_
    · exact hop
    · intro t; exact (hRmeas t).const_mul _
  -- transfer through the identity in law `W(t) =d R(t)`
  have hWmeas : ∀ t, AEMeasurable (fun ω => (Real.sqrt t)⁻¹ * workload h ξ U V t ω) P := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact (hrev t ht).aemeasurable_fst.const_mul _
    · have : IsEmpty (Icc (0 : ℝ) t) := by
        rw [isEmpty_coe_sort, Set.Icc_eq_empty_iff]; exact not_le.mpr ht
      have hc : (fun ω => (Real.sqrt t)⁻¹ * workload h ξ U V t ω) = fun _ => 0 := by
        funext ω; simp only [workload]; rw [Real.iSup_of_isEmpty]; simp
      rw [hc]; exact aemeasurable_const
  refine ⟨hWmeas, hY.aemeasurable_limit, ?_⟩
  refine hY.tendsto.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  apply Subtype.ext
  simp only
  have hid := ((hrev t ht).comp (measurable_const_mul (Real.sqrt t)⁻¹))
  exact hid.map_eq.symm
