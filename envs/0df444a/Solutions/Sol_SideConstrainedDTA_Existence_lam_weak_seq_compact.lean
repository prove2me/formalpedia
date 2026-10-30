-- Prove2me | solution 1 for SideConstrainedDTA.Existence.lam_weak_seq_compact
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:33:22.086705+00:00
-- url     : https://prove2.me/submissions/5d0f3ae0-9be9-4e39-9e7d-dc6a7c1db05f

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting

open MeasureTheory Set Filter Topology

open SideConstrainedDTA.Existence

theorem solution {I W E : Type*} [Fintype W] [DecidableEq I]
    (N : Model I W E) (hs : ℕ → W → ℝ → ℝ) (hhs : ∀ n, Lam N (hs n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ hstar : W → ℝ → ℝ, Lam N hstar ∧
      WeakTendsto N (fun n => hs (φ n)) hstar := by
  classical
  set μ : Measure ℝ := volume.restrict (Icc N.t0 N.tf) with hμ
  have : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
  have hbd : ∀ n p, ∀ᵐ t ∂μ, 0 ≤ hs n p t ∧ hs n p t ≤ N.B p := by
    intro n p
    have h1 := ae_restrict_of_ae (μ := volume) (s := Icc N.t0 N.tf) ((hhs n).2.1 p)
    filter_upwards [h1, ae_restrict_mem measurableSet_Icc] with t ht htI
    exact (ht.1 htI)
  have hmem : ∀ n p, MemLp (hs n p) 2 μ := fun n p =>
    MemLp.of_bound ((hhs n).1 p).aestronglyMeasurable (N.B p) (by
      filter_upwards [hbd n p] with t ht
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [ht.1, ht.2])
  let u : ℕ → W → Lp ℝ 2 μ := fun n p => (hmem n p).toLp
  have hu : ∀ n p, (u n p : ℝ → ℝ) =ᵐ[μ] hs n p := fun n p => (hmem n p).coeFn_toLp
  -- norm bound
  obtain ⟨K, hK⟩ : ∃ K : W → ℝ, ∀ n p, ‖u n p‖ ≤ K p := by
    refine ⟨fun p => (measureUnivNNReal μ : ℝ) ^ ((2:ENNReal).toReal)⁻¹ * |N.B p|, ?_⟩
    intro n p
    refine Lp.norm_le_of_ae_bound (abs_nonneg _) ?_
    filter_upwards [hu n p, hbd n p] with t h1 h2
    rw [h1, Real.norm_eq_abs]
    exact abs_le_abs h2.2 (by linarith [h2.1, h2.2])
  let ψ : ℕ → StrongDual ℝ (W → Lp ℝ 2 μ) := fun n =>
    ∑ p, (innerSL ℝ (u n p)).comp (ContinuousLinearMap.proj p)
  have hψ : ∀ n G, ψ n G = ∑ p, inner ℝ (u n p) (G p) := by
    intro n G; simp [ψ]
  have hψnorm : ∀ n, ‖ψ n‖ ≤ ∑ p, K p := by
    intro n
    refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
    · exact Finset.sum_nonneg (fun p _ => (norm_nonneg _).trans (hK 0 p))
    · intro G
      rw [hψ, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
      refine (norm_inner_le_norm _ _).trans ?_
      exact mul_le_mul (hK n p) (norm_le_pi_norm G p) (norm_nonneg _)
        ((norm_nonneg _).trans (hK n p))
  obtain ⟨a, -, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℝ (W → Lp ℝ 2 μ) 0
    (∑ p, K p) (x := fun n => StrongDual.toWeakDual (ψ n)) (fun n => by
      simpa [mem_closedBall_zero_iff] using hψnorm n)
  have hev : ∀ G, Tendsto (fun n => ψ (φ n) G) atTop (𝓝 (a G)) := fun G =>
    ((WeakDual.eval_continuous G).tendsto a).comp hlim
  let v : W → Lp ℝ 2 μ := fun p => (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm
    ((WeakDual.toStrongDual a).comp (ContinuousLinearMap.single ℝ (fun _ : W => Lp ℝ 2 μ) p))
  have hv : ∀ p g, inner ℝ (v p) g = a (Pi.single p g) := by
    intro p g
    simp only [v, InnerProductSpace.toDual_symm_apply]
    rfl
  have hconv : ∀ p g, Tendsto (fun n => inner ℝ (u (φ n) p) g) atTop (𝓝 (inner ℝ (v p) g)) := by
    intro p g
    rw [hv]
    convert hev (Pi.single p g) using 1
    funext n
    rw [hψ]
    rw [Finset.sum_eq_single p]
    · simp
    · intro q _ hq; simp [Pi.single_apply, hq]
    · simp
  -- representative
  have hvm : ∀ p, AEStronglyMeasurable (v p : ℝ → ℝ) μ := fun p => Lp.aestronglyMeasurable _
  let hstar : W → ℝ → ℝ := fun p => (Icc N.t0 N.tf).indicator ((hvm p).mk _)
  have hstar_ae : ∀ p, hstar p =ᵐ[μ] (v p : ℝ → ℝ) := by
    intro p
    filter_upwards [ae_restrict_mem measurableSet_Icc, (hvm p).ae_eq_mk] with t ht h2
    simp [hstar, indicator_of_mem ht, h2]
  -- integrals as inner products
  have hint_u : ∀ n p (g : ℝ → ℝ) (hg : MemLp g 2 μ),
      ∫ t, g t * hs n p t ∂μ = inner ℝ (u n p) hg.toLp := by
    intro n p g hg
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hu n p, hg.coeFn_toLp] with t h1 h2
    rw [h1, h2]; simp [mul_comm]
  have hint_v : ∀ p (g : ℝ → ℝ) (hg : MemLp g 2 μ),
      ∫ t, g t * hstar p t ∂μ = inner ℝ (v p) hg.toLp := by
    intro p g hg
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hstar_ae p, hg.coeFn_toLp] with t h1 h2
    rw [h1, h2]; simp [mul_comm]
  have hlimInt : ∀ p (g : ℝ → ℝ), MemLp g 2 μ →
      Tendsto (fun n => ∫ t, g t * hs (φ n) p t ∂μ) atTop (𝓝 (∫ t, g t * hstar p t ∂μ)) := by
    intro p g hg
    simp_rw [hint_u _ p g hg, hint_v p g hg]
    exact hconv p _
  refine ⟨φ, hφ, hstar, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro p
    exact ((hvm p).stronglyMeasurable_mk.measurable).indicator measurableSet_Icc
  · intro p
    have hI : Integrable (hstar p) μ :=
      ((Lp.memLp (v p)).integrable one_le_two).congr (hstar_ae p).symm
    have hind : ∀ s, MeasurableSet s → ∀ f : ℝ → ℝ,
        ∫ t, s.indicator (fun _ => (1:ℝ)) t * f t ∂μ = ∫ t in s, f t ∂μ := by
      intro s hs f
      rw [← integral_indicator hs]
      congr 1; funext t
      by_cases ht : t ∈ s <;> simp [ht]
    have hgm : ∀ s, MeasurableSet s → MemLp (s.indicator (fun _ => (1:ℝ))) 2 μ := by
      intro s hs
      refine MemLp.of_bound ((measurable_const.indicator hs).aestronglyMeasurable) 1 ?_
      refine Eventually.of_forall fun t => ?_
      by_cases ht : t ∈ s <;> simp [ht]
    have hlo : (0 : ℝ → ℝ) ≤ᵐ[μ] hstar p := by
      refine ae_le_of_forall_setIntegral_le (integrable_zero _ _ _) hI fun s hsm _ => ?_
      rw [← hind s hsm, ← hind s hsm]
      simp only [Pi.zero_apply, mul_zero, integral_zero]
      refine ge_of_tendsto' (hlimInt p _ (hgm s hsm)) fun n => ?_
      refine integral_nonneg_of_ae ?_
      filter_upwards [hbd (φ n) p] with t ht
      exact mul_nonneg (by by_cases h : t ∈ s <;> simp [h]) ht.1
    have hhi : hstar p ≤ᵐ[μ] (fun _ => N.B p) := by
      refine ae_le_of_forall_setIntegral_le hI (integrable_const _) fun s hsm _ => ?_
      rw [← hind s hsm, ← hind s hsm]
      refine le_of_tendsto' (hlimInt p _ (hgm s hsm)) fun n => ?_
      have hI1 : Integrable (hs (φ n) p) μ := (hmem (φ n) p).integrable one_le_two
      rw [hind s hsm, hind s hsm]
      refine setIntegral_mono_ae hI1.integrableOn (integrable_const _).integrableOn ?_
      filter_upwards [hbd (φ n) p] with t ht
      exact ht.2
    have hb : ∀ᵐ t ∂μ, 0 ≤ hstar p t ∧ hstar p t ≤ N.B p := by
      filter_upwards [hlo, hhi] with t h1 h2
      exact ⟨h1, h2⟩
    rw [hμ, ae_restrict_iff' measurableSet_Icc] at hb
    filter_upwards [hb] with t ht
    refine ⟨ht, fun hn => ?_⟩
    simp [hstar, indicator_of_notMem hn]
  · intro i
    have hlim1 := tendsto_finsetSum (Finset.univ.filter (fun p => N.com p = i))
      (fun p _ => hlimInt p (fun _ => (1:ℝ)) (memLp_const 1))
    simp only [one_mul] at hlim1
    have hcst : (fun n => ∑ p ∈ Finset.univ.filter (fun p => N.com p = i),
        ∫ t, hs (φ n) p t ∂μ) = fun _ => N.Q i := by
      funext n; exact (hhs (φ n)).2.2 i
    rw [hcst] at hlim1
    exact (tendsto_nhds_unique tendsto_const_nhds hlim1).symm
  · intro g hg
    unfold pair
    exact tendsto_finsetSum _ (fun p _ => hlimInt p (g p) (hg p))

