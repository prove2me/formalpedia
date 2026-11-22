-- Prove2me | solution 1 for PettisIntegral.pettisIntegrable_of_reflexive
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:07:51.787397+00:00
-- url     : https://prove2.me/submissions/dfe666ac-c7d0-4ec3-ab9a-fc56feb181f1

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

open PettisIntegral

theorem solution {𝕜 B X : Type*} [RCLike 𝕜] [NormedAddCommGroup B]
    [NormedSpace 𝕜 B] [CompleteSpace B]
    (hB : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 B))
    [MeasurableSpace X] (μ : Measure X) (f : X → B) (hf : WeaklyIntegrable 𝕜 μ f) :
    PettisIntegrable 𝕜 μ f := by
  classical
  -- The map `φ ↦ [φ ∘ f]` from the dual of `B` to `L¹(μ)`.
  let T : StrongDual 𝕜 B →ₗ[𝕜] Lp 𝕜 1 μ :=
    { toFun := fun φ => (hf φ).toL1 _
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hrep : ∀ φ : StrongDual 𝕜 B, ⇑(T φ) =ᵐ[μ] fun x => φ (f x) :=
    fun φ => (hf φ).coeFn_toL1
  -- `T` has a sequentially closed graph, hence is continuous (closed graph theorem).
  have hT : Continuous T := by
    apply T.continuous_of_seq_closed_graph
    intro u φ y hu hy
    apply Lp.ext
    -- convergence in `L¹` gives a subsequence converging almost everywhere
    obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hy).exists_seq_tendsto_ae
    have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, T (u n) x = u n (f x) :=
      ae_all_iff.mpr fun n => hrep (u n)
    filter_upwards [hns, hall, hrep φ] with x hx hx' hφ
    -- pointwise convergence `u n (f x) → φ (f x)`
    have hpt : Filter.Tendsto (fun n => u n (f x)) Filter.atTop (nhds (φ (f x))) :=
      ((NormedSpace.inclusionInDoubleDual 𝕜 B (f x)).continuous.tendsto φ).comp hu
    have hsub : Filter.Tendsto (fun i => u (ns i) (f x)) Filter.atTop (nhds (y x)) := by
      refine hx.congr fun i => ?_
      exact hx' (ns i)
    have hpt' : Filter.Tendsto (fun i => u (ns i) (f x)) Filter.atTop (nhds (φ (f x))) :=
      hpt.comp hmono.tendsto_atTop
    rw [hφ]
    exact tendsto_nhds_unique hsub hpt'
  -- The weak integral `φ ↦ ∫ φ (f x) ∂μ` is a continuous linear form on the dual.
  let L : StrongDual 𝕜 (StrongDual 𝕜 B) :=
    (L1.integralCLM' (μ := μ) (E := 𝕜) 𝕜).comp ⟨T, hT⟩
  have hL : ∀ φ : StrongDual 𝕜 B, L φ = ∫ x, φ (f x) ∂μ := by
    intro φ
    change L1.integralCLM' (μ := μ) (E := 𝕜) 𝕜 ((hf φ).toL1 _) = _
    rw [← L1.integral_eq' 𝕜, L1.integral_eq_integral]
    exact integral_congr_ae (hrep φ)
  obtain ⟨b, hb⟩ := hB L
  refine ⟨b, hf, fun φ => ?_⟩
  rw [← hL φ, ← hb]
  rfl
