-- Prove2me | solution 1 for StochIneqPO.Comparison.theorem1_tfae
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T17:48:14.950209+00:00
-- url     : https://prove2.me/submissions/e1ed301e-373c-4bc9-8735-1c9bd61972f9

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Definitions.Def_StochIneqPO_Comparison_IsUpward
import Theorems.Thm_StochIneqPO_Comparison_theorem1_vi_imp_ii

open MeasureTheory ProbabilityTheory StochIneqPO.Comparison

theorem solution {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    (P₁ P₂ : Measure E) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] :
    List.TFAE
      [ -- (i)
        StochLE P₁ P₂,
        -- (ii)
        ∃ lam : Measure (E × E), IsProbabilityMeasure lam ∧ lam {z : E × E | z.1 ≤ z.2}ᶜ = 0 ∧
          lam.map Prod.fst = P₁ ∧ lam.map Prod.snd = P₂,
        -- (iii)
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
          ∃ (Z : Ω → ℝ) (f g : ℝ → E), Measurable Z ∧ Measurable f ∧ Measurable g ∧
            (∀ t, f t ≤ g t) ∧ μ.map (fun ω => f (Z ω)) = P₁ ∧ μ.map (fun ω => g (Z ω)) = P₂,
        -- (iv)
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
          ∃ X₁ X₂ : Ω → E, Measurable X₁ ∧ Measurable X₂ ∧ (∀ᵐ ω ∂μ, X₁ ω ≤ X₂ ω) ∧
            μ.map X₁ = P₁ ∧ μ.map X₂ = P₂,
        -- (v)
        ∃ k : Kernel E E, IsMarkovKernel k ∧ IsUpward k ∧ P₂ = (P₁ ⊗ₘ k).snd,
        -- (vi)
        ∀ B : Set E, IsClosed B → IsUpperSet B → P₁ B ≤ P₂ B ] := by
  have hK : MeasurableSet {z : E × E | z.1 ≤ z.2} := measurableSet_le measurable_fst measurable_snd
  have hNe : Nonempty E := nonempty_of_isProbabilityMeasure P₁
  tfae_have 1 → 6 := by
    intro h B hB hBup
    have hBm := hB.measurableSet
    have hi := h (B.indicator (1 : E → ℝ)) (measurable_const.indicator hBm)
      (by
        intro x y hxy
        by_cases hx : x ∈ B
        · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (hBup hxy hx)]
        · rw [Set.indicator_of_notMem hx]
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) y)
      ⟨1, fun x => by
        by_cases hx : x ∈ B <;> simp [Set.indicator, hx]⟩
    rw [integral_indicator_one hBm, integral_indicator_one hBm] at hi
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hi
  tfae_have 6 → 2 := fun h => theorem1_vi_imp_ii P₁ P₂ h
  tfae_have 2 → 3 := by
    rintro ⟨lam, hlam, hsupp, h1, h2⟩
    obtain ⟨ψ, hψ⟩ := exists_measurableEmbedding_real (α := E × E)
    let e0 : E := Classical.arbitrary E
    classical
    let K : Set (E × E) := {z | z.1 ≤ z.2}
    let F : ℝ → E × E := fun t => if t ∈ ψ '' K then hψ.invFun t else (e0, e0)
    have hF : Measurable F :=
      Measurable.ite (hψ.measurableSet_image' hK) hψ.measurable_invFun measurable_const
    have hFψ : ∀ x ∈ K, F (ψ x) = x := fun x hx => by
      simp only [F, if_pos (Set.mem_image_of_mem ψ hx)]
      exact hψ.leftInverse_invFun x
    have hae : ∀ᵐ z ∂lam, z ∈ K := by rw [ae_iff]; exact hsupp
    have hμ : IsProbabilityMeasure (lam.map ψ) :=
      Measure.isProbabilityMeasure_map hψ.measurable.aemeasurable
    refine ⟨ℝ, inferInstance, lam.map ψ, hμ, id, fun t => (F t).1, fun t => (F t).2,
      measurable_id, measurable_fst.comp hF, measurable_snd.comp hF, ?_, ?_, ?_⟩
    · intro t
      by_cases ht : t ∈ ψ '' K
      · obtain ⟨x, hx, rfl⟩ := ht
        simp only [hFψ x hx]
        exact hx
      · have hF' : F t = (e0, e0) := by simp only [F, if_neg ht]
        simp only [hF', le_refl]
    · rw [show (fun ω => (fun t => (F t).1) (id ω)) = Prod.fst ∘ F from rfl,
        Measure.map_map (measurable_fst.comp hF) hψ.measurable, ← h1]
      apply Measure.map_congr
      filter_upwards [hae] with x hx
      simp [hFψ x hx]
    · rw [show (fun ω => (fun t => (F t).2) (id ω)) = Prod.snd ∘ F from rfl,
        Measure.map_map (measurable_snd.comp hF) hψ.measurable, ← h2]
      apply Measure.map_congr
      filter_upwards [hae] with x hx
      simp [hFψ x hx]
  tfae_have 3 → 4 := by
    rintro ⟨Ω, mΩ, μ, hμ, Z, f, g, hZ, hf, hg, hfg, h1, h2⟩
    exact ⟨Ω, mΩ, μ, hμ, fun ω => f (Z ω), fun ω => g (Z ω), hf.comp hZ, hg.comp hZ,
      ae_of_all _ (fun ω => hfg (Z ω)), h1, h2⟩
  tfae_have 4 → 1 := by
    rintro ⟨Ω, mΩ, μ, hμ, X₁, X₂, hX₁, hX₂, hle, h1, h2⟩ u hu humono ⟨C, hC⟩
    have hint : ∀ X : Ω → E, Measurable X → Integrable (fun ω => u (X ω)) μ := fun X hX =>
      Integrable.of_bound (hu.comp hX).aestronglyMeasurable C
        (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hC (X ω))
    rw [← h1, ← h2, integral_map hX₁.aemeasurable hu.aestronglyMeasurable,
      integral_map hX₂.aemeasurable hu.aestronglyMeasurable]
    apply integral_mono_ae (hint X₁ hX₁) (hint X₂ hX₂)
    filter_upwards [hle] with ω h
    exact humono h
  tfae_have 5 → 2 := by
    rintro ⟨k, hk, hup, h2⟩
    refine ⟨P₁ ⊗ₘ k, inferInstance, ?_, ?_, ?_⟩
    · rw [Measure.compProd_apply hK.compl]
      have h0 : ∀ x : E, k x (Prod.mk x ⁻¹' {z : E × E | z.1 ≤ z.2}ᶜ) = 0 := fun x => hup x
      exact (lintegral_congr h0).trans lintegral_zero
    · rw [← Measure.fst, Measure.fst_compProd]
    · rw [← Measure.snd, h2]
  tfae_have 2 → 5 := by
    rintro ⟨lam, hlam, hsupp, h1, h2⟩
    let κ0 := lam.condKernel
    have hdis : lam.fst ⊗ₘ κ0 = lam := lam.disintegrate κ0
    have hfst : lam.fst = P₁ := h1
    rw [hfst] at hdis
    have hmk : Measurable (fun x : E => κ0 x (Prod.mk x ⁻¹' {z : E × E | z.1 ≤ z.2}ᶜ)) :=
      Kernel.measurable_kernel_prodMk_left hK.compl
    let S : Set E := {x | κ0 x (Prod.mk x ⁻¹' {z : E × E | z.1 ≤ z.2}ᶜ) = 0}
    have hS : MeasurableSet S := hmk (measurableSet_singleton 0)
    let k : Kernel E E := Kernel.piecewise hS κ0 (Kernel.deterministic id measurable_id)
    have hkM : IsMarkovKernel k := by simp only [k]; infer_instance
    have hSae : ∀ᵐ x ∂P₁, x ∈ S := by
      have : lam {z : E × E | z.1 ≤ z.2}ᶜ =
          ∫⁻ x, κ0 x (Prod.mk x ⁻¹' {z : E × E | z.1 ≤ z.2}ᶜ) ∂P₁ := by
        conv_lhs => rw [← hdis]
        rw [Measure.compProd_apply hK.compl]
      rw [hsupp, eq_comm, lintegral_eq_zero_iff hmk] at this
      exact this
    refine ⟨k, hkM, ?_, ?_⟩
    · intro x
      by_cases hx : x ∈ S
      · simp only [k, Kernel.piecewise_apply, if_pos hx]
        exact hx
      · simp only [k, Kernel.piecewise_apply, if_neg hx, Kernel.deterministic_apply, id]
        show Measure.dirac x (Set.Ici x)ᶜ = 0
        rw [Measure.dirac_apply' _ (measurableSet_Ici).compl]
        simp
    · have hkeq : k =ᵐ[P₁] κ0 := by
        filter_upwards [hSae] with x hx
        simp only [k, Kernel.piecewise_apply, if_pos hx]
      rw [Measure.compProd_congr hkeq, hdis, ← h2]
      rfl
  tfae_finish
