-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum.unf_lint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:48.758488+00:00
-- url     : https://prove2.me/submissions/db09834b-d7f7-4f74-a695-169de410e6fb

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_IsFirstChernFamily
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_MeasurableSh
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_UnfoldingIntegralSum_measurable_sh
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_latHaar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.deprecated false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Act PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum
variable {V A : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
  [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
namespace PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum
theorem _root_.solution {Γ : AddSubgroup V} {Δ : AddSubgroup A} [Countable Γ] [Countable Δ]
    {ν : Measure V} [ν.IsAddHaarMeasure] {lam : Measure A} [lam.IsAddHaarMeasure]
    {𝓤 : Set V} (hU : IsAddFundamentalDomain Γ 𝓤 ν) (hU1 : ν 𝓤 = 1)
    (hUU : IsAddFundamentalDomain (Γ.prod Γ) (𝓤 ×ˢ 𝓤) (ν.prod ν))
    {𝓐 : Set A} (hA : IsAddFundamentalDomain Δ 𝓐 lam)
    (Λ : (V × V) ≃ₜ+ (V × V)) (hΛ : ∀ w, w ∈ Γ.prod Γ ↔ Λ w ∈ Γ.prod Γ)
    {Q : V × V → A} (hQ : Measurable Q) {Z : V → V → A} (hZ : Measurable (Function.uncurry Z))
    {ψ : V × A → ℝ≥0∞} (hψ : Measurable ψ) :
    ∫⁻ p, ∑' c : Γ × Δ, ψ (sh Λ Q Z ((c.1 : V), (c.2 : A)) p)
        ∂((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod (lam.restrict 𝓐))) =
      ∫⁻ c, ψ c ∂(ν.prod lam) := by
  classical
  have hsh : ∀ c : V × A, Measurable (sh Λ Q Z c) := fun c => measurable_sh hQ hZ c
  have hFm : Measurable fun x : V => ∫⁻ s, ψ (x, s) ∂lam := hψ.lintegral_prod_right'
  have hfib : ∀ u b : V,
      ∫⁻ a in 𝓐, ∑' c : Γ × Δ, ψ (sh Λ Q Z ((c.1 : V), (c.2 : A)) (u, (b, a))) ∂lam =
        ∑' r : Γ, ∫⁻ s, ψ ((r : V) + (Λ (b, u)).2, s) ∂lam := by
    intro u b
    rw [lintegral_tsum (f := fun (c : Γ × Δ) (a : A) => ψ (sh Λ Q Z ((c.1 : V), (c.2 : A)) (u, (b, a))))
      fun c => (hψ.comp ((hsh _).comp
      (measurable_prodMk_left.comp measurable_prodMk_left))).aemeasurable, ENNReal.tsum_prod']
    refine tsum_congr fun r => ?_
    calc _ = ∑' t : Δ, ∫⁻ a in 𝓐, (fun s => ψ ((r : V) + (Λ (b, u)).2,
            s + (Q (b, u) + Z r (Λ (b, u)).1))) (t +ᵥ a) ∂lam := by
          refine tsum_congr fun t => ?_
          refine lintegral_congr fun a => ?_
          simp only [sh, AddSubgroup.vadd_def, vadd_eq_add, add_assoc]
      _ = ∫⁻ s, ψ ((r : V) + (Λ (b, u)).2, s + (Q (b, u) + Z r (Λ (b, u)).1)) ∂lam :=
          (hA.lintegral_eq_tsum'' (fun s => ψ ((r : V) + (Λ (b, u)).2,
            s + (Q (b, u) + Z r (Λ (b, u)).1)))).symm
      _ = _ := lintegral_add_right_eq_self (fun s => ψ ((r : V) + (Λ (b, u)).2, s)) _
  set H : V × V → ℝ≥0∞ := fun w => ∑' r : Γ, ∫⁻ s, ψ ((r : V) + w.2, s) ∂lam with hH
  have hHm : Measurable H := Measurable.ennreal_tsum fun r => hFm.comp (measurable_snd.const_add _)
  have hHinv : ∀ (g : Γ.prod Γ) (x : V × V), H (g +ᵥ x) = H x := by
    intro g x
    have hg2 : (g : V × V).2 ∈ Γ := (AddSubgroup.mem_prod.1 g.2).2
    calc H (g +ᵥ x) = ∑' r : Γ, (fun r : Γ => ∫⁻ s, ψ ((r : V) + x.2, s) ∂lam)
          (Equiv.addRight (⟨_, hg2⟩ : Γ) r) := by
          simp only [hH, AddSubgroup.vadd_def, vadd_eq_add, Prod.snd_add]
          refine tsum_congr fun r => ?_
          simp [add_assoc]
      _ = H x := Equiv.tsum_eq (Equiv.addRight (⟨_, hg2⟩ : Γ))
          (fun r : Γ => ∫⁻ s, ψ ((r : V) + x.2, s) ∂lam)
  have hμ : (ν.prod ν) (𝓤 ×ˢ 𝓤) = 1 := by rw [Measure.prod_prod, hU1, one_mul]
  haveI : Countable (Γ.prod Γ) := Countable.of_equiv (Γ × Γ) (AddSubgroup.prodEquiv Γ Γ).toEquiv.symm
  have hsymm : MeasurePreserving Λ.symm (ν.prod ν) (ν.prod ν) :=
    ⟨Λ.symm.continuous.measurable, latHaar (V × V) (ν.prod ν) (Γ.prod Γ) Λ.symm
      (fun x => by simpa using hΛ (Λ.symm x)) (𝓤 ×ˢ 𝓤) hUU (by rw [hμ]; exact one_ne_zero)
      (by rw [hμ]; exact ENNReal.one_ne_top)⟩
  have hT : IsAddFundamentalDomain (Γ.prod Γ) (Λ.symm ⁻¹' (𝓤 ×ˢ 𝓤)) (ν.prod ν) := by
    refine hUU.preimage_of_equiv hsymm.quasiMeasurePreserving
      (e := fun g => ⟨Λ g, (hΛ g).1 g.2⟩) ⟨?_, ?_⟩ ?_
    · intro g h hgh
      exact Subtype.ext (Λ.injective (congrArg Subtype.val hgh))
    · intro h
      exact ⟨⟨Λ.symm h, (hΛ _).2 (by simp [h.2])⟩, Subtype.ext (by simp)⟩
    · intro g x
      simp [AddSubgroup.vadd_def, vadd_eq_add, map_add]
  have hM : Measurable fun p : V × (V × A) =>
      ∑' c : Γ × Δ, ψ (sh Λ Q Z ((c.1 : V), (c.2 : A)) p) :=
    Measurable.ennreal_tsum fun c => hψ.comp (hsh _)
  calc ∫⁻ p, ∑' c : Γ × Δ, ψ (sh Λ Q Z ((c.1 : V), (c.2 : A)) p)
        ∂((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod (lam.restrict 𝓐)))
      = ∫⁻ u in 𝓤, ∫⁻ b in 𝓤, H (Λ (b, u)) ∂ν ∂ν := by
        rw [lintegral_prod _ hM.aemeasurable]
        refine lintegral_congr fun u => ?_
        refine (lintegral_prod (fun q : V × A => ∑' c : Γ × Δ,
          ψ (sh Λ Q Z ((c.1 : V), (c.2 : A)) (u, q))) (hM.comp measurable_prodMk_left).aemeasurable).trans ?_
        exact lintegral_congr fun b => hfib u b
    _ = ∫⁻ w in 𝓤 ×ˢ 𝓤, H (Λ w) ∂(ν.prod ν) := by
        rw [← Measure.prod_restrict]
        exact (lintegral_prod_symm (fun w => H (Λ w)) (hHm.comp Λ.continuous.measurable).aemeasurable).symm
    _ = ∫⁻ w in Λ.symm ⁻¹' (𝓤 ×ˢ 𝓤), H w ∂(ν.prod ν) := by
        have := hsymm.setLIntegral_comp_preimage_emb Λ.symm.toHomeomorph.measurableEmbedding
          (fun w => H (Λ w)) (𝓤 ×ˢ 𝓤)
        rw [← this]
        simp only [ContinuousAddEquiv.apply_symm_apply]
    _ = ∫⁻ w in 𝓤 ×ˢ 𝓤, H w ∂(ν.prod ν) := hT.setLIntegral_eq hUU H hHinv
    _ = ∫⁻ b in 𝓤, ∫⁻ v in 𝓤, ∑' r : Γ, ∫⁻ s, ψ ((r : V) + v, s) ∂lam ∂ν ∂ν := by
        rw [← Measure.prod_restrict]
        exact lintegral_prod _ hHm.aemeasurable
    _ = ∫⁻ v in 𝓤, ∑' r : Γ, ∫⁻ s, ψ ((r : V) + v, s) ∂lam ∂ν := by
        rw [lintegral_const, Measure.restrict_apply_univ, hU1, mul_one]
    _ = ∫⁻ v, ∫⁻ s, ψ (v, s) ∂lam ∂ν := by
        rw [hU.lintegral_eq_tsum'' (fun v => ∫⁻ s, ψ (v, s) ∂lam)]
        exact lintegral_tsum fun r => (hFm.comp (measurable_const_add (r : V))).aemeasurable
    _ = ∫⁻ c, ψ c ∂(ν.prod lam) := (lintegral_prod _ hψ.aemeasurable).symm
end PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum
