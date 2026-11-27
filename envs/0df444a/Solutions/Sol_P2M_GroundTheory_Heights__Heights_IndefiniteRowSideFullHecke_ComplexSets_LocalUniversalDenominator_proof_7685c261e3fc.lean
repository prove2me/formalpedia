-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_LocalUniversalDenominator_proof_7685c261e3fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:58:26.586533+00:00
-- url     : https://prove2.me/submissions/389ed9f2-dc0c-4ebd-9244-7ae35e70655c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalUniversalDenominator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRootSumHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVanishNearPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalUniversalDenominator
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_LocalUniversalDenominator_fin_case_08eab7a6b602

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
open MvPolynomial Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace LocalUniversalDenominator
theorem _root_.solution
    (hcl : GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionCluster.Statement)
    (hrs : GroundTheory.Heights₂.Heights.ComplexSets.RootSumHolomorphic.Statement) :
    LocalUniversalDenominator.Statement := by
  intro σ _ I h w U f hI hh hw hU hf hb
  classical
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let ρ : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial (Fin (Fintype.card σ)) ℂ := MvPolynomial.renameEquiv ℂ e
  let T : (σ → ℂ) → (Fin (Fintype.card σ) → ℂ) := fun z => z ∘ e.symm
  let Ti : (Fin (Fintype.card σ) → ℂ) → (σ → ℂ) := fun x => x ∘ e
  have hTiT : ∀ z, Ti (T z) = z := fun z => funext fun i => by simp [T, Ti]
  have hev : ∀ (x : Fin (Fintype.card σ) → ℂ) (q : MvPolynomial σ ℂ), eval x (ρ q) = eval (Ti x) q :=
    fun x q => by
      show eval x (rename e q) = eval (x ∘ e) q
      exact MvPolynomial.eval_rename _ _ _
  have hev' : ∀ (z : σ → ℂ) (q' : MvPolynomial (Fin (Fintype.card σ)) ℂ),
      eval z (ρ.symm q') = eval (T z) q' := fun z q' => by
    have h1 := hev (T z) (ρ.symm q')
    rw [AlgEquiv.apply_symm_apply, hTiT] at h1
    exact h1.symm
  have hTic : Continuous Ti := continuous_pi fun i => continuous_apply (e i)
  have hTc : Continuous T := continuous_pi fun i => continuous_apply (e.symm i)
  have hTid : Differentiable ℂ Ti := differentiable_pi.2 fun i => differentiable_apply (e i)
  have hTd : Differentiable ℂ T := differentiable_pi.2 fun i => differentiable_apply (e.symm i)
  set I' : Ideal (MvPolynomial (Fin (Fintype.card σ)) ℂ) := I.comap ρ.symm with hI'def
  have hI' : I'.IsPrime := by
    have := hI
    exact Ideal.comap_isPrime _ _
  have hZ : ∀ x, x ∈ zeroSetIn I' ↔ Ti x ∈ zeroSetIn I := by
    intro x
    constructor
    · intro hx q hq
      rw [← hev]
      exact hx _ (by rw [hI'def, Ideal.mem_comap, AlgEquiv.symm_apply_apply]; exact hq)
    · intro hx q' hq'
      rw [hI'def, Ideal.mem_comap] at hq'
      have h1 := hx _ hq'
      rwa [← hev, AlgEquiv.apply_symm_apply] at h1
  have hS : ∀ x, x ∈ (zeroSetIn I' ∩ Ti ⁻¹' U) \ {x | eval x (ρ h) = 0} →
      Ti x ∈ (zeroSetIn I ∩ U) \ {z | eval z h = 0} := fun x hx =>
    ⟨⟨(hZ x).1 hx.1.1, hx.1.2⟩, fun h0 => hx.2 (by
      show eval x (ρ h) = 0
      rw [hev]
      exact h0)⟩
  have hf' : HolomorphicOnSubset (f ∘ Ti) ((zeroSetIn I' ∩ Ti ⁻¹' U) \ {x | eval x (ρ h) = 0}) := by
    intro x hx
    obtain ⟨O, hO, hxO, F, hF, hfF⟩ := hf (Ti x) (hS x hx)
    exact ⟨Ti ⁻¹' O, hO.preimage hTic, hxO, F ∘ Ti, hF.comp hTid.differentiableOn fun y hy => hy,
      fun y hy => hfF ⟨hS y hy.1, hy.2⟩⟩
  have hb' : Bornology.IsBounded ((f ∘ Ti) '' ((zeroSetIn I' ∩ Ti ⁻¹' U) \ {x | eval x (ρ h) = 0})) :=
    hb.subset (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨Ti x, hS x hx, rfl⟩)
  have hh' : ρ h ∉ I' := fun hm => hh (by
    rw [hI'def, Ideal.mem_comap, AlgEquiv.symm_apply_apply] at hm
    exact hm)
  have hw' : T w ∈ zeroSetIn I' := (hZ _).2 (by rw [hTiT]; exact hw)
  have hU' : Ti ⁻¹' U ∈ 𝓝 (T w) := hTic.continuousAt.preimage_mem_nhds (by rw [hTiT]; exact hU)
  obtain ⟨g', hg', N', hN'o, hwN', hN'U, F', hF', hid⟩ :=
    LocalUniversalDenominator.fin_case hcl hrs (Fintype.card σ) I' (ρ h) (T w) (Ti ⁻¹' U) (f ∘ Ti)
      hI' hh' hw' hU' hf' hb'
  refine ⟨ρ.symm g', fun hm => hg' (by rw [hI'def, Ideal.mem_comap]; exact hm), T ⁻¹' N',
    hN'o.preimage hTc, hwN', fun z hz => ?_, F' ∘ T, hF'.comp hTd.differentiableOn fun z hz => hz, ?_⟩
  · have h1 : Ti (T z) ∈ U := hN'U hz
    rwa [hTiT] at h1
  · rintro z ⟨⟨hzI, hzN⟩, hzh⟩
    have h1 := hid (T z) ⟨⟨(hZ _).2 (by rw [hTiT]; exact hzI), hzN⟩, fun h0 => hzh (by
      have h2 : eval (T z) (ρ h) = 0 := h0
      rw [hev, hTiT] at h2
      exact h2)⟩
    rw [hev']
    simpa only [Function.comp_apply, hTiT] using h1
end LocalUniversalDenominator
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
