-- Prove2me | solution 1 for PI.VolStabW.restrProd_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:15:59.880501+00:00
-- url     : https://prove2.me/submissions/e63b39ce-5165-4bb0-bf2c-89acdd50a33e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_isClopen_latV
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_isSB_latV
import Theorems.Thm_PI_VolStabW_TopoMeas_measurable_adm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution (hA : RPAbs) (hF : RPFib) (hG : RPGlue) (hGr : RPGram) (hTl : RPTail)
    (hL : LatCofin) : RestrProd := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμi νinf hνi μv hμv νv hνv
    fibInf hfi fibV hfv hmult
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have cF := hF F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  obtain ⟨hsfI, hintI⟩ := cF.1 μinf νinf fibInf hfi
  have hFv := fun v => cF.2 v (μv v) (νv v) (fibV v) (hfv v)
  have hSB : ∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ →
      Integrable Φ (fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) :=
    fun v Φ h => (hFv v).2 Φ h.1.continuous h.2
  let b := Module.finBasis F E
  rcases hTl F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet fibV _ b hSB (hmult _ b) with
    ⟨v0, hv0⟩ | hconv
  · refine ⟨0, by simp, fun d' b' Φ Φinf Φf Φv _ _ hp _ => ⟨integrable_zero_measure, ?_⟩⟩
    have h0 : HasProd (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) 0 :=
      hasProd_zero_of_exists_eq_zero ⟨v0, hv0 _ (hp.1 v0)⟩
    rw [integral_zero_measure, h0.tprod_eq, mul_zero]
  · let W : HeightOneSpectrum (𝓞 F) → Type := fun v => Fin a → Fin M → Fv F v ⊗[F] E
    let m : ∀ v, Measure (W v) := fun v => fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)
    have : ∀ v, SigmaFinite (m v) := fun v => (hFv v).1
    have := hsfI
    have hLm : ∀ v, MeasurableSet (latV (M := M) (n := a) b v) := fun v =>
      (PositiveNearLattice.isClopen_latV b v a M).isOpen.measurableSet
    have hLf : ∀ v, m v (latV b v) ≠ ⊤ := fun v => by
      have h := hSB v _ (PositiveNearLattice.isSB_latV b v a M)
      rw [integrable_indicator_iff (hLm v)] at h
      exact (((integrableOn_const_iff (C := (1 : ℂ))).1 h).resolve_left (by simp)).ne
    obtain ⟨ρ, hρsf, hρgood, hρmarg, hρint⟩ :=
      hA (HeightOneSpectrum (𝓞 F)) W m (fun v => latV b v) hLm hLf hconv
    have := hρsf
    obtain ⟨Γ, hΓm, hΓ⟩ := hG F E M a _ b
    have cG := hGr F E σ M J a (gramE σ J X0)
    let P : Measure ((Fin a → Fin M → Ainf F ⊗[F] E) × ∀ v, W v) :=
      (fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)).prod ρ
    have hgood : P (Set.univ ×ˢ {x : ∀ v, W v | ¬ ∀ᶠ v in Filter.cofinite, x v ∈ latV b v}) = 0 := by
      rw [Measure.prod_prod, hρgood, mul_zero]
    refine ⟨P.map Γ, ?_, ?_⟩
    · rw [Measure.map_apply hΓm cG.1]
      have h1 : (fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))
          {y | gramR (Ainf F) σ J y = (gramE σ J X0).map (inclR (Ainf F))}ᶜ = 0 :=
        measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_left) (hfi.1 _)
      have h2 : ∀ v, m v {x | gramR (Fv F v) σ J x = (gramE σ J X0).map (inclR (Fv F v))}ᶜ = 0 :=
        fun v => measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_left) ((hfv v).1 _)
      have hbad : Γ ⁻¹' {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} ⊆
          ({y | gramR (Ainf F) σ J y = (gramE σ J X0).map (inclR (Ainf F))}ᶜ ×ˢ Set.univ) ∪
          ((Set.univ ×ˢ {x : ∀ v, W v | ¬ ∀ᶠ v in Filter.cofinite, x v ∈ latV b v}) ∪
            ⋃ v, Set.univ ×ˢ {x : ∀ v, W v | x v ∉
              {x | gramR (Fv F v) σ J x = (gramE σ J X0).map (inclR (Fv F v))}}) := by
        intro p hp
        by_contra hn
        have hi : gramR (Ainf F) σ J p.1 = (gramE σ J X0).map (inclR (Ainf F)) := by
          by_contra h; exact hn (Or.inl ⟨h, Set.mem_univ _⟩)
        have hg : ∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v := by
          by_contra h; exact hn (Or.inr (Or.inl ⟨Set.mem_univ _, h⟩))
        have hv : ∀ v, gramR (Fv F v) σ J (p.2 v) = (gramE σ J X0).map (inclR (Fv F v)) := by
          intro v; by_contra h
          exact hn (Or.inr (Or.inr (Set.mem_iUnion.2 ⟨v, Set.mem_univ _, h⟩)))
        obtain ⟨e1, e2⟩ := hΓ p hg
        apply hp
        apply cG.2.2.2 (Γ p)
        · rw [e1]; exact hi
        · intro v; rw [e2 v]; exact hv v
      refine measure_mono_null hbad (measure_union_null ?_ (measure_union_null hgood
        (measure_iUnion_null fun v => ?_)))
      · rw [Measure.prod_prod, h1, zero_mul]
      · rw [Measure.prod_prod, hρmarg v _ (cG.2.2.1 v) (h2 v), mul_zero]
    · intro d' b' Φ Φinf Φf Φv hc1 hc2 hp hpr
      have hΦm : Measurable Φ :=
        TopoMeas.measurable_adm Φ ⟨d', b', Φinf, Φf, Φv, hc1, hc2, hp, hpr⟩
      have hf : ∀ v, Integrable (Φv v) (m v) := fun v => hSB v _ (hp.1 v)
      have hfc : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1 :=
        (hp.2.1.and (hL F E a M d' _ b' b)).mono fun v h => h.1.trans (by rw [h.2])
      obtain ⟨hIρ, hHP⟩ := hρint Φv hf hfc
      have hae' : ∀ᵐ p ∂P, ∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v := by
        rw [ae_iff]
        exact measure_mono_null (fun p hp => Set.mem_prod.2 ⟨Set.mem_univ _, hp⟩) hgood
      have hae : (fun p => Φ (Γ p)) =ᵐ[P] fun p => Φinf p.1 * ∏ᶠ v, Φv v (p.2 v) := by
        filter_upwards [hae'] with p hp'
        obtain ⟨e1, e2⟩ := hΓ p hp'
        rw [hpr (Γ p), hp.2.2 (projFin (Γ p)), e1]
        congr 1
        exact finprod_congr fun v => by rw [e2 v]
      have hPI : Integrable (fun p : _ × (∀ v, W v) => Φinf p.1 * ∏ᶠ v, Φv v (p.2 v)) P :=
        (hintI Φinf hc1 hc2).mul_prod hIρ
      refine ⟨(integrable_map_measure hΦm.aestronglyMeasurable hΓm.aemeasurable).2
        (hPI.congr hae.symm), ?_⟩
      rw [integral_map hΓm.aemeasurable hΦm.aestronglyMeasurable, integral_congr_ae hae,
        integral_prod_mul (fun y => Φinf y) (fun x : ∀ v, W v => ∏ᶠ v, Φv v (x v)),
        ← hHP.tprod_eq]
end PI.VolStabW
