-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_maxRank_equations_f246dd7c3832
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:27:13.211511+00:00
-- url     : https://prove2.me/submissions/8e20a125-445f-4c6c-a2c6-6adc978d82b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularLocusDense

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
open Topology Filter Module
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) {U : Set (σ → ℂ)}
    (hU : IsOpen U) (hne : (Y ∩ U).Nonempty) :
    ∃ a ∈ Y, ∃ (ι : Type) (_ : Fintype ι) (h : ι → (σ → ℂ) → ℂ) (W : Set (σ → ℂ)),
      IsOpen W ∧ a ∈ W ∧ W ⊆ U ∧ (∀ j, ∀ z ∈ W, AnalyticAt ℂ (h j) z) ∧
      (∀ j, ∀ z ∈ W, z ∈ Y → h j z = 0) ∧ LinearIndependent ℂ (fun j => fderiv ℂ (h j) a) ∧
      ∀ z ∈ W ∩ Y, ∀ ψ : (σ → ℂ) → ℂ, AnalyticAt ℂ ψ z → (∀ᶠ u in 𝓝 z, u ∈ Y → ψ u = 0) →
        fderiv ℂ ψ z ∈ Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) z) := by
  classical
  set rk : (σ → ℂ) → ℕ := fun z => finrank ℂ (conormalSpan Y z) with hrk
  have hbdd : BddAbove (rk '' (Y ∩ U)) :=
    ⟨finrank ℂ ((σ → ℂ) →L[ℂ] ℂ), by rintro _ ⟨z, -, rfl⟩; exact Submodule.finrank_le _⟩
  obtain ⟨a, haYU, har⟩ := Nat.sSup_mem (hne.image rk) hbdd
  have hmax : ∀ z ∈ Y ∩ U, rk z ≤ rk a := fun z hz => har ▸ le_csSup hbdd ⟨z, hz, rfl⟩
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℂ
    {ℓ : (σ → ℂ) →L[ℂ] ℂ | ∃ h : (σ → ℂ) → ℂ, AnalyticAt ℂ h a ∧ (∀ᶠ u in 𝓝 a, u ∈ Y → h u = 0) ∧
      fderiv ℂ h a = ℓ}
  have : Finite b := hbli.finite
  let _ : Fintype b := Fintype.ofFinite b
  have hb' : ∀ ℓ : b, ∃ h : (σ → ℂ) → ℂ, AnalyticAt ℂ h a ∧ (∀ᶠ u in 𝓝 a, u ∈ Y → h u = 0) ∧
      fderiv ℂ h a = ℓ := fun ℓ => hbS ℓ.2
  choose h hha hhY hhd using hb'
  have hfun : (fun j : b => fderiv ℂ (h j) a) = ((↑) : b → (σ → ℂ) →L[ℂ] ℂ) := funext hhd
  have hli_a : LinearIndependent ℂ (fun j => fderiv ℂ (h j) a) := hfun ▸ hbli
  have hcard : rk a = Fintype.card b := by
    have hsp : conormalSpan Y a = Submodule.span ℂ (Set.range fun j : b => fderiv ℂ (h j) a) := by
      rw [hfun, Subtype.range_coe, hbspan]
      rfl
    show finrank ℂ (conormalSpan Y a) = _
    rw [hsp]
    exact finrank_span_eq_card hli_a
  have E3 : ∀ᶠ z in 𝓝 a, LinearIndependent ℂ (fun j => fderiv ℂ (h j) z) := by
    have ht : Tendsto (fun z => fun j => fderiv ℂ (h j) z) (𝓝 a) (𝓝 fun j => fderiv ℂ (h j) a) :=
      tendsto_pi_nhds.2 fun j => (hha j).fderiv.continuousAt.tendsto
    exact ht.eventually hli_a.eventually
  have E : ∀ᶠ z in 𝓝 a, z ∈ U ∧ (∀ j, AnalyticAt ℂ (h j) z) ∧ (∀ j, z ∈ Y → h j z = 0) ∧
      LinearIndependent ℂ (fun j => fderiv ℂ (h j) z) :=
    (show ∀ᶠ z in 𝓝 a, z ∈ U from hU.mem_nhds haYU.2).and ((eventually_all.2 fun j => (hha j).eventually_analyticAt).and
      ((eventually_all.2 hhY).and E3))
  obtain ⟨W, hWP, hWo, haW⟩ := eventually_nhds_iff.1 E
  refine ⟨a, haYU.1, b, inferInstance, h, W, hWo, haW, fun z hz => (hWP z hz).1,
    fun j z hz => (hWP z hz).2.1 j, fun j z hz => (hWP z hz).2.2.1 j, hli_a, ?_⟩
  rintro z ⟨hzW, hzY⟩ ψ hψ hψY
  obtain ⟨hzU, hza, -, hzli⟩ := hWP z hzW
  have hle : Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) z) ≤ conormalSpan Y z := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨h j, hza j, ?_, rfl⟩
    filter_upwards [hWo.mem_nhds hzW] with u hu huY using (hWP u hu).2.2.1 j huY
  have heq : Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) z) = conormalSpan Y z :=
    Submodule.eq_of_le_of_finrank_le hle
      (by rw [finrank_span_eq_card hzli, ← hcard]; exact hmax z ⟨hzY, hzU⟩)
  rw [heq]
  exact Submodule.subset_span ⟨ψ, hψ, hψY, rfl⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
