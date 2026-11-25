-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.exists_localHomeomorph_of_isDegreeOff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:18.595872+00:00
-- url     : https://prove2.me/submissions/1ee98c11-04dc-4369-bef6-278a2744afa5

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeSheets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open FinHolAtlas Topology
noncomputable section
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {A : FinHolAtlas e X} {B : FinHolAtlas e Y}
    {h : Y → X} (hh : HoloMap B A h) {d : ℕ} {S : Set X} (hd : IsDegreeOff A B h d S) (y : Y)
    (hy : h y ∉ S) :
    ∃ E : OpenPartialHomeomorph Y X, y ∈ E.source ∧ Set.EqOn h E E.source ∧
      ∃ j : Fin B.n, E.source ⊆ (B.chart j).source := by
  obtain ⟨j, hyj⟩ := B.cover y
  obtain ⟨k, hk⟩ := A.cover (h y)
  have hb : (B.chart j) y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source) := by
    refine ⟨(B.chart j).map_source hyj, ?_⟩
    show h ((B.chart j).symm ((B.chart j) y)) ∈ (A.chart k).source
    rw [(B.chart j).left_inv hyj]
    exact hk
  have han := hh.2 j k ((B.chart j) y) hb
  have hdet := hd.2.2.2.2.2 j k ((B.chart j) y) ((B.chart j).map_source hyj)
    (by rw [(B.chart j).left_inv hyj]; exact hy) (by rw [(B.chart j).left_inv hyj]; exact hk)
  set L := (LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv with hL
  have hstrict : HasStrictFDerivAt ((A.chart k) ∘ h ∘ (B.chart j).symm)
      (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) ((B.chart j) y) :=
    han.hasStrictFDerivAt.congr_fderiv (by ext v; rfl)
  set Φ := hstrict.toOpenPartialHomeomorph ((A.chart k) ∘ h ∘ (B.chart j).symm) with hΦ
  have hcoe : (Φ : (Fin e → ℂ) → (Fin e → ℂ)) = (A.chart k) ∘ h ∘ (B.chart j).symm :=
    hstrict.toOpenPartialHomeomorph_coe
  have hsrc : (B.chart j) y ∈ Φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hU : IsOpen (h ⁻¹' (A.chart k).source) := (A.chart k).open_source.preimage hh.1
  refine ⟨(((B.chart j).trans Φ).trans (A.chart k).symm).restrOpen _ hU, ?_, ?_, j, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source]
    refine ⟨⟨⟨hyj, hsrc⟩, ?_⟩, hk⟩
    show Φ ((B.chart j) y) ∈ (A.chart k).target
    rw [hcoe]
    show (A.chart k) (h ((B.chart j).symm ((B.chart j) y))) ∈ (A.chart k).target
    rw [(B.chart j).left_inv hyj]
    exact (A.chart k).map_source hk
  · intro y' hy'
    rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hy'
    obtain ⟨⟨⟨hy1, -⟩, -⟩, hy4⟩ := hy'
    show h y' = (A.chart k).symm (Φ ((B.chart j) y'))
    rw [hcoe]
    show h y' = (A.chart k).symm ((A.chart k) (h ((B.chart j).symm ((B.chart j) y'))))
    rw [(B.chart j).left_inv hy1, (A.chart k).left_inv hy4]
  · intro y' hy'
    rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hy'
    exact hy'.1.1.1
end ReciprocityTheory.AnForm.M
