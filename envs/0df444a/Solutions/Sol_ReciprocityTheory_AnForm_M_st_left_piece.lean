-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_left_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:33:50.16745+00:00
-- url     : https://prove2.me/submissions/13a4234a-3c33-48b1-8c8c-256569718d85

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_mInt_eq_piece
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_locDens_piece
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
private lemma continuous_of_atlas_smooth' (A : FinHolAtlas e X) {f : X → ℝ} (hf : A.Smooth f) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨k, hk⟩ := A.cover x
  have hs : (A.chart k).target ∩ (A.chart k).symm ⁻¹' univ ∈ 𝓝 ((A.chart k) x) := by
    rw [preimage_univ, inter_univ]
    exact (A.chart k).open_target.mem_nhds ((A.chart k).map_source hk)
  have h1 : ContinuousAt (f ∘ (A.chart k).symm) ((A.chart k) x) :=
    (hf k).continuousOn.continuousAt hs
  have h2 : ContinuousAt ((f ∘ (A.chart k).symm) ∘ (A.chart k)) x :=
    ContinuousAt.comp (f := A.chart k) h1 ((A.chart k).continuousAt hk)
  refine h2.congr ?_
  filter_upwards [(A.chart k).open_source.mem_nhds hk] with z hz
  simp [(A.chart k).left_inv hz]
section Piece
variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))
end Piece
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))
include hΦ hGo hG hGU
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (w ψ : X → ℝ) (hw : A.Smooth w) (hψ : A.Smooth ψ) (hψG : tsupport ψ ⊆ G) :
    mInt A (Fin.cons (LocPot.ofFun w) Φ) ψ =
      ∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
        (A.chart j).target.indicator (ψ ∘ (A.chart j).symm) y *
          maDens (Fin.cons (w ∘ (A.chart j).symm)
            fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) y := by
  have hP0 : IsPotential A (LocPot.ofFun w) := by
    unfold IsPotential
    refine ⟨fun _ => hw, fun x x' z _ => ⟨univ, isOpen_univ, mem_univ _, fun _ => 0, ?_, ?_⟩⟩
    · intro k z' _
      exact analyticAt_const
    · intro z' _
      simp [LocPot.ofFun]
  have hΨ : ∀ i, IsPotential A ((Fin.cons (LocPot.ofFun w) Φ : Fin (e + 1) → LocPot X) i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa only [Fin.cons_zero] using hP0
    · simpa only [Fin.cons_succ] using hΦ i
  rw [st_mInt_eq_piece A _ hΨ j G hG ψ (continuous_of_atlas_smooth' A hψ) hψG]
  have hSm : MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) :=
    ((A.chart j).isOpen_inter_preimage_symm hGo).measurableSet
  refine setIntegral_congr_fun hSm ?_
  intro y hy
  have h1 := st_locDens_piece A Φ hΦ j G hG x0 hGU w hw hy
  have h2 : (A.chart j).target.indicator (ψ ∘ (A.chart j).symm) y = ψ ((A.chart j).symm y) :=
    Set.indicator_of_mem hy.1 _
  simp only [h1, h2]
end ReciprocityTheory.AnForm.M
