-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.degree_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:28:42.606733+00:00
-- url     : https://prove2.me/submissions/31120aad-745f-4873-8310-9c3f65ad9801

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeInt
import Theorems.Thm_ReciprocityTheory_AnForm_M_integralWith_localize_support
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_indicator
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_target_of_mIntegrable
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotentialPullback
import Theorems.Thm_ReciprocityTheory_AnForm_M_sheet_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution [CompactSpace Y] [T2Space Y] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h) {d : ℕ}
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (P : ChartPartition A)
    (Q : ChartPartition B) {E V : Set X} (hE : MeasurableSet E) (hEV : E ⊆ V) (hV : IsOpen V)
    {k : Fin A.n} (hVk : V ⊆ (A.chart k).source) {W : Fin d → Set Y} {j : Fin d → Fin B.n}
    (hW : ∀ i, IsOpen (W i)) (hdis : Pairwise (Function.onFun Disjoint W))
    (hpre : h ⁻¹' V = ⋃ i, W i) (hsh : ∀ i, Set.BijOn h (W i) V ∧ W i ⊆ (B.chart (j i)).source)
    (g : X → ℝ) (hg : MIntegrable A Φ g) :
    (∀ j', IntegrableOn (fun y => Q.χ j' ((B.chart j').symm y) *
        (E.indicator g (h ((B.chart j').symm y))) *
        locDens B (fun i => (Φ i).pullback h hh.1) j' y) (B.chart j').target) ∧
    integralWith B Q (fun i => (Φ i).pullback h hh.1) (fun y => E.indicator g (h y)) =
      d * integralWith A P Φ (E.indicator g) := by
  have hΨ : ∀ i, IsPotential B ((Φ i).pullback h hh.1) :=
    fun i => isPotentialPullback A B h hh (Φ i) (hΦ i)
  have hfX : IntegrableOn (fun z => E.indicator g ((A.chart k).symm z) * locDens A Φ k z)
      (A.chart k).target :=
    dI_indicator (A.chart k) hE g _ (dI_target_of_mIntegrable A Φ hΦ g hg k)
  have hf0 : ∀ x, x ∉ (A.chart k).source → E.indicator g x = 0 :=
    fun x hx => Set.indicator_of_notMem (fun h' => hx (hVk (hEV h'))) g
  have hIX := (integralWith_localize_support A P Φ hΦ k (E.indicator g) hf0 hfX).2
  have hsum : ∀ y, E.indicator g (h y) =
      ∑ i, (W i).indicator (fun y => E.indicator g (h y)) y := by
    intro y
    by_cases hy : h y ∈ E
    · have hyV : y ∈ h ⁻¹' V := hEV hy
      rw [hpre] at hyV
      obtain ⟨i0, hi0⟩ := Set.mem_iUnion.1 hyV
      rw [Finset.sum_eq_single i0 (fun i _ hi => Set.indicator_of_notMem
          (fun hiy => Set.disjoint_left.1 (show Disjoint (W i) (W i0) from hdis hi) hiy hi0) _)
        (fun h' => absurd (Finset.mem_univ i0) h'), Set.indicator_of_mem hi0]
    · rw [Set.indicator_of_notMem hy]
      exact (Finset.sum_eq_zero fun i _ => by simp [hy]).symm
  have hsheet : ∀ i, IntegrableOn (fun y => (W i).indicator (fun y => E.indicator g (h y))
        ((B.chart (j i)).symm y) * locDens B (fun i => (Φ i).pullback h hh.1) (j i) y)
        (B.chart (j i)).target ∧
      ∫ y in (B.chart (j i)).target, (W i).indicator (fun y => E.indicator g (h y))
        ((B.chart (j i)).symm y) * locDens B (fun i => (Φ i).pullback h hh.1) (j i) y =
        ∫ z in (A.chart k).target, E.indicator g ((A.chart k).symm z) * locDens A Φ k z := by
    intro i
    obtain ⟨hbij, hWj⟩ := hsh i
    have hSI := sheet_integral hh Φ hΦ (j i) k (hW i) hWj hVk hbij (E.indicator g)
    have hOim : IsOpen ((B.chart (j i)) '' W i) :=
      (B.chart (j i)).isOpen_image_of_subset_source (hW i) hWj
    have hVim : (A.chart k) '' V ⊆ (A.chart k).target := by
      rintro _ ⟨x, hx, rfl⟩; exact (A.chart k).map_source (hVk hx)
    have hWim : (B.chart (j i)) '' W i ⊆ (B.chart (j i)).target := by
      rintro _ ⟨w, hw, rfl⟩; exact (B.chart (j i)).map_source (hWj hw)
    have hint1 : IntegrableOn (fun y => E.indicator g (h ((B.chart (j i)).symm y)) *
        locDens B (fun i => (Φ i).pullback h hh.1) (j i) y) ((B.chart (j i)) '' W i) :=
      hSI.1.2 (hfX.mono_set hVim)
    have heqW : Set.EqOn (fun y => E.indicator g (h ((B.chart (j i)).symm y)) *
        locDens B (fun i => (Φ i).pullback h hh.1) (j i) y)
        (fun y => (W i).indicator (fun y => E.indicator g (h y)) ((B.chart (j i)).symm y) *
          locDens B (fun i => (Φ i).pullback h hh.1) (j i) y) ((B.chart (j i)) '' W i) := by
      rintro _ ⟨w, hw, rfl⟩
      simp only [(B.chart (j i)).left_inv (hWj hw), Set.indicator_of_mem hw]
    have hzeroW : ∀ y ∈ (B.chart (j i)).target \ (B.chart (j i)) '' W i,
        (W i).indicator (fun y => E.indicator g (h y)) ((B.chart (j i)).symm y) *
          locDens B (fun i => (Φ i).pullback h hh.1) (j i) y = 0 := by
      rintro y ⟨hy, hyW⟩
      have : (B.chart (j i)).symm y ∉ W i := fun h' => hyW ⟨_, h', (B.chart (j i)).right_inv hy⟩
      simp [Set.indicator_of_notMem this]
    have hzeroV : ∀ z ∈ (A.chart k).target \ (A.chart k) '' V,
        E.indicator g ((A.chart k).symm z) * locDens A Φ k z = 0 := by
      rintro z ⟨hz, hzV⟩
      have : (A.chart k).symm z ∉ E := fun h' => hzV ⟨_, hEV h', (A.chart k).right_inv hz⟩
      simp [Set.indicator_of_notMem this]
    refine ⟨(hint1.congr_fun heqW hOim.measurableSet).of_forall_sdiff_eq_zero
      (B.chart (j i)).open_target.measurableSet hzeroW, ?_⟩
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (B.chart (j i)).open_target.measurableSet
        hWim hzeroW, ← setIntegral_congr_fun hOim.measurableSet heqW, hSI.2,
      ← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (A.chart k).open_target.measurableSet
        hVim hzeroV]
  have hloc := fun i => integralWith_localize_support B Q (fun i => (Φ i).pullback h hh.1) hΨ
    (j i) ((W i).indicator (fun y => E.indicator g (h y)))
    (fun y hy => Set.indicator_of_notMem (fun h' => hy ((hsh i).2 h')) _) (hsheet i).1
  have hpt : ∀ j' y, Q.χ j' ((B.chart j').symm y) * E.indicator g (h ((B.chart j').symm y)) *
      locDens B (fun i => (Φ i).pullback h hh.1) j' y =
      ∑ i, Q.χ j' ((B.chart j').symm y) *
        (W i).indicator (fun y => E.indicator g (h y)) ((B.chart j').symm y) *
        locDens B (fun i => (Φ i).pullback h hh.1) j' y := by
    intro j' y
    rw [hsum, Finset.mul_sum, Finset.sum_mul]
  refine ⟨fun j' => ?_, ?_⟩
  · have := integrable_finsetSum Finset.univ
      (f := fun i y => Q.χ j' ((B.chart j').symm y) *
        (W i).indicator (fun y => E.indicator g (h y)) ((B.chart j').symm y) *
        locDens B (fun i => (Φ i).pullback h hh.1) j' y) (fun i _ => (hloc i).1 j')
    exact IntegrableOn.congr_fun this (fun y _ => (hpt j' y).symm) (B.chart j').open_target.measurableSet
  · have h1 : integralWith B Q (fun i => (Φ i).pullback h hh.1) (fun y => E.indicator g (h y)) =
        ∑ i, integralWith B Q (fun i => (Φ i).pullback h hh.1)
          ((W i).indicator (fun y => E.indicator g (h y))) := by
      unfold integralWith
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      rw [← integral_finsetSum _ (fun i _ => (hloc i).1 j')]
      exact setIntegral_congr_fun (B.chart j').open_target.measurableSet (fun y _ => hpt j' y)
    rw [h1, Finset.sum_congr rfl (fun i _ => (hloc i).2.trans (hsheet i).2), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hIX]
end ReciprocityTheory.AnForm.M
