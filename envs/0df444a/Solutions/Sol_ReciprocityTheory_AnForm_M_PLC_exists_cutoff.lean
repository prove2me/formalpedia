-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.exists_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:30.703099+00:00
-- url     : https://prove2.me/submissions/9b783982-768b-4470-a388-c0d3d51478cf

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AtlasIndep
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA

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
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.PLC
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLC
theorem _root_.solution [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (K : Set X)
    (hK : IsClosed K) (hKψ : K ⊆ ψ.source) :
    ∃ ρ : X → ℝ, A.Smooth ρ ∧ tsupport ρ ⊆ ψ.source ∧ ∀ z ∈ K, ρ z = 1 := by
  classical

  have hKc : IsCompact K := hK.isCompact
  have hK'c : IsCompact (ψ '' K) := hKc.image_of_continuousOn (ψ.continuousOn.mono hKψ)
  have hK'U : ψ '' K ⊆ ψ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact ψ.map_source (hKψ hz)
  have hb : ∀ x ∈ ψ.target, ∃ f : (Fin e → ℂ) → ℝ, tsupport f ⊆ ψ.target ∧ HasCompactSupport f ∧
      ContDiff ℝ ∞ f ∧ Set.range f ⊆ Set.Icc 0 1 ∧ f x = 1 :=
    fun x hx => exists_contDiff_tsupport_subset (n := ⊤) (ψ.open_target.mem_nhds hx)
  choose! F hFs hFc hFd hFr hF1 using hb
  obtain ⟨t, ht⟩ := hK'c.elim_finite_subcover (fun i : ψ '' K => {y | 1 / 2 < F i y})
    (fun i => isOpen_lt continuous_const (hFd i (hK'U i.2)).continuous)
    (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, by
      show (1 : ℝ) / 2 < F y y
      rw [hF1 y (hK'U hy)]
      norm_num⟩)

  have hgd : ContDiff ℝ ∞ (fun y => ∑ i ∈ t, F i y) :=
    contDiffOn_univ.mp (ContDiffOn.sum (fun i _ => (hFd i (hK'U i.2)).contDiffOn))
  have hgK : ∀ y ∈ ψ '' K, 1 / 2 ≤ ∑ i ∈ t, F i y := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (ht hy)
    exact le_trans (le_of_lt hyi) (Finset.single_le_sum (f := fun j : ψ '' K => F j y)
      (fun j _ => (hFr j (hK'U j.2) (Set.mem_range_self y)).1) hi)
  have hTc : IsCompact (⋃ i ∈ t, tsupport (F i)) := t.isCompact_biUnion (fun i _ => hFc i (hK'U i.2))
  have hTU : (⋃ i ∈ t, tsupport (F i)) ⊆ ψ.target := Set.iUnion₂_subset (fun i _ => hFs i (hK'U i.2))
  have hrd : ContDiff ℝ ∞ (fun y => Real.smoothTransition (2 * ∑ i ∈ t, F i y)) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul hgd)
  have hrT : ∀ y, Real.smoothTransition (2 * ∑ i ∈ t, F i y) ≠ 0 → y ∈ ⋃ i ∈ t, tsupport (F i) := by
    intro y hy
    by_contra hyT
    apply hy
    apply Real.smoothTransition.zero_of_nonpos
    have h0 : ∑ i ∈ t, F i y = 0 := Finset.sum_eq_zero (fun i hi => by
      by_contra hne
      exact hyT (Set.mem_iUnion₂.mpr ⟨i, hi, subset_tsupport _ hne⟩))
    rw [h0]
    norm_num

  have hLc : IsCompact (ψ.symm '' ⋃ i ∈ t, tsupport (F i)) :=
    hTc.image_of_continuousOn (ψ.continuousOn_symm.mono hTU)
  have hLs : ψ.symm '' (⋃ i ∈ t, tsupport (F i)) ⊆ ψ.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact ψ.map_target (hTU hy)
  have hsupp : Function.support (fun x => if x ∈ ψ.source then
      Real.smoothTransition (2 * ∑ i ∈ t, F i (ψ x)) else 0) ⊆ ψ.symm '' ⋃ i ∈ t, tsupport (F i) := by
    intro x hx
    by_cases hxs : x ∈ ψ.source
    · have hr : Real.smoothTransition (2 * ∑ i ∈ t, F i (ψ x)) ≠ 0 := by simpa [hxs] using hx
      exact ⟨ψ x, hrT _ hr, ψ.left_inv hxs⟩
    · exact absurd (show (if x ∈ ψ.source then
        Real.smoothTransition (2 * ∑ i ∈ t, F i (ψ x)) else 0) = 0 by simp [hxs]) hx
  refine ⟨fun x => if x ∈ ψ.source then Real.smoothTransition (2 * ∑ i ∈ t, F i (ψ x)) else 0,
    ?_, (closure_minimal hsupp hLc.isClosed).trans hLs, ?_⟩
  · intro j
    refine contDiffOn_of_locally_contDiffOn (fun y hy => ?_)
    have hyt : y ∈ (A.chart j).target := hy.1
    by_cases hp : (A.chart j).symm y ∈ ψ.source
    · have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) :=
        (A.chart j).isOpen_inter_preimage_symm ψ.open_source
      refine ⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source, hopen, ⟨hyt, hp⟩, ?_⟩
      have han : ContDiffOn ℝ ∞ (ψ ∘ (A.chart j).symm)
          ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) :=
        ((hψ j).1.contDiffOn hopen.uniqueDiffOn).restrict_scalars ℝ
      refine ((hrd.comp_contDiffOn han).mono Set.inter_subset_right).congr (fun w hw => ?_)
      have hws : (A.chart j).symm w ∈ ψ.source := hw.2.2
      simp only [Function.comp_apply, if_pos hws]
    · refine ⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ.symm '' ⋃ i ∈ t, tsupport (F i))ᶜ,
        (A.chart j).isOpen_inter_preimage_symm hLc.isClosed.isOpen_compl,
        ⟨hyt, fun hL => hp (hLs hL)⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : ℝ))).congr (fun w hw => ?_)
      have hwL : (A.chart j).symm w ∉ ψ.symm '' ⋃ i ∈ t, tsupport (F i) := hw.2.2
      show (fun x => if x ∈ ψ.source then
        Real.smoothTransition (2 * ∑ i ∈ t, F i (ψ x)) else 0) ((A.chart j).symm w) = 0
      by_contra hne
      exact hwL (hsupp hne)
  · intro z hz
    simp only [if_pos (hKψ hz)]
    exact Real.smoothTransition.one_of_one_le (by linarith [hgK (ψ z) ⟨z, hz, rfl⟩])
end ReciprocityTheory.AnForm.M.PLC
