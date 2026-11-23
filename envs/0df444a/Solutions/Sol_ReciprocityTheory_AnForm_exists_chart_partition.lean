-- Prove2me | solution 1 for ReciprocityTheory.AnForm.exists_chart_partition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:17.906828+00:00
-- url     : https://prove2.me/submissions/8f94b538-ff1c-4a9f-b8a7-4f3c259b4b38

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Partition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open scoped ContDiff
open Set Metric
namespace ReciprocityTheory.AnForm
theorem _root_.solution {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {D m : ℕ} (e : Fin m → OpenPartialHomeomorph X (Fin D → ℂ))
    (hcov : ∀ x, ∃ i, x ∈ (e i).source)
    (htr : ∀ i j, ContDiffOn ℝ ∞ (e j ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) :
    ∃ χ : Fin m → X → ℝ, (∀ i x, 0 ≤ χ i x) ∧ (∀ x, ∑ i, χ i x = 1) ∧
      (∀ i, tsupport (χ i) ⊆ (e i).source) ∧
      (∀ i j, ContDiffOn ℝ ∞ (χ i ∘ (e j).symm) (e j).target) := by
  classical
  have hext : ∀ (k : Fin m) (g : (Fin D → ℂ) → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ (e k).target →
      tsupport (fun p => if p ∈ (e k).source then g (e k p) else 0) ⊆ (e k).source ∧
      ∀ j, ContDiffOn ℝ ∞ ((fun p => if p ∈ (e k).source then g (e k p) else 0) ∘ (e j).symm)
        (e j).target := by
    intro k g hg hgc hgt
    set G : X → ℝ := fun p => if p ∈ (e k).source then g (e k p) else 0 with hG
    set T : Set X := (e k).symm '' tsupport g with hT
    have hTc : IsCompact T :=
      (show IsCompact (tsupport g) from hgc).image_of_continuousOn ((e k).continuousOn_symm.mono hgt)
    have hTs : T ⊆ (e k).source := by
      rintro _ ⟨y, hy, rfl⟩
      exact (e k).map_target (hgt hy)
    have hsupp : Function.support G ⊆ T := by
      intro p hp
      rw [Function.mem_support] at hp
      by_cases hps : p ∈ (e k).source
      · simp only [hG, if_pos hps] at hp
        exact ⟨e k p, subset_tsupport g hp, (e k).left_inv hps⟩
      · simp only [hG, if_neg hps] at hp
        exact absurd rfl hp
    have hts : tsupport G ⊆ T := closure_minimal hsupp hTc.isClosed
    refine ⟨hts.trans hTs, fun j => ?_⟩
    apply contDiffOn_of_locally_contDiffOn
    intro y hy
    by_cases hp : (e j).symm y ∈ (e k).source
    · refine ⟨(e j).target ∩ (e j).symm ⁻¹' (e k).source,
        (e j).isOpen_inter_preimage_symm (e k).open_source, ⟨hy, hp⟩, ?_⟩
      have h1 : ContDiffOn ℝ ∞ (g ∘ (e k ∘ (e j).symm))
          ((e j).target ∩ (e j).symm ⁻¹' (e k).source) := hg.comp_contDiffOn (htr j k)
      refine (h1.mono Set.inter_subset_right).congr ?_
      intro y' hy'
      have hc : (e j).symm y' ∈ (e k).source := hy'.2.2
      simp only [Function.comp, hG, if_pos hc]
    · refine ⟨(e j).target ∩ (e j).symm ⁻¹' Tᶜ,
        (e j).isOpen_inter_preimage_symm hTc.isClosed.isOpen_compl,
        ⟨hy, fun hT' => hp (hTs hT')⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : ℝ))).congr ?_
      intro y' hy'
      have h2 : ¬ G ((e j).symm y') ≠ 0 := fun h => hy'.2.2 (hsupp h)
      exact not_not.mp h2
  have hb : ∀ x : X, ∃ k : Fin m, ∃ g : (Fin D → ℂ) → ℝ, x ∈ (e k).source ∧
      tsupport g ⊆ (e k).target ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      Set.range g ⊆ Set.Icc 0 1 ∧ g (e k x) = 1 := by
    intro x
    obtain ⟨k, hk⟩ := hcov x
    obtain ⟨g, h1, h2, h3, h4, h5⟩ :=
      exists_contDiff_tsupport_subset (n := ⊤) ((e k).open_target.mem_nhds ((e k).map_source hk))
    exact ⟨k, g, hk, h1, h2, h3, h4, h5⟩
  choose κ g hxs hgt hgc hgs hgr hg1 using hb
  let ψ : X → X → ℝ := fun x p => if p ∈ (e (κ x)).source then g x (e (κ x) p) else 0
  have hψ0 : ∀ x p, 0 ≤ ψ x p := by
    intro x p
    simp only [ψ]
    split_ifs
    · exact (hgr x ⟨_, rfl⟩).1
    · exact le_rfl
  have hψext := fun x => hext (κ x) (g x) (hgs x) (hgc x) (hgt x)
  let O : X → Set X := fun x => (e (κ x)).source ∩ (e (κ x)) ⁻¹' {v | 1 / 2 < g x v}
  have hO : ∀ x, IsOpen (O x) := fun x =>
    (e (κ x)).continuousOn.isOpen_inter_preimage (e (κ x)).open_source
      (isOpen_lt continuous_const (hgs x).continuous)
  have hxO : ∀ x, x ∈ O x := by
    intro x
    refine ⟨hxs x, ?_⟩
    show (1 : ℝ) / 2 < g x (e (κ x) x)
    rw [hg1 x]
    norm_num
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun p _ => Set.mem_iUnion.mpr ⟨p, hxO p⟩)
  have hOψ : ∀ x p, p ∈ O x → 1 / 2 < ψ x p := by
    intro x p hp
    simp only [ψ, if_pos hp.1]
    exact hp.2
  have hS : ∀ p, 0 < ∑ x ∈ t, ψ x p := by
    intro p
    have hp := ht (Set.mem_univ p)
    simp only [Set.mem_iUnion] at hp
    obtain ⟨x, hx, hpx⟩ := hp
    have h1 := hOψ x p hpx
    have h2 := Finset.single_le_sum (fun y _ => hψ0 y p) hx
    linarith
  refine ⟨fun k p => (∑ x ∈ t.filter (fun x => κ x = k), ψ x p) / ∑ x ∈ t, ψ x p, ?_, ?_, ?_, ?_⟩
  · intro k p
    exact div_nonneg (Finset.sum_nonneg fun x _ => hψ0 x p) (hS p).le
  · intro p
    rw [← Finset.sum_div, Finset.sum_fiberwise]
    exact div_self (hS p).ne'
  · intro k
    have hC : IsClosed (⋃ x ∈ t.filter (fun x => κ x = k), tsupport (ψ x)) :=
      isClosed_biUnion_finset fun x _ => isClosed_tsupport _
    refine (closure_minimal ?_ hC).trans ?_
    · intro p hp
      rw [Function.mem_support] at hp
      have hnum : ∑ x ∈ t.filter (fun x => κ x = k), ψ x p ≠ 0 := fun h => hp (by simp only [h, zero_div])
      obtain ⟨x, hx, hxp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnum
      exact Set.mem_biUnion hx (subset_tsupport _ hxp)
    · intro p hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨x, hx, hpx⟩ := hp
      have hk : κ x = k := (Finset.mem_filter.mp hx).2
      have hsrc := (hψext x).1 hpx
      rw [hk] at hsrc
      exact hsrc
  · intro k j
    have hnum : ContDiffOn ℝ ∞ (fun y => ∑ x ∈ t.filter (fun x => κ x = k), ψ x ((e j).symm y))
        (e j).target := ContDiffOn.sum fun x _ => (hψext x).2 j
    have hden : ContDiffOn ℝ ∞ (fun y => ∑ x ∈ t, ψ x ((e j).symm y)) (e j).target :=
      ContDiffOn.sum fun x _ => (hψext x).2 j
    exact hnum.div hden fun y _ => (hS _).ne'
end ReciprocityTheory.AnForm
