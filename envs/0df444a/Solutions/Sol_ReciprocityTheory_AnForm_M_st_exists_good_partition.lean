-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_exists_good_partition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:46.541794+00:00
-- url     : https://prove2.me/submissions/8e834175-e68f-4b42-8723-c88e504e0d11

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_trans_smooth
import Theorems.Thm_ReciprocityTheory_AnForm_exists_chart_partition


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) {r : ℕ}
    (Φ : Fin r → LocPot X) :
    ∃ (M : ℕ) (θ : Fin M → X → ℝ) (G : Fin M → Set X) (j : Fin M → Fin A.n)
      (x0 : Fin M → Fin r → X),
      (∀ m, A.Smooth (θ m)) ∧ (∀ m x, 0 ≤ θ m x) ∧ (∀ x, ∑ m, θ m x = 1) ∧
      (∀ m, tsupport (θ m) ⊆ G m) ∧ (∀ m, IsOpen (G m)) ∧
      (∀ m, G m ⊆ (A.chart (j m)).source) ∧ (∀ m i, G m ⊆ (Φ i).U (x0 m i)) := by
  classical
  choose jx hjx using A.cover
  let G : X → Set X := fun x => (A.chart (jx x)).source ∩ ⋂ i, (Φ i).U x
  have hGo : ∀ x, IsOpen (G x) := fun x =>
    (A.chart (jx x)).open_source.inter (isOpen_iInter_of_finite fun i => (Φ i).isOpen_U x)
  have hGx : ∀ x, x ∈ G x := fun x => ⟨hjx x, Set.mem_iInter.mpr fun i => (Φ i).mem_U x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover G hGo
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hGx x⟩)
  let pt : Fin t.card → X := fun m => (t.equivFin.symm m : X)
  let ch : Fin t.card → OpenPartialHomeomorph X (Fin e → ℂ) := fun m =>
    (A.chart (jx (pt m))).restr (G (pt m))
  have hsrc : ∀ m, (ch m).source = G (pt m) := by
    intro m
    simp only [ch, OpenPartialHomeomorph.restr_source, (hGo _).interior_eq]
    exact Set.inter_eq_right.mpr Set.inter_subset_left
  have hcov : ∀ x, ∃ m, x ∈ (ch m).source := by
    intro x
    obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, x ∈ G y := by simpa using ht (Set.mem_univ x)
    refine ⟨t.equivFin ⟨y, hy⟩, ?_⟩
    rw [hsrc]
    simpa [pt] using hxy
  have htr : ∀ a b, ContDiffOn ℝ ∞ (ch b ∘ (ch a).symm)
      ((ch a).target ∩ (ch a).symm ⁻¹' (ch b).source) := by
    intro a b
    simp only [ch, OpenPartialHomeomorph.restr_apply, OpenPartialHomeomorph.restr_symm_apply,
      OpenPartialHomeomorph.restr_target, OpenPartialHomeomorph.restr_source]
    exact (st_trans_smooth A _ _).mono fun y hy => ⟨hy.1.1, hy.2.1⟩
  obtain ⟨χ, hχ0, hχ1, hχs, hχsm⟩ := exists_chart_partition ch hcov htr
  refine ⟨t.card, χ, fun m => G (pt m), fun m => jx (pt m), fun m _ => pt m, ?_, hχ0, hχ1,
    fun m => (hχs m).trans (hsrc m).subset, fun m => hGo _, fun m => Set.inter_subset_left,
    fun m i x hx => Set.mem_iInter.mp hx.2 i⟩
  intro m k y hy
  obtain ⟨n, hn⟩ := hcov ((A.chart k).symm y)
  have hyk : y ∈ (A.chart k).target := hy.1
  have hxs : (A.chart k).symm y ∈ (A.chart (jx (pt n))).source := by
    have hn' := hn
    rw [hsrc] at hn'
    exact hn'.1
  have hx_in : (A.chart (jx (pt n))) ((A.chart k).symm y) ∈ (ch n).target := (ch n).map_source hn
  have hsm := hχsm m n
  simp only [ch, OpenPartialHomeomorph.restr_symm_apply] at hsm
  have hf := hsm.contDiffAt (((A.chart (jx (pt n))).restr (G (pt n))).open_target.mem_nhds hx_in)
  have hW : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart (jx (pt n))).source) :=
    (A.chart k).isOpen_inter_preimage_symm (A.chart (jx (pt n))).open_source
  have hg := (st_trans_smooth A k (jx (pt n))).contDiffAt (hW.mem_nhds ⟨hyk, hxs⟩)
  have hc := hf.comp y hg
  refine (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hW.mem_nhds ⟨hyk, hxs⟩] with z hz
  simp only [Function.comp_apply]
  rw [(A.chart (jx (pt n))).left_inv hz.2]
end ReciprocityTheory.AnForm.M
