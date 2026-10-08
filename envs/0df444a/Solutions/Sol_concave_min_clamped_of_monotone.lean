-- Prove2me | solution 1 for concave_min_clamped_of_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T16:59:45.246974+00:00
-- url     : https://prove2.me/submissions/e9214bfa-3937-4631-a322-247e3c38da09

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution
    (a y : ℝ) (ha : 0 ≤ a) (hy : 0 ≤ y) (h : ℝ → ℝ)
    (hh : ConcaveOn ℝ (Set.Ici 0) h)
    (hleft : MonotoneOn h (Set.Icc 0 a))
    (hright : AntitoneOn h (Set.Ici a)) :
    ConcaveOn ℝ (Set.Ici 0)
      (fun s => min (h (min s a)) (h (max (s - y) a))) := by
  let leftClamp : ℝ → ℝ := fun s => min s a
  let rightClamp : ℝ → ℝ := fun s => max (s - y) a
  have hS : Convex ℝ (Set.Ici (0 : ℝ)) := convex_Ici 0
  have hleftClamp : ConcaveOn ℝ (Set.Ici 0) leftClamp := by
    have hmin := (concaveOn_id hS).inf (concaveOn_const a hS)
    have hmin' : ConcaveOn ℝ (Set.Ici 0) (fun s => min s a) := by
      convert hmin using 1 <;> ext s <;> rfl
    simpa [leftClamp] using hmin'
  have hrightShift : ConvexOn ℝ (Set.Ici 0) (fun s : ℝ => s - y) := by
    convert (convexOn_id hS).add (convexOn_const (-y) hS) using 1 <;>
      ext s <;> simp [sub_eq_add_neg]
  have hrightClamp : ConvexOn ℝ (Set.Ici 0) rightClamp := by
    have hmax := hrightShift.sup (convexOn_const a hS)
    have hmax' : ConvexOn ℝ (Set.Ici 0) (fun s => max (s - y) a) := by
      convert hmax using 1 <;> ext s <;> rfl
    simpa [rightClamp] using hmax'
  have hleft_image_eq : leftClamp '' Set.Ici (0 : ℝ) = Set.Icc 0 a := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨le_min hs ha, min_le_right _ _⟩
    · intro hx
      refine ⟨x, hx.1, ?_⟩
      simp [leftClamp, min_eq_left hx.2]
  have hright_image_eq : rightClamp '' Set.Ici (0 : ℝ) = Set.Ici a := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact Set.mem_Ici.mpr (le_max_right _ _)
    · intro hx
      refine ⟨x + y, ?_, ?_⟩
      · have hax : a ≤ x := Set.mem_Ici.mp hx
        exact add_nonneg (le_trans ha hax) hy
      · simp [rightClamp, max_eq_left (Set.mem_Ici.mp hx)]
  have hleft_image_convex : Convex ℝ (leftClamp '' Set.Ici (0 : ℝ)) := by
    rw [hleft_image_eq]
    exact convex_Icc 0 a
  have hright_image_convex : Convex ℝ (rightClamp '' Set.Ici (0 : ℝ)) := by
    rw [hright_image_eq]
    exact convex_Ici a
  have hleft_image_i0 : leftClamp '' Set.Ici (0 : ℝ) ⊆ Set.Ici 0 := by
    intro x hx
    rw [hleft_image_eq] at hx
    exact Set.mem_Ici.mpr hx.1
  have hleft_image_ia : leftClamp '' Set.Ici (0 : ℝ) ⊆ Set.Icc 0 a := by
    rw [hleft_image_eq]
  have hright_image_i0 : rightClamp '' Set.Ici (0 : ℝ) ⊆ Set.Ici 0 := by
    intro x hx
    rw [hright_image_eq] at hx
    exact Set.mem_Ici.mpr (le_trans ha (Set.mem_Ici.mp hx))
  have hright_image_ia : rightClamp '' Set.Ici (0 : ℝ) ⊆ Set.Ici a := by
    rw [hright_image_eq]
  have hleft_hconc : ConcaveOn ℝ (leftClamp '' Set.Ici (0 : ℝ)) h := by
    refine ⟨hleft_image_convex, ?_⟩
    intro x hx z hz u v hu hv huv
    exact hh.2 (hleft_image_i0 hx) (hleft_image_i0 hz) hu hv huv
  have hleft_hmono : MonotoneOn h (leftClamp '' Set.Ici (0 : ℝ)) := by
    intro x hx z hz hxz
    exact hleft (hleft_image_ia hx) (hleft_image_ia hz) hxz
  have hleft_comp : ConcaveOn ℝ (Set.Ici 0) (h ∘ leftClamp) :=
    ConcaveOn.comp hleft_hconc hleftClamp hleft_hmono
  have hright_hconc : ConcaveOn ℝ (rightClamp '' Set.Ici (0 : ℝ)) h := by
    refine ⟨hright_image_convex, ?_⟩
    intro x hx z hz u v hu hv huv
    exact hh.2 (hright_image_i0 hx) (hright_image_i0 hz) hu hv huv
  have hright_hanti : AntitoneOn h (rightClamp '' Set.Ici (0 : ℝ)) := by
    intro x hx z hz hxz
    exact hright (hright_image_ia hx) (hright_image_ia hz) hxz
  have hright_comp : ConcaveOn ℝ (Set.Ici 0) (h ∘ rightClamp) :=
    ConcaveOn.comp_convexOn hright_hconc hrightClamp hright_hanti
  have hmin := hleft_comp.inf hright_comp
  have hmin' : ConcaveOn ℝ (Set.Ici 0)
      (fun s => min ((h ∘ leftClamp) s) ((h ∘ rightClamp) s)) := by
    convert hmin using 1 <;> ext s <;> rfl
  simpa [leftClamp, rightClamp, Function.comp_def] using hmin'
