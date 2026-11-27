-- Prove2me | solution 1 for SPFacilityGraph.lemma_Q_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:17:11.652614+00:00
-- url     : https://prove2.me/submissions/8872a453-1bc7-4fa5-8f2d-e75e513066ee

import Mathlib
import Theorems.Thm_SPFacilityGraph_theorem_4_5
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_comm
import Theorems.Thm_SPFacilityGraph_MetricGraph_exists_walk_eq_dist
import Definitions.Def_SPFacilityGraph_IsSSP
import Definitions.Def_SPFacilityGraph_IsEdgeTriangulation
import Definitions.Def_SPFacilityGraph_HasDetAttribution

set_option autoImplicit false

open SPFacilityGraph

theorem solution {k n : ℕ} (G : MetricGraph k) (M : Profile G n → G.Pt) (W : Finset G.Pt)
    (K : Geometry.SimplicialComplex ℝ (Fin n → EuclideanSpace ℝ (Fin k)))
    (hK : IsEdgeTriangulation G n K) (hA : HasDetAttribution G M W K) :
    IsSSP G M := by
  classical
  obtain ⟨hfin, hspace, -⟩ := hK
  obtain ⟨sel, hsel⟩ := hA
  have hdist_nonneg : ∀ a b : G.Pt, 0 ≤ G.dist a b := by
    intro a b
    obtain ⟨m, p, -, -, -, hL⟩ := G.exists_walk_eq_dist a b
    rw [← hL]; exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hFfin : K.facets.Finite := hfin.subset Geometry.SimplicialComplex.facets_subset
  let Fs := hFfin.toFinset
  let 𝒰 : Finset (Finset ((Fin n → EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k))) :=
    (Fs ×ˢ G.edges).image (fun se => se.1 ×ˢ ({se.2.1, se.2.2} : Finset (EuclideanSpace ℝ (Fin k))))
  have hhull : ∀ (s : Finset (Fin n → EuclideanSpace ℝ (Fin k)))
      (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)),
      convexHull ℝ ((s ×ˢ ({e.1, e.2} : Finset (EuclideanSpace ℝ (Fin k))) : Finset _) :
        Set ((Fin n → EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k))) =
        convexHull ℝ (s : Set (Fin n → EuclideanSpace ℝ (Fin k))) ×ˢ segment ℝ e.1 e.2 := by
    intro s e
    rw [Finset.coe_product, convexHull_prod, ← convexHull_pair]
    simp
  have hcover : ∀ (x : Profile G n) (t : G.Pt), (G.embed x, (t : EuclideanSpace ℝ (Fin k))) ∈
      ⋃ P ∈ 𝒰, convexHull ℝ (P : Set ((Fin n → EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k))) := by
    intro x t
    have hx : G.embed x ∈ K.space := by rw [hspace]; exact ⟨x, rfl⟩
    obtain ⟨f, hf, hxf⟩ := Geometry.SimplicialComplex.mem_space_iff.1 hx
    obtain ⟨s, hfs, hsmax⟩ := hfin.exists_le_maximal hf
    have hsF : s ∈ K.facets := Geometry.SimplicialComplex.mem_facets.2
      ⟨hsmax.1, fun u hu hsu => le_antisymm hsu (hsmax.2 hu hsu)⟩
    obtain ⟨e, he, hte⟩ := Set.mem_iUnion₂.1 t.2
    refine Set.mem_biUnion (x := s ×ˢ ({e.1, e.2} : Finset (EuclideanSpace ℝ (Fin k)))) ?_ ?_
    · exact Finset.mem_image.2 ⟨(s, e), Finset.mem_product.2 ⟨hFfin.mem_toFinset.2 hsF, he⟩, rfl⟩
    · rw [hhull]
      exact ⟨convexHull_mono (by exact_mod_cast hfs) hxf, hte⟩
  refine (theorem_4_5 G _ 𝒰 hcover).2 ?_
  intro i t x y z hd ⟨P, hP, hyP, hzP⟩
  obtain ⟨⟨s, e⟩, hse, rfl⟩ := Finset.mem_image.1 hP
  have hsF : s ∈ K.facets := hFfin.mem_toFinset.1 (Finset.mem_product.1 hse).1
  rw [hhull] at hyP hzP
  have hMy := hsel ⟨s, hsF⟩ (Function.update x i y) hyP.1
  have hMz := hsel ⟨s, hsF⟩ (Function.update x i z) hzP.1
  show G.dist (M (Function.update x i y)) t ≤ G.dist (M (Function.update x i z)) t
  rw [hMy, hMz]
  cases hsl : sel ⟨s, hsF⟩ with
  | report j =>
    simp only [Selector.eval]
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self]
      rw [G.dist_comm y t, G.dist_comm z t, hd]
      linarith [hdist_nonneg y z]
    · simp [Function.update_of_ne hj]
  | const w hw => simp [Selector.eval]
