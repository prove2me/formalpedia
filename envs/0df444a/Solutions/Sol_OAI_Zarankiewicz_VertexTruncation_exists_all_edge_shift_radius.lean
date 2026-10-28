-- Prove2me | solution 1 for OAI.Zarankiewicz.VertexTruncation.exists_all_edge_shift_radius
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T13:18:42.80798+00:00
-- url     : https://prove2.me/submissions/b8c706f7-0c2d-4dd0-9f52-d5ed909579d9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr002
import Definitions.Def_OAIB3Zr003

section
-- module Solutions.OAIB3_Zar.Crossing_ArcRangeMinimality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem path_range_eq_of_subset {a b : Plane} (γ δ : Path a b)
    (hγ : Function.Injective γ) (hsub : Set.range δ ⊆ Set.range γ) :
    Set.range δ=Set.range γ := by
  apply Set.Subset.antisymm hsub
  rintro x ⟨t,rfl⟩
  have hc : IsPreconnected (γ ⁻¹' Set.range δ) :=
    (isPreconnected_range δ.continuous).preimage_of_isClosedMap hγ γ.continuous.isClosedMap hsub
  have h0 : (0 : unitInterval) ∈ γ ⁻¹' Set.range δ := ⟨0,δ.source.trans γ.source.symm⟩
  have h1 : (1 : unitInterval) ∈ γ ⁻¹' Set.range δ := ⟨1,δ.target.trans γ.target.symm⟩
  exact hc.Icc_subset h0 h1 t.property

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FiniteSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem finite_positive_lower_bound {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 < f i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ S, ε < f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨ε,hε,hbound⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hfi := hf i (Finset.mem_insert_self i S)
    refine ⟨min (ε/2) (f i/2),lt_min (by linarith) (by linarith),?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (min_le_right _ _).trans_lt (by linarith)
    · exact (min_le_left _ _).trans_lt (by have hh := hbound j hj; linarith)

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PlanarSegments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical

theorem det2_swap (u v : Plane) : det2 v u = -det2 u v := by
  simp only [det2]
  ring

theorem det2_neg_left (u v : Plane) : det2 (-u) v = -det2 u v := by
  simp [det2]
  ring

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PlanarDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem det2_add_right (u v w : Plane) : det2 u (v+w) = det2 u v+det2 u w := by
  dsimp [det2]
  ring

theorem det2_sub_right (u v w : Plane) : det2 u (v-w) = det2 u v-det2 u w := by
  dsimp [det2]
  ring

theorem det2_smul_left (r : ℝ) (u v : Plane) : det2 (r • u) v = r*det2 u v := by
  dsimp [det2]
  ring

theorem det2_smul_right (r : ℝ) (u v : Plane) : det2 u (r • v) = r*det2 u v := by
  dsimp [det2]
  ring

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OffsetVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem det2_normalShift (v : Plane) (hv : v ≠ 0) : det2 v (normalShift v) = 1 := by
  have hn := ne_of_gt (squaredLength_pos v hv)
  unfold normalShift
  rw [det2_smul_right]
  have he : det2 v (rotateQuarter v) = squaredLength v := by
    dsimp [det2,rotateQuarter,squaredLength]
    ring
  rw [he,inv_mul_cancel₀ hn]

theorem det2_cornerShift_left (u v : Plane) (hn : det2 u v ≠ 0) :
    det2 u (cornerShift u v) = 1 := by
  unfold cornerShift
  rw [det2_smul_right,det2_sub_right,det2_self,sub_zero,inv_mul_cancel₀ hn]

theorem det2_cornerShift_right (u v : Plane) (hn : det2 u v ≠ 0) :
    det2 v (cornerShift u v) = 1 := by
  unfold cornerShift
  rw [det2_smul_right,det2_sub_right,det2_self,det2_swap u v,zero_sub,neg_neg,inv_mul_cancel₀ hn]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ParallelDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem offset_direction_det_zero (a b qa qb : Plane) (ε : ℝ)
    (ha : det2 (b-a) qa=1) (hb : det2 (b-a) qb=1) :
    det2 (b-a) ((b+ε • qb)-(a+ε • qa)) = 0 := by
  dsimp [det2] at *
  linear_combination ε*hb-ε*ha

theorem exists_forward_offset_radius (a b qa qb : Plane) (hab : b ≠ a)
    (ha : det2 (b-a) qa=1) (hb : det2 (b-a) qb=1) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ →
      ∃ r : ℝ, 0<r ∧ (b+ε • qb)-(a+ε • qa) = r • (b-a) := by
  have hn : b-a ≠ 0 := sub_ne_zero.mpr hab
  have hlen := squaredLength_pos (b-a) hn
  let f : ℝ → ℝ := fun ε => dot2 (b-a) ((b+ε • qb)-(a+ε • qa)) / squaredLength (b-a)
  have hf : Continuous f := by
    dsimp [f,dot2,squaredLength]
    fun_prop
  have hf0 : 0<f 0 := by
    have he : f 0=1 := by
      dsimp [f]
      simp only [zero_smul,add_zero]
      have hd : dot2 (b-a) (b-a)=squaredLength (b-a) := by dsimp [dot2,squaredLength]; ring
      rw [hd]
      exact div_self (ne_of_gt hlen)
    rw [he]
    norm_num
  have hevent : ∀ᶠ ε : ℝ in 𝓝 0, 0<f ε := continuousAt_const.eventually_lt hf.continuousAt hf0
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨δ,hδ,?_⟩
  intro ε hε
  refine ⟨f ε,hd (by simpa [Real.dist_eq] using hε),?_⟩
  exact vector_parallel_of_det_zero (b-a) _ hn (offset_direction_det_zero a b qa qb ε ha hb)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RadialExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem radial_spur_exterior (z x : Plane) (r α : ℝ)
    (hx : squaredLength (x-z)=r^2) (hr : 0 < r) (hα : 0 < α) :
    segment ℝ x (x+α • (x-z)) ⊆ insert x {y | r^2 < squaredLength (y-z)} := by
  intro y hy
  rw [← Path.range_segment] at hy
  obtain ⟨t,rfl⟩ := hy
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  by_cases ht : t.val=0
  · left
    change segmentPoint x (x+α • (x-z)) t.val=x
    rw [ht,segmentPoint_zero]
  · right
    have htpos : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    change r^2 < squaredLength (segmentPoint x (x+α • (x-z)) t.val-z)
    have he : squaredLength (segmentPoint x (x+α • (x-z)) t.val-z)=
        (1+t.val*α)^2*squaredLength (x-z) := by
      dsimp [squaredLength,segmentPoint]
      ring
    rw [he,hx]
    have hp := mul_pos htpos hα
    nlinarith [sq_pos_of_pos hr,mul_pos hp (sq_pos_of_pos hr)]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SegmentSymmetries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical

theorem segmentsCrossProperly_swap (a b c d : Plane) :
    SegmentsCrossProperly c d a b ↔ SegmentsCrossProperly a b c d := by
  constructor
  · rintro ⟨hn,t,ht,u,hu,he⟩
    refine ⟨?_,u,hu,t,ht,he.symm⟩
    rw [det2_swap] at hn
    exact neg_ne_zero.mp hn
  · rintro ⟨hn,t,ht,u,hu,he⟩
    refine ⟨?_,u,hu,t,ht,he.symm⟩
    rw [det2_swap]
    exact neg_ne_zero.mpr hn

theorem nonzero_orientation_sign_neg (r : ℝ) (hr : r ≠ 0) :
    (if 0 < -r then (1 : ℝ) else -1) = -(if 0 < r then 1 else -1) := by
  by_cases hpos : 0 < r
  · have hn : ¬ 0 < -r := by linarith
    simp [hpos,hn]
  · have hn : 0 < -r := by rcases lt_or_gt_of_ne hr with hh | hh <;> linarith
    simp [hpos,hn]

theorem segmentCrossingSign_swap (a b c d : Plane) :
    segmentCrossingSign c d a b = -segmentCrossingSign a b c d := by
  unfold segmentCrossingSign
  rw [segmentsCrossProperly_swap]
  by_cases h : SegmentsCrossProperly a b c d
  · rw [ite_eq_left h, ite_eq_left h, det2_swap]
    exact nonzero_orientation_sign_neg _ h.1
  · simp [h]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SegmentParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem intersection_parameters_eq (a b c d : Plane) (hn : det2 (b-a) (d-c) ≠ 0) :
    segmentPoint a b (firstIntersectionParameter a b c d) =
      segmentPoint c d (secondIntersectionParameter a b c d) := by
  apply Prod.ext
  · change (1-firstIntersectionParameter a b c d)*a.1+firstIntersectionParameter a b c d*b.1 =
      (1-secondIntersectionParameter a b c d)*c.1+secondIntersectionParameter a b c d*d.1
    unfold firstIntersectionParameter secondIntersectionParameter
    field_simp
    dsimp [det2]
    ring
  · change (1-firstIntersectionParameter a b c d)*a.2+firstIntersectionParameter a b c d*b.2 =
      (1-secondIntersectionParameter a b c d)*c.2+secondIntersectionParameter a b c d*d.2
    unfold firstIntersectionParameter secondIntersectionParameter
    field_simp
    dsimp [det2]
    ring

theorem segmentsCrossProperly_iff_parameters (a b c d : Plane) (hn : det2 (b-a) (d-c) ≠ 0) :
    SegmentsCrossProperly a b c d ↔
      firstIntersectionParameter a b c d ∈ Set.Ioo (0 : ℝ) 1 ∧
      secondIntersectionParameter a b c d ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · rintro ⟨_,t,ht,u,hu,he⟩
    have hh := segment_intersection_parameters_unique a b c d hn t u
      (firstIntersectionParameter a b c d) (secondIntersectionParameter a b c d)
      he (intersection_parameters_eq a b c d hn)
    exact ⟨hh.1 ▸ ht,hh.2 ▸ hu⟩
  · rintro ⟨ht,hu⟩
    exact ⟨hn,_,ht,_,hu,intersection_parameters_eq a b c d hn⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SegmentContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology Classical

theorem closedSegmentsMeet_of_proper (a b c d : Plane) (h : SegmentsCrossProperly a b c d) :
    ClosedSegmentsMeet a b c d := by
  obtain ⟨_,t,ht,u,hu,he⟩ := h
  exact ⟨t,⟨ht.1.le,ht.2.le⟩,u,⟨hu.1.le,hu.2.le⟩,he⟩

theorem isClosed_closedSegmentsMeet (c d : Plane) :
    IsClosed {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 c d} := by
  let P := (Plane × Plane) × (unitInterval × unitInterval)
  let S : Set P := {x | segmentPoint x.1.1 x.1.2 x.2.1.val = segmentPoint c d x.2.2.val}
  have hS : IsClosed S := by
    apply isClosed_eq
    · dsimp [segmentPoint]
      fun_prop
    · dsimp [segmentPoint]
      fun_prop
  have hproj := (isClosedMap_fst_of_compactSpace : IsClosedMap (Prod.fst : P → Plane × Plane)) S hS
  have heq : Prod.fst '' S = {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 c d} := by
    ext ab
    constructor
    · rintro ⟨⟨ab',t,u⟩,hx,h⟩
      change ab'=ab at h
      subst ab'
      exact ⟨t.val,t.property,u.val,u.property,hx⟩
    · rintro ⟨t,ht,u,hu,h⟩
      exact ⟨(ab,(⟨t,ht⟩,⟨u,hu⟩)),h,rfl⟩
  rwa [heq] at hproj

theorem eventually_segmentCrossingSign_of_proper (a b c d : Plane)
    (h : SegmentsCrossProperly a b c d) :
    ∀ᶠ ab : Plane × Plane in 𝓝 (a,b),
      segmentCrossingSign ab.1 ab.2 c d = segmentCrossingSign a b c d := by
  have hD : Continuous (fun ab : Plane × Plane => det2 (ab.2-ab.1) (d-c)) := by
    dsimp [det2]
    fun_prop
  have hF : ContinuousAt (fun ab : Plane × Plane => firstIntersectionParameter ab.1 ab.2 c d) (a,b) := by
    apply ContinuousAt.div
    · dsimp [det2]
      fun_prop
    · exact hD.continuousAt
    · exact h.1
  have hS : ContinuousAt (fun ab : Plane × Plane => secondIntersectionParameter ab.1 ab.2 c d) (a,b) := by
    apply ContinuousAt.div
    · dsimp [det2]
      fun_prop
    · exact hD.continuousAt
    · exact h.1
  obtain ⟨ht,hu⟩ := (segmentsCrossProperly_iff_parameters a b c d h.1).mp h
  have ht' := hF.eventually (isOpen_Ioo.mem_nhds ht)
  have hu' := hS.eventually (isOpen_Ioo.mem_nhds hu)
  by_cases hpos : 0 < det2 (b-a) (d-c)
  · have hd' : ∀ᶠ ab : Plane × Plane in 𝓝 (a,b), 0 < det2 (ab.2-ab.1) (d-c) :=
      continuousAt_const.eventually_lt hD.continuousAt hpos
    filter_upwards [ht',hu',hd'] with ab ht hu hd
    have hc := (segmentsCrossProperly_iff_parameters ab.1 ab.2 c d (ne_of_gt hd)).mpr ⟨ht,hu⟩
    simp [segmentCrossingSign,h,hc,hpos,hd]
  · have hneg : det2 (b-a) (d-c) < 0 := lt_of_le_of_ne (le_of_not_gt hpos) h.1
    have hd' : ∀ᶠ ab : Plane × Plane in 𝓝 (a,b), det2 (ab.2-ab.1) (d-c) < 0 :=
      hD.continuousAt.eventually_lt continuousAt_const hneg
    filter_upwards [ht',hu',hd'] with ab ht hu hd
    have hc := (segmentsCrossProperly_iff_parameters ab.1 ab.2 c d (ne_of_lt hd)).mpr ⟨ht,hu⟩
    simp [segmentCrossingSign,h,hc,hpos,not_lt.mpr hd.le]

theorem eventually_segmentCrossingSign (a b c d : Plane) (h : SegmentPairTransverse a b c d) :
    ∀ᶠ ab : Plane × Plane in 𝓝 (a,b),
      segmentCrossingSign ab.1 ab.2 c d = segmentCrossingSign a b c d := by
  by_cases hc : SegmentsCrossProperly a b c d
  · exact eventually_segmentCrossingSign_of_proper a b c d hc
  · have hn : ¬ ClosedSegmentsMeet a b c d := by
      rintro ⟨t,ht,u,hu,he⟩
      obtain ⟨hd,ht',hu'⟩ := h t ht u hu he
      exact hc ⟨hd,t,ht',u,hu',he⟩
    have hevent := (isClosed_closedSegmentsMeet c d).isOpen_compl.mem_nhds
      (show (a,b) ∈ {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 c d}ᶜ from hn)
    filter_upwards [hevent] with ab hab
    have hn' : ¬ SegmentsCrossProperly ab.1 ab.2 c d :=
      fun hx => hab (closedSegmentsMeet_of_proper _ _ _ _ hx)
    simp [segmentCrossingSign,hc,hn']

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CollinearSegmentUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem collinear_segment_subset_union (a b c : Plane) (hac : a ≠ c)
    (h : det2 (b-a) (c-b)=0) :
    segment ℝ a c ⊆ segment ℝ a b ∪ segment ℝ b c := by
  have hd : det2 (c-a) (b-a)=0 := by
    have he : det2 (c-a) (b-a) = -det2 (b-a) (c-b) := by dsimp [det2]; ring
    rw [he,h,neg_zero]
  have hp := vector_parallel_of_det_zero (c-a) (b-a) (sub_ne_zero.mpr (Ne.symm hac)) hd
  have hb : b ∈ Set.range (AffineMap.lineMap a c : ℝ → Plane) := by
    refine ⟨dot2 (c-a) (b-a)/squaredLength (c-a),?_⟩
    rw [AffineMap.lineMap_apply]
    change (dot2 (c-a) (b-a)/squaredLength (c-a)) • (c-a)+a=b
    rw [← hp,sub_add_cancel]
  intro x hx
  rw [← insert_endpoints_openSegment] at hx
  rcases hx with hxa | hxc | hxo
  · subst x
    exact Or.inl (left_mem_segment ℝ a b)
  · subst x
    exact Or.inr (right_mem_segment ℝ b c)
  · rcases openSegment_subset_union a c hb hxo with hxb | hx'
    · subst x
      exact Or.inl (right_mem_segment ℝ a b)
    · exact hx'.elim (fun hh => Or.inl (openSegment_subset_segment ℝ a b hh))
        (fun hh => Or.inr (openSegment_subset_segment ℝ b c hh))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalChainShortcuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem minimum_shortcut_bound (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ P.pieces)
    (Q : PolygonalChain O (P.vertices i) (P.vertices j)) : j-i ≤ Q.pieces := by
  have hh := hmin (((P.take i (by omega)).join Q).join (P.drop j hj))
  simp only [pieces_join,pieces_take,pieces_drop] at hh
  omega

theorem minimum_vertices_ne (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i j : ℕ) (hij : i < j) (hj : j ≤ P.pieces) : P.vertices i ≠ P.vertices j := by
  intro he
  let Q := (point O (P.vertices i) (P.vertex_mem i (by omega))).withEndpoints rfl he.symm
  have hh := P.minimum_shortcut_bound hmin i j (by omega) hj Q
  change j-i ≤ 0 at hh
  omega

theorem minimum_nonadjacent_disjoint (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i j : ℕ) (hij : i+1 < j) (hj : j < P.pieces) :
    Disjoint (segment ℝ (P.vertices i) (P.vertices (i+1)))
      (segment ℝ (P.vertices j) (P.vertices (j+1))) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hleft : segment ℝ (P.vertices i) x ⊆ O :=
    ((convex_segment (𝕜 := ℝ) _ _).segment_subset (left_mem_segment ℝ _ _) hxi).trans
      (P.inside i (by omega))
  have hright : segment ℝ x (P.vertices (j+1)) ⊆ O :=
    ((convex_segment (𝕜 := ℝ) _ _).segment_subset hxj (right_mem_segment ℝ _ _)).trans
      (P.inside j hj)
  let Q := (single O (P.vertices i) x (P.vertex_mem i (by omega)) hleft).join
    (single O x (P.vertices (j+1)) (P.inside i (by omega) hxi) hright)
  have hh := P.minimum_shortcut_bound hmin i (j+1) (by omega) (by omega) Q
  change j+1-i ≤ 1+1 at hh
  omega

theorem minimum_two_step_not_subset (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) :
    ¬ segment ℝ (P.vertices i) (P.vertices (i+2)) ⊆ O := by
  intro h
  have hh := P.minimum_shortcut_bound hmin i (i+2) (by omega) hi
    (single O (P.vertices i) (P.vertices (i+2)) (P.vertex_mem i (by omega)) h)
  change i+2-i ≤ 1 at hh
  omega

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_MinimumChainGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem minimum_piece_ne_zero (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i < P.pieces) : P.vertices (i+1)-P.vertices i ≠ 0 := by
  exact sub_ne_zero.mpr (Ne.symm (P.minimum_vertices_ne hmin i (i+1) (by omega) (by omega)))

theorem minimum_bend_det_ne_zero (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) :
    det2 (P.vertices (i+1)-P.vertices i) (P.vertices (i+2)-P.vertices (i+1)) ≠ 0 := by
  intro he
  apply P.minimum_two_step_not_subset hmin i hi
  exact (collinear_segment_subset_union _ _ _ (P.minimum_vertices_ne hmin i (i+2) (by omega) hi) he).trans
    (Set.union_subset (P.inside i (by omega)) (P.inside (i+1) (by omega)))

end PolygonalChain
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OffsetSegments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem offset_segment_side (a b qa qb : Plane) (ε t : ℝ)
    (ha : det2 (b-a) qa=1) (hb : det2 (b-a) qb=1) :
    orient2 a b (segmentPoint (a+ε • qa) (b+ε • qb) t) = ε := by
  dsimp [orient2,det2,segmentPoint] at *
  linear_combination ε*(1-t)*ha+ε*t*hb

theorem offset_segment_no_contact (a b qa qb : Plane) (ε : ℝ) (hε : ε ≠ 0)
    (ha : det2 (b-a) qa=1) (hb : det2 (b-a) qb=1) (s t : ℝ) :
    segmentPoint a b s ≠ segmentPoint (a+ε • qa) (b+ε • qb) t := by
  intro he
  have hh := congrArg (orient2 a b) he
  rw [orient2_self_segment,offset_segment_side a b qa qb ε t ha hb] at hh
  exact hε hh.symm

theorem offset_bend_no_contact (u v q : Plane) (ε : ℝ) (hε : ε ≠ 0)
    (hu : det2 u q=ε) (hv : det2 v q=ε)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    q+α • v+β • u ≠ 0 := by
  intro he
  have h₁ := congrArg (det2 u) he
  have h₂ := congrArg (det2 v) he
  simp only [det2_add_right,det2_smul_right,det2_self,det2_zero_right,hu,hv,
    mul_zero,add_zero] at h₁ h₂
  rw [det2_swap u v] at h₂
  have hprod : (α+β)*det2 u v=0 := by nlinarith
  rcases mul_eq_zero.mp hprod with hz | hz
  · have hα0 : α=0 := by linarith
    rw [hα0,zero_mul,add_zero] at h₁
    exact hε h₁
  · rw [hz,mul_zero,add_zero] at h₁
    exact hε h₁

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OffsetTrack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem trackOffset_incident_levels (v : ℕ → Plane) (n : ℕ)
    (hv : ∀ i, i < n → trackDirection v i ≠ 0)
    (hb : ∀ i, 0 < i → i < n → det2 (trackDirection v (i-1)) (trackDirection v i) ≠ 0)
    (i : ℕ) (hi : i < n) :
    det2 (trackDirection v i) (trackOffset v n i)=1 ∧
      det2 (trackDirection v i) (trackOffset v n (i+1))=1 := by
  constructor
  · by_cases hz : i=0
    · subst i
      simpa [trackOffset] using det2_normalShift (trackDirection v 0) (hv 0 hi)
    · have hip : 0 < i := by omega
      simpa [trackOffset,hz,hi] using
        det2_cornerShift_right (trackDirection v (i-1)) (trackDirection v i) (hb i hip hi)
  · by_cases hnext : i+1 < n
    · simpa [trackOffset,hnext] using
        det2_cornerShift_left (trackDirection v i) (trackDirection v (i+1))
          (by simpa using hb (i+1) (by omega) hnext)
    · have hn : n=i+1 := by omega
      subst n
      simpa [trackOffset] using det2_normalShift (trackDirection v i) (hv i hi)

theorem shiftedTrack_stretch_no_contact (v : ℕ → Plane) (n : ℕ)
    (hv : ∀ i, i < n → trackDirection v i ≠ 0)
    (hb : ∀ i, 0 < i → i < n → det2 (trackDirection v (i-1)) (trackDirection v i) ≠ 0)
    (i : ℕ) (hi : i < n) (t : ℝ) (ht : t ≠ 0) (s r : ℝ) :
    segmentPoint (v i) (v (i+1)) s ≠
      segmentPoint (shiftedTrack v n t i) (shiftedTrack v n t (i+1)) r := by
  have hlevels := trackOffset_incident_levels v n hv hb i hi
  exact offset_segment_no_contact _ _ _ _ t ht hlevels.1 hlevels.2 s r

theorem exists_forward_shiftedTrack_radius (v : ℕ → Plane) (n : ℕ)
    (hv : ∀ i, i < n → trackDirection v i ≠ 0)
    (hb : ∀ i, 0 < i → i < n → det2 (trackDirection v (i-1)) (trackDirection v i) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ i : Fin n,
      ∃ r : ℝ, 0 < r ∧ shiftedTrack v n t (i.val+1)-shiftedTrack v n t i.val = r • trackDirection v i.val := by
  have hh (i : Fin n) := exists_forward_offset_radius (v i.val) (v (i.val+1))
    (trackOffset v n i.val) (trackOffset v n (i.val+1))
    (sub_ne_zero.mp (hv i.val i.isLt))
    (trackOffset_incident_levels v n hv hb i.val i.isLt).1
    (trackOffset_incident_levels v n hv hb i.val i.isLt).2
  choose radius hpos hdir using hh
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun i _ => hpos i)
  exact ⟨δ,hδ,fun t ht i => hdir i t (ht.trans (hbound i (Finset.mem_univ _)))⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_MinimumChainVertexPieces
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem PolygonalChain.minimum_vertex_piece_index {O : Set Plane} {a b : Plane}
    (P : PolygonalChain O a b) (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i k : ℕ) (hi : i < P.pieces) (hk : k ≤ P.pieces)
    (hx : P.vertices k ∈ segment ℝ (P.vertices i) (P.vertices (i+1))) : k=i ∨ k=i+1 := by
  have hlow : i ≤ k := by
    by_contra h
    have hki : k < i := by omega
    have hseg : segment ℝ (P.vertices k) (P.vertices (i+1)) ⊆ O :=
      ((convex_segment (𝕜 := ℝ) _ _).segment_subset hx (right_mem_segment ℝ _ _)).trans (P.inside i hi)
    have hh := P.minimum_shortcut_bound hmin k (i+1) (by omega) (by omega)
      (PolygonalChain.single O _ _ (P.vertex_mem k hk) hseg)
    change i+1-k ≤ 1 at hh
    omega
  have hhigh : k ≤ i+1 := by
    by_contra h
    have hik : i+1 < k := by omega
    have hseg : segment ℝ (P.vertices i) (P.vertices k) ⊆ O :=
      ((convex_segment (𝕜 := ℝ) _ _).segment_subset (left_mem_segment ℝ _ _) hx).trans (P.inside i hi)
    have hh := P.minimum_shortcut_bound hmin i k (by omega) hk
      (PolygonalChain.single O _ _ (P.vertex_mem i (by omega)) hseg)
    change k-i ≤ 1 at hh
    omega
  omega

theorem drawing_chain_piece_vertex {m n : ℕ} (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i < P.pieces) (j : BipartiteVertex m n)
    (hx : D.vertex j ∈ segment ℝ (P.vertices i) (P.vertices (i+1))) :
    (j=.inl e.1 ∧ i=0) ∨ (j=.inr e.2 ∧ i+1=P.pieces) := by
  obtain ⟨t,ht⟩ := P.inside i hi hx
  rcases drawing_edge_vertex_parameter D e t j ht with ⟨_,he⟩ | ⟨_,he⟩
  · have hx0 : P.vertices 0 ∈ segment ℝ (P.vertices i) (P.vertices (i+1)) := by
      simpa only [P.first,he] using hx
    have hh := P.minimum_vertex_piece_index hmin i 0 hi (by omega) hx0
    exact Or.inl ⟨he,by omega⟩
  · have hxN : P.vertices P.pieces ∈ segment ℝ (P.vertices i) (P.vertices (i+1)) := by
      simpa only [P.last,he] using hx
    have hh := P.minimum_vertex_piece_index hmin i P.pieces hi (by omega) hxN
    exact Or.inr ⟨he,by omega⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OpenSegmentEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem openSegmentTrace_ne_endpoints (a b : Plane) (hab : a ≠ b)
    (x : Plane) (hx : x ∈ openSegmentTrace a b) : x ≠ a ∧ x ≠ b := by
  obtain ⟨t,ht,he⟩ := hx
  let u : unitInterval := ⟨t,⟨ht.1.le,ht.2.le⟩⟩
  have hu : (Path.segment a b) u=x := by
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he
  constructor
  · intro h
    have hh := Path.segment_injective_of_ne hab (hu.trans (h.trans (Path.segment a b).source.symm))
    have ht0 : t=0 := congrArg Subtype.val hh
    exact ht.1.ne ht0.symm
  · intro h
    have hh := Path.segment_injective_of_ne hab (hu.trans (h.trans (Path.segment a b).target.symm))
    have ht1 : t=1 := congrArg Subtype.val hh
    exact ht.2.ne ht1

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ChainPieceInteriors
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem drawing_chain_piece_open_subset_interior {m n : ℕ} (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i < P.pieces) :
    openSegmentTrace (P.vertices i) (P.vertices (i+1)) ⊆ edgeInterior D e := by
  intro x hx
  have hseg := openSegmentTrace_subset_segment _ _ hx
  have hne := openSegmentTrace_ne_endpoints _ _
    (P.minimum_vertices_ne hmin i (i+1) (by omega) (by omega)) x hx
  apply edgeInterior_of_range_not_vertices D e x (P.inside i hi hseg)
  intro j hj
  have hvertex : D.vertex j ∈ segment ℝ (P.vertices i) (P.vertices (i+1)) := hj ▸ hseg
  rcases drawing_chain_piece_vertex D e P hmin i hi j hvertex with ⟨he,hii⟩ | ⟨he,hii⟩
  · apply hne.1
    calc
      x = D.vertex j := hj
      _ = D.vertex (.inl e.1) := congrArg D.vertex he
      _ = P.vertices i := by simpa only [hii] using P.first.symm
  · apply hne.2
    calc
      x = D.vertex j := hj
      _ = D.vertex (.inr e.2) := congrArg D.vertex he
      _ = P.vertices (i+1) := by simpa only [hii] using P.last.symm

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ChainTracePieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem drawing_chain_range_eq {m n : ℕ} (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2))) :
    Set.range P.path=Set.range (D.edge e) :=
  path_range_eq_of_subset (D.edge e) P.path (D.edge_injective e) P.path_range_subset

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RadialBoundaryPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem squaredLength_smul (v : Plane) (t : ℝ) : squaredLength (t • v)=t^2*squaredLength v := by
  dsimp [squaredLength]
  ring

theorem radialPort_sub (a b : Plane) (r : ℝ) :
    radialPort a b r-a=(r/Real.sqrt (squaredLength (b-a))) • (b-a) := by
  simp only [radialPort,add_sub_cancel_left]

theorem radialPort_on_circle (a b : Plane) (hab : a ≠ b) (r : ℝ) :
    squaredLength (radialPort a b r-a)=r^2 := by
  have hL := squaredLength_pos (b-a) (sub_ne_zero.mpr hab.symm)
  have hs : Real.sqrt (squaredLength (b-a)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL)
  rw [radialPort_sub,squaredLength_smul,div_pow,Real.sq_sqrt hL.le]
  exact div_mul_cancel₀ _ (ne_of_gt hL)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingSpokePorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem drawing_chain_startPort_interior {m n : ℕ} (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r) (hshort : r^2 < squaredLength (P.vertices 1-P.vertices 0)) :
    P.startPort r ∈ edgeInterior D e := by
  exact drawing_chain_piece_open_subset_interior D e P hmin 0 (drawing_chain_pieces_pos D e P)
    (radialPort_mem_openSegment _ _ r hr hshort)

theorem drawing_chain_endPort_interior {m n : ℕ} (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    P.endPort r ∈ edgeInterior D e := by
  have hp := drawing_chain_pieces_pos D e P
  have hs : r^2 < squaredLength (P.vertices (P.pieces-1)-P.vertices P.pieces) := by
    rwa [squaredLength_sub_comm]
  have hx := openSegmentTrace_reverse_mem _ _ _ (radialPort_mem_openSegment _ _ r hr hs)
  apply drawing_chain_piece_open_subset_interior D e P hmin (P.pieces-1) (by omega)
  simpa only [PolygonalChain.endPort,show P.pieces-1+1=P.pieces by omega] using hx

theorem drawing_chain_startPort_circle {m n : ℕ} (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ Q.pieces) (r : ℝ) :
    squaredLength (P.startPort r-D.vertex (.inl e.1))=r^2 := by
  have hp := drawing_chain_pieces_pos D e P
  have h := radialPort_on_circle (P.vertices 0) (P.vertices 1)
    (P.minimum_vertices_ne hmin 0 1 (by omega) hp) r
  simpa only [PolygonalChain.startPort,P.first] using h

theorem drawing_chain_endPort_circle {m n : ℕ} (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ Q.pieces) (r : ℝ) :
    squaredLength (P.endPort r-D.vertex (.inr e.2))=r^2 := by
  have hp := drawing_chain_pieces_pos D e P
  have h := radialPort_on_circle (P.vertices P.pieces) (P.vertices (P.pieces-1))
    (Ne.symm (P.minimum_vertices_ne hmin (P.pieces-1) P.pieces (by omega) (by omega))) r
  simpa only [PolygonalChain.endPort,P.last] using h

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FiniteEventualRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz
open scoped Topology

theorem finite_eventual_radius {ι : Type*} [Fintype ι] (P : ι → ℝ → Prop)
    (h : ∀ i, ∀ᶠ t : ℝ in 𝓝 0, P i t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ i, P i t := by
  have hex (i : ι) : ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r → P i t := by
    obtain ⟨r,hr,hh⟩ := Metric.eventually_nhds_iff.mp (h i)
    exact ⟨r,hr,fun t ht => hh (by simpa [Real.dist_eq] using ht)⟩
  choose radius hpos hprop using hex
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun i _ => hpos i)
  exact ⟨δ,hδ,fun t ht i => hprop i t (ht.trans (hbound i (Finset.mem_univ _)))⟩

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_IncidentSpokePorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem incident_edges_adjacent (j : BipartiteVertex m n) (e f : IncidentEdges j) :
    e.val.1=f.val.1 ∨ e.val.2=f.val.2 := by
  rcases e.property with he | he <;> rcases f.property with hf | hf
  · exact Or.inl (Sum.inl.inj (he.symm.trans hf))
  · cases he.symm.trans hf
  · cases he.symm.trans hf
  · exact Or.inr (Sum.inr.inj (he.symm.trans hf))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_LocalLineBends
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem segment_direction_of_local_line (a b d : Plane) (U : Set Plane)
    (hU : IsOpen U) (hb : b ∈ U)
    (hline : ∀ z ∈ U, z ∈ segment ℝ b a → det2 d (z-b)=0) :
    det2 d (a-b)=0 := by
  have hc : Continuous (fun t : ℝ => segmentPoint b a t) := by dsimp [segmentPoint]; fun_prop
  have hh : ∀ᶠ t : ℝ in 𝓝 0, segmentPoint b a t ∈ U := by
    exact hc.continuousAt.eventually (by simpa using hU.mem_nhds hb)
  obtain ⟨r,hr,hs⟩ := Metric.eventually_nhds_iff.mp hh
  let t : ℝ := min (r/2) (1/2)
  have ht : 0 < t := lt_min (by linarith) (by norm_num)
  have htr : t < r := (min_le_left _ _).trans_lt (by linarith)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hm : segmentPoint b a t ∈ U := hs (by simpa [Real.dist_eq,abs_of_pos ht] using htr)
  have hseg : segmentPoint b a t ∈ segment ℝ b a := by
    rw [← Path.range_segment]
    exact ⟨⟨t,⟨ht.le,ht1⟩⟩,by simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]⟩
  have he := hline _ hm hseg
  have heq : segmentPoint b a t-b=t • (a-b) := by
    apply Prod.ext <;> dsimp [segmentPoint] <;> ring
  rw [heq,det2_smul_right] at he
  exact (mul_eq_zero.mp he).resolve_left (ne_of_gt ht)

theorem bend_det_zero_of_local_line (a b c d : Plane) (hd : d ≠ 0)
    (U : Set Plane) (hU : IsOpen U) (hb : b ∈ U)
    (hline : ∀ z ∈ U, z ∈ segment ℝ a b ∪ segment ℝ b c → det2 d (z-b)=0) :
    det2 (b-a) (c-b)=0 := by
  have ha := segment_direction_of_local_line a b d U hU hb (by
    intro z hz hs
    exact hline z hz (Or.inl (by simpa only [segment_symm ℝ b a] using hs)))
  have hc := segment_direction_of_local_line c b d U hU hb (fun z hz hs => hline z hz (Or.inr hs))
  have hba : b-a=-(a-b) := by abel
  rw [hba,vector_parallel_of_det_zero d (a-b) hd ha,
    vector_parallel_of_det_zero d (c-b) hd hc,det2_neg_left,
    det2_smul_left,det2_smul_right,det2_self]
  ring

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_LocalSegmentTransversality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segment_direction_of_local_line_at_interior (a b x d : Plane)
    (hx : x ∈ openSegmentTrace a b) (U : Set Plane) (hU : IsOpen U) (hxU : x ∈ U)
    (hline : ∀ z ∈ U, z ∈ segment ℝ a b → det2 d (z-x)=0) :
    det2 d (b-a)=0 := by
  obtain ⟨t,ht,he⟩ := hx
  have hxseg : x ∈ segment ℝ a b := by
    rw [← Path.range_segment]
    exact ⟨⟨t,⟨ht.1.le,ht.2.le⟩⟩,by simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he⟩
  have hsub := (convex_segment (𝕜 := ℝ) a b).segment_subset hxseg (right_mem_segment ℝ a b)
  have hh := segment_direction_of_local_line b x d U hU hxU (fun z hz hs => hline z hz (hsub hs))
  have heq : b-x=(1-t) • (b-a) := by
    rw [← he]
    apply Prod.ext <;> dsimp [segmentPoint] <;> ring
  rw [heq,det2_smul_right] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by linarith [ht.2])

theorem det2_ne_zero_of_parallel_nonzero (d e u v : Plane)
    (hde : det2 d e ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hdu : det2 d u=0) (hev : det2 e v=0) : det2 u v ≠ 0 := by
  have hd : d ≠ 0 := by intro h; subst d; simp at hde
  have he : e ≠ 0 := by intro h; subst e; simp at hde
  have hU := vector_parallel_of_det_zero d u hd hdu
  have hV := vector_parallel_of_det_zero e v he hev
  have hα : dot2 d u/squaredLength d ≠ 0 := by
    intro h
    rw [h,zero_smul] at hU
    exact hu hU
  have hβ : dot2 e v/squaredLength e ≠ 0 := by
    intro h
    rw [h,zero_smul] at hV
    exact hv hV
  conv_lhs => rw [hU,hV,det2_smul_left,det2_smul_right]
  exact mul_ne_zero hα (mul_ne_zero hβ hde)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SegmentAffineForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem segmentPoint_start_form (a b : Plane) (t : ℝ) :
    segmentPoint a b t = a+t • (b-a) := by
  apply Prod.ext <;> dsimp [segmentPoint] <;> ring

theorem segmentPoint_end_form (a b : Plane) (t : ℝ) :
    segmentPoint a b t = b-(1-t) • (b-a) := by
  apply Prod.ext <;> dsimp [segmentPoint] <;> ring

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OffsetBendSegments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem offset_bend_no_reverse_contact (u v q : Plane) (ε : ℝ) (hε : ε ≠ 0)
    (hu : det2 u q=ε) (hv : det2 v q=ε)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) : q-α • u-β • v ≠ 0 := by
  intro he
  have h₁ := congrArg (det2 u) he
  have h₂ := congrArg (det2 v) he
  simp only [det2_sub_right,det2_smul_right,det2_self,det2_zero_right,hu,hv,
    mul_zero,sub_zero] at h₁ h₂
  rw [det2_swap u v] at h₂
  have hprod : (α+β)*det2 u v=0 := by nlinarith
  rcases mul_eq_zero.mp hprod with hz | hz
  · have hα0 : α=0 := by linarith
    rw [hα0,zero_mul,sub_zero] at h₂
    exact hε h₂
  · rw [hz,mul_zero,sub_zero] at h₁
    exact hε h₁

theorem incoming_shifted_outgoing_disjoint (a b c qb qc : Plane) (ε r : ℝ)
    (hε : ε ≠ 0) (hr : 0 < r)
    (hu : det2 (b-a) qb=1) (hv : det2 (c-b) qb=1)
    (hdir : (c+ε • qc)-(b+ε • qb)=r • (c-b))
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    segmentPoint a b s ≠ segmentPoint (b+ε • qb) (c+ε • qc) t := by
  intro he
  rw [segmentPoint_end_form a b s,segmentPoint_start_form,hdir,smul_smul] at he
  have hno := offset_bend_no_contact (b-a) (c-b) (ε • qb) ε hε
    (by rw [det2_smul_right,hu,mul_one]) (by rw [det2_smul_right,hv,mul_one])
    (t*r) (1-s) (mul_nonneg ht.1 hr.le) (by linarith [hs.2])
  apply hno
  calc
    ε • qb+(t*r) • (c-b)+(1-s) • (b-a) =
        ((b+ε • qb)+(t*r) • (c-b))-(b-(1-s) • (b-a)) := by abel
    _ = 0 := sub_eq_zero.mpr he.symm

theorem outgoing_shifted_incoming_disjoint (a b c qa qb : Plane) (ε r : ℝ)
    (hε : ε ≠ 0) (hr : 0 < r)
    (hu : det2 (b-a) qb=1) (hv : det2 (c-b) qb=1)
    (hdir : (b+ε • qb)-(a+ε • qa)=r • (b-a))
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    segmentPoint b c s ≠ segmentPoint (a+ε • qa) (b+ε • qb) t := by
  intro he
  rw [segmentPoint_start_form b c s,segmentPoint_end_form,hdir,smul_smul] at he
  have hno := offset_bend_no_reverse_contact (b-a) (c-b) (ε • qb) ε hε
    (by rw [det2_smul_right,hu,mul_one]) (by rw [det2_smul_right,hv,mul_one])
    ((1-t)*r) s (mul_nonneg (by linarith [ht.2]) hr.le) hs.1
  apply hno
  calc
    ε • qb-((1-t)*r) • (b-a)-s • (c-b) =
        ((b+ε • qb)-((1-t)*r) • (b-a))-(b+s • (c-b)) := by abel
    _ = 0 := sub_eq_zero.mpr he.symm

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ReducedCrossingCorners
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem det2_of_common_openSegment (a b x z : Plane)
    (hx : x ∈ openSegmentTrace a b) (hz : z ∈ openSegmentTrace a b) :
    det2 (b-a) (z-x)=0 := by
  obtain ⟨t,ht,rfl⟩ := hx
  obtain ⟨u,hu,rfl⟩ := hz
  dsimp [det2,segmentPoint]
  ring

theorem LocallyStraightAt.exists_trace_line (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n) (x : Plane) (hx : x ∈ edgeInterior D e)
    (h : LocallyStraightAt D e x) :
    ∃ d : Plane, d ≠ 0 ∧ ∃ U : Set Plane, IsOpen U ∧ x ∈ U ∧
      ∀ z ∈ U, z ∈ Set.range (D.edge e) → det2 d (z-x)=0 := by
  obtain ⟨a,b,hab,hxab,U,hU,hxU,htrace⟩ := h
  let V : Set Plane := Set.range D.vertex
  have hV : IsClosed V := (Set.finite_range D.vertex).isClosed
  have hxV : x ∉ V := by
    rintro ⟨j,hj⟩
    exact edgeInterior_not_vertex D e x hx j hj.symm
  refine ⟨b-a,sub_ne_zero.mpr (Ne.symm hab),U ∩ Vᶜ,hU.inter hV.isOpen_compl,⟨hxU,hxV⟩,?_⟩
  intro z hz hze
  have hzi : z ∈ edgeInterior D e := edgeInterior_of_range_not_vertices D e z hze (by
    intro j hj
    exact hz.2 ⟨j,hj.symm⟩)
  exact det2_of_common_openSegment a b x z hxab ((htrace z hz.1).mp hzi)

theorem minimum_bend_not_locallyStraight (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) (hx : P.vertices (i+1) ∈ edgeInterior D e) :
    ¬ LocallyStraightAt D e (P.vertices (i+1)) := by
  intro h
  obtain ⟨d,hd,U,hU,hxU,hh⟩ := LocallyStraightAt.exists_trace_line D e _ hx h
  apply P.minimum_bend_det_ne_zero hmin i hi
  apply bend_det_zero_of_local_line _ _ _ d hd U hU hxU
  intro z hz hseg
  apply hh z hz
  rcases hseg with hseg | hseg
  · exact P.inside i (by omega) hseg
  · exact P.inside (i+1) (by omega) hseg

theorem minimum_bend_not_crossing (D : AdmissibleDrawing m n)
    (hstraight : LocallyStraightCrossings D) (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) : P.vertices (i+1) ∉ crossingPoints D.toContinuousDrawing := by
  rintro ⟨f,g,hfg,hf,hg⟩
  have hx : P.vertices (i+1) ∈ edgeInterior D.toContinuousDrawing e :=
    edgeInterior_of_range_not_vertices D.toContinuousDrawing e _ (P.vertex_mem (i+1) (by omega))
      (edgeInterior_not_vertex D.toContinuousDrawing f _ hf)
  apply minimum_bend_not_locallyStraight D.toContinuousDrawing e P hmin i hi hx
  by_cases hef : e=f
  · subst f
    exact (hstraight e g hfg _ hx hg).1
  · exact (hstraight e f hef _ hx hf).1

theorem minimum_vertices_not_crossing (D : AdmissibleDrawing m n)
    (hstraight : LocallyStraightCrossings D) (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i ≤ P.pieces) : P.vertices i ∉ crossingPoints D.toContinuousDrawing := by
  by_cases h0 : i=0
  · subst i
    rw [P.first]
    rintro ⟨f,g,hfg,hf,hg⟩
    exact edgeInterior_not_vertex D.toContinuousDrawing f _ hf (.inl e.1) rfl
  by_cases hn : i=P.pieces
  · subst i
    rw [P.last]
    rintro ⟨f,g,hfg,hf,hg⟩
    exact edgeInterior_not_vertex D.toContinuousDrawing f _ hf (.inr e.2) rfl
  have h := minimum_bend_not_crossing D hstraight e P hmin (i-1) (by omega)
  simpa only [show i-1+1=i by omega] using h

theorem minimum_piece_crossing_open (D : AdmissibleDrawing m n)
    (hstraight : LocallyStraightCrossings D) (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i < P.pieces) (x : Plane) (hx : x ∈ crossingPoints D.toContinuousDrawing)
    (hseg : x ∈ segment ℝ (P.vertices i) (P.vertices (i+1))) :
    x ∈ openSegmentTrace (P.vertices i) (P.vertices (i+1)) := by
  rw [← Path.range_segment] at hseg
  obtain ⟨t,ht⟩ := hseg
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    simp only [Path.source] at ht
    exact minimum_vertices_not_crossing D hstraight e P hmin i (by omega) (ht.symm ▸ hx)
  have ht1 : t ≠ 1 := by
    intro h
    subst t
    simp only [Path.target] at ht
    exact minimum_vertices_not_crossing D hstraight e P hmin (i+1) (by omega) (ht.symm ▸ hx)
  refine ⟨t.val,⟨?_,?_⟩,?_⟩
  · exact lt_of_le_of_ne t.property.1 (fun h => ht0 (Subtype.ext h.symm))
  · exact lt_of_le_of_ne t.property.2 (fun h => ht1 (Subtype.ext h))
  · simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ReducedCrossingTransversality
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem LocallyTransverseCrossings.exists_trace_lines (D : AdmissibleDrawing m n)
    (h : LocallyTransverseCrossings D) (e f : BipartiteEdge m n) (hef : e ≠ f)
    (x : Plane) (hxe : x ∈ edgeInterior D.toContinuousDrawing e)
    (hxf : x ∈ edgeInterior D.toContinuousDrawing f) :
    ∃ d k : Plane, det2 d k ≠ 0 ∧ ∃ U : Set Plane, IsOpen U ∧ x ∈ U ∧
      (∀ z ∈ U, z ∈ Set.range (D.edge e) → det2 d (z-x)=0) ∧
      (∀ z ∈ U, z ∈ Set.range (D.edge f) → det2 k (z-x)=0) := by
  obtain ⟨a,b,c,d,hdet,hxab,hxcd,U,hU,hxU,htraceE,htraceF⟩ := h e f hef x hxe hxf
  let V : Set Plane := Set.range D.vertex
  have hV : IsClosed V := (Set.finite_range D.vertex).isClosed
  have hxV : x ∉ V := by
    rintro ⟨j,hj⟩
    exact edgeInterior_not_vertex D.toContinuousDrawing e x hxe j hj.symm
  refine ⟨b-a,d-c,hdet,U ∩ Vᶜ,hU.inter hV.isOpen_compl,⟨hxU,hxV⟩,?_,?_⟩
  · intro z hz hze
    have hzi := edgeInterior_of_range_not_vertices D.toContinuousDrawing e z hze (by
      intro j hj
      exact hz.2 ⟨j,hj.symm⟩)
    exact det2_of_common_openSegment a b x z hxab ((htraceE z hz.1).mp hzi)
  · intro z hz hzf
    have hzi := edgeInterior_of_range_not_vertices D.toContinuousDrawing f z hzf (by
      intro j hj
      exact hz.2 ⟨j,hj.symm⟩)
    exact det2_of_common_openSegment c d x z hxcd ((htraceF z hz.1).mp hzi)

theorem minimum_piece_det_at_crossing (D : AdmissibleDrawing m n)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (e f : BipartiteEdge m n) (hef : e ≠ f)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (Q : PolygonalChain (Set.range (D.edge f)) (D.vertex (.inl f.1)) (D.vertex (.inr f.2)))
    (hP : ∀ R : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ R.pieces)
    (hQ : ∀ R : PolygonalChain (Set.range (D.edge f)) (D.vertex (.inl f.1))
      (D.vertex (.inr f.2)), Q.pieces ≤ R.pieces)
    (i j : ℕ) (hi : i < P.pieces) (hj : j < Q.pieces) (x : Plane)
    (hxe : x ∈ edgeInterior D.toContinuousDrawing e) (hxf : x ∈ edgeInterior D.toContinuousDrawing f)
    (hxp : x ∈ segment ℝ (P.vertices i) (P.vertices (i+1)))
    (hxq : x ∈ segment ℝ (Q.vertices j) (Q.vertices (j+1))) :
    det2 (P.vertices (i+1)-P.vertices i) (Q.vertices (j+1)-Q.vertices j) ≠ 0 := by
  have hx : x ∈ crossingPoints D.toContinuousDrawing := ⟨e,f,hef,hxe,hxf⟩
  have hpo := minimum_piece_crossing_open D hstraight e P hP i hi x hx hxp
  have hqo := minimum_piece_crossing_open D hstraight f Q hQ j hj x hx hxq
  obtain ⟨d,k,hdk,U,hU,hxU,hlineP,hlineQ⟩ :=
    LocallyTransverseCrossings.exists_trace_lines D htrans e f hef x hxe hxf
  have hd := segment_direction_of_local_line_at_interior _ _ x d hpo U hU hxU
    (fun z hz hs => hlineP z hz (P.inside i hi hs))
  have hk := segment_direction_of_local_line_at_interior _ _ x k hqo U hU hxU
    (fun z hz hs => hlineQ z hz (Q.inside j hj hs))
  exact det2_ne_zero_of_parallel_nonzero d k _ _ hdk
    (P.minimum_piece_ne_zero hP i hi) (Q.minimum_piece_ne_zero hQ j hj) hd hk

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SegmentClosedIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem closedSegmentsMeet_iff_nonempty_inter (a b c d : Plane) :
    ClosedSegmentsMeet a b c d ↔ (segment ℝ a b ∩ segment ℝ c d).Nonempty := by
  constructor
  · rintro ⟨s,hs,t,ht,he⟩
    refine ⟨segmentPoint a b s,?_,?_⟩
    · rw [← Path.range_segment]
      exact ⟨⟨s,hs⟩,by simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]⟩
    · rw [← Path.range_segment]
      exact ⟨⟨t,ht⟩,by simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he.symm⟩
  · rintro ⟨x,hx,hy⟩
    rw [← Path.range_segment] at hx hy
    obtain ⟨s,hs⟩ := hx
    obtain ⟨t,ht⟩ := hy
    refine ⟨s.val,s.property,t.val,t.property,?_⟩
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs.trans ht.symm

theorem not_closedSegmentsMeet_of_disjoint (a b c d : Plane)
    (h : Disjoint (segment ℝ a b) (segment ℝ c d)) : ¬ ClosedSegmentsMeet a b c d := by
  intro hh
  obtain ⟨x,hx,hy⟩ := (closedSegmentsMeet_iff_nonempty_inter a b c d).mp hh
  exact Set.disjoint_left.mp h hx hy

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TransversalityStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology Classical

theorem segmentPairTransverse_of_proper (a b c d : Plane) (h : SegmentsCrossProperly a b c d) :
    SegmentPairTransverse a b c d := by
  obtain ⟨hn,t₀,ht₀,u₀,hu₀,he₀⟩ := h
  intro t ht u hu he
  obtain ⟨rfl,rfl⟩ := segment_intersection_parameters_unique a b c d hn t u t₀ u₀ he he₀
  exact ⟨hn,ht₀,hu₀⟩

theorem segmentPairTransverse_swap (a b c d : Plane) (h : SegmentPairTransverse a b c d) :
    SegmentPairTransverse c d a b := by
  intro t ht u hu he
  obtain ⟨hn,hu',ht'⟩ := h u hu t ht he.symm
  refine ⟨?_,ht',hu'⟩
  rw [det2_swap]
  exact neg_ne_zero.mpr hn

theorem eventually_segmentPairTransverse (a b c d : Plane) (h : SegmentPairTransverse a b c d) :
    ∀ᶠ ab : Plane × Plane in 𝓝 (a,b), SegmentPairTransverse ab.1 ab.2 c d := by
  by_cases hc : SegmentsCrossProperly a b c d
  · have hsign : segmentCrossingSign a b c d ≠ 0 := by
      unfold segmentCrossingSign
      rw [ite_eq_left hc]
      split_ifs <;> norm_num
    filter_upwards [eventually_segmentCrossingSign_of_proper a b c d hc] with ab hab
    apply segmentPairTransverse_of_proper
    by_contra hn
    have hz : segmentCrossingSign ab.1 ab.2 c d = 0 := by simp [segmentCrossingSign,hn]
    exact hsign (hab.symm.trans hz)
  · have hn : ¬ ClosedSegmentsMeet a b c d := by
      rintro ⟨t,ht,u,hu,he⟩
      obtain ⟨hd,ht',hu'⟩ := h t ht u hu he
      exact hc ⟨hd,t,ht',u,hu',he⟩
    have hevent := (isClosed_closedSegmentsMeet c d).isOpen_compl.mem_nhds
      (show (a,b) ∈ {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 c d}ᶜ from hn)
    filter_upwards [hevent] with ab hab
    intro t ht u hu he
    exact False.elim (hab ⟨t,ht,u,hu,he⟩)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ShiftedSegmentStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem shifted_endpoints_tendsto (c d qc qd : Plane) :
    Filter.Tendsto (fun t : ℝ => (c+t • qc,d+t • qd)) (𝓝 0) (𝓝 (c,d)) := by
  have hh : Continuous (fun t : ℝ => (c+t • qc,d+t • qd)) := by fun_prop
  simpa [ContinuousAt] using hh.continuousAt (x := 0)

theorem eventually_shifted_segment_pair (a b c d qc qd : Plane)
    (h : SegmentPairTransverse a b c d) :
    ∀ᶠ t : ℝ in 𝓝 0,
      SegmentPairTransverse a b (c+t • qc) (d+t • qd) ∧
      segmentCrossingSign a b (c+t • qc) (d+t • qd)=segmentCrossingSign a b c d := by
  have hs := segmentPairTransverse_swap a b c d h
  have he := (shifted_endpoints_tendsto c d qc qd).eventually
    ((eventually_segmentPairTransverse c d a b hs).and (eventually_segmentCrossingSign c d a b hs))
  filter_upwards [he] with t ht
  refine ⟨segmentPairTransverse_swap _ _ _ _ ht.1,?_⟩
  have hsign := ht.2
  rw [segmentCrossingSign_swap a b _ _,segmentCrossingSign_swap a b c d] at hsign
  exact neg_injective hsign

theorem closedSegmentsMeet_symm (a b c d : Plane) : ClosedSegmentsMeet a b c d ↔ ClosedSegmentsMeet c d a b := by
  constructor <;> rintro ⟨t,ht,u,hu,he⟩ <;> exact ⟨u,hu,t,ht,he.symm⟩

theorem eventually_shifted_disjoint_segments (a b c d qc qd : Plane)
    (h : ¬ ClosedSegmentsMeet a b c d) :
    ∀ᶠ t : ℝ in 𝓝 0, ¬ ClosedSegmentsMeet a b (c+t • qc) (d+t • qd) := by
  have hn : (c,d) ∈ {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 a b}ᶜ := by
    intro hx
    exact h ((closedSegmentsMeet_symm c d a b).mp hx)
  have he := (shifted_endpoints_tendsto c d qc qd).eventually
    ((isClosed_closedSegmentsMeet a b).isOpen_compl.mem_nhds hn)
  filter_upwards [he] with t ht
  intro hx
  exact ht ((closedSegmentsMeet_symm a b _ _).mp hx)

theorem exists_shifted_segment_pairs_radius {ι : Type*} [Fintype ι]
    (a b c d qc qd : ι → Plane) (h : ∀ i, SegmentPairTransverse (a i) (b i) (c i) (d i)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ i,
      SegmentPairTransverse (a i) (b i) (c i+t • qc i) (d i+t • qd i) ∧
      segmentCrossingSign (a i) (b i) (c i+t • qc i) (d i+t • qd i)=
        segmentCrossingSign (a i) (b i) (c i) (d i) := by
  exact finite_eventual_radius _ (fun i => eventually_shifted_segment_pair _ _ _ _ _ _ (h i))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SharedTrackAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology Classical

theorem exists_shared_track_avoidance_radius (v : ℕ → Plane) (n : ℕ)
    (hv : ∀ i, i < n → trackDirection v i ≠ 0)
    (hb : ∀ i, 0 < i → i < n → det2 (trackDirection v (i-1)) (trackDirection v i) ≠ 0)
    (hfar : ∀ i j : Fin n, i.val+1 < j.val ∨ j.val+1 < i.val →
      ¬ ClosedSegmentsMeet (v i.val) (v (i.val+1)) (v j.val) (v (j.val+1))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ i j : Fin n,
      ¬ ClosedSegmentsMeet (v i.val) (v (i.val+1))
        (shiftedTrack v n t j.val) (shiftedTrack v n t (j.val+1)) := by
  have hevent (ij : Fin n × Fin n) : ∀ᶠ t : ℝ in 𝓝 0,
      (ij.1.val+1 < ij.2.val ∨ ij.2.val+1 < ij.1.val) →
      ¬ ClosedSegmentsMeet (v ij.1.val) (v (ij.1.val+1))
        (shiftedTrack v n t ij.2.val) (shiftedTrack v n t (ij.2.val+1)) := by
    by_cases hh : ij.1.val+1 < ij.2.val ∨ ij.2.val+1 < ij.1.val
    · exact (eventually_shifted_disjoint_segments _ _ _ _ _ _ (hfar ij.1 ij.2 hh)).mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hh h))
  obtain ⟨δ₀,hδ₀,hstable⟩ := finite_eventual_radius _ hevent
  obtain ⟨δ₁,hδ₁,hforward⟩ := exists_forward_shiftedTrack_radius v n hv hb
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro t ht hsmall i j
  have hdir := hforward t (hsmall.trans_le (min_le_right _ _))
  by_cases hij : i=j
  · subst j
    rintro ⟨s,hs,r,hr,he⟩
    exact shiftedTrack_stretch_no_contact v n hv hb i.val i.isLt t ht s r he
  · by_cases hnext : j.val=i.val+1
    · obtain ⟨r,hr,heq⟩ := hdir j
      have hu := (trackOffset_incident_levels v n hv hb i.val i.isLt).2
      have hv' := (trackOffset_incident_levels v n hv hb j.val j.isLt).1
      rw [hnext] at hv'
      have hd : (v (i.val+1+1)+t • trackOffset v n (i.val+1+1))-
          (v (i.val+1)+t • trackOffset v n (i.val+1))=r • (v (i.val+1+1)-v (i.val+1)) := by
        simpa only [shiftedTrack,trackDirection,hnext] using heq
      rintro ⟨s,hs,u,hu',he⟩
      apply incoming_shifted_outgoing_disjoint (v i.val) (v (i.val+1)) (v (i.val+1+1))
        (trackOffset v n (i.val+1)) (trackOffset v n (i.val+1+1)) t r ht hr hu hv' hd s u hs hu'
      simpa only [shiftedTrack,hnext] using he
    · by_cases hprev : i.val=j.val+1
      · obtain ⟨r,hr,heq⟩ := hdir j
        have hu := (trackOffset_incident_levels v n hv hb j.val j.isLt).2
        have hv' := (trackOffset_incident_levels v n hv hb i.val i.isLt).1
        rw [hprev] at hv'
        rintro ⟨s,hs,u,hu',he⟩
        apply outgoing_shifted_incoming_disjoint (v j.val) (v (j.val+1)) (v (j.val+1+1))
          (trackOffset v n j.val) (trackOffset v n (j.val+1)) t r ht hr hu hv' heq s u hs hu'
        simpa only [shiftedTrack,hprev] using he
      · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
        exact hstable t (hsmall.trans_le (min_le_left _ _)) (i,j) (by change i.val+1 < j.val ∨ j.val+1 < i.val; omega)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedChainVertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem radialPort_parameter_half (a b : Plane) (r : ℝ) (hr : 0 < r)
    (hshort : 4*r^2 < squaredLength (b-a)) :
    0 < r/Real.sqrt (squaredLength (b-a)) ∧ r/Real.sqrt (squaredLength (b-a)) < 1/2 := by
  have hL : 0 < squaredLength (b-a) := by nlinarith [sq_nonneg r]
  have hs := Real.sqrt_pos.mpr hL
  have hs2 := Real.sq_sqrt hL.le
  exact ⟨div_pos hr hs,(div_lt_iff₀ hs).mpr (by nlinarith)⟩

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem startPort_eq_fraction (P : PolygonalChain O a b) (r : ℝ) :
    P.startPort r=P.vertices 0+P.startFraction r • (P.vertices 1-P.vertices 0) := rfl

theorem endPort_eq_fraction (P : PolygonalChain O a b) (r : ℝ) :
    P.endPort r=P.vertices P.pieces-P.endFraction r • (P.vertices P.pieces-P.vertices (P.pieces-1)) := by
  unfold endPort radialPort endFraction
  rw [squaredLength_sub_comm (P.vertices (P.pieces-1)) (P.vertices P.pieces)]
  apply Prod.ext <;> dsimp <;> ring

end PolygonalChain
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedChainDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem truncated_start_formula (P : PolygonalChain O a b) (r : ℝ) (i : ℕ) (hi : i < P.pieces) :
    P.truncatedVertices r i=P.vertices i+(if i=0 then P.startFraction r else 0) • trackDirection P.vertices i := by
  by_cases h : i=0
  · subst i
    rw [truncatedVertices_first,startPort_eq_fraction]
    rfl
  · simp only [truncatedVertices,ite_eq_right h,ite_eq_right (show i ≠ P.pieces by omega),zero_smul,add_zero]

theorem truncated_end_formula (P : PolygonalChain O a b) (r : ℝ) (i : ℕ) (_hi : i < P.pieces) :
    P.truncatedVertices r (i+1)=P.vertices (i+1)-(if i+1=P.pieces then P.endFraction r else 0) •
      trackDirection P.vertices i := by
  by_cases h : i+1=P.pieces
  · have hh : i=P.pieces-1 := by omega
    rw [h,truncatedVertices_last P (by omega) r,endPort_eq_fraction,ite_eq_left rfl]
    simp only [trackDirection,hh,show P.pieces-1+1=P.pieces by omega]
  · simp only [truncatedVertices,ite_eq_right (show i+1 ≠ 0 by omega),ite_eq_right h,zero_smul,sub_zero]

theorem truncated_direction (P : PolygonalChain O a b) (r : ℝ) (i : ℕ) (hi : i < P.pieces) :
    trackDirection (P.truncatedVertices r) i=P.truncatedScale r i • trackDirection P.vertices i := by
  change P.truncatedVertices r (i+1)-P.truncatedVertices r i=_
  rw [truncated_end_formula P r i hi,truncated_start_formula P r i hi]
  apply Prod.ext <;> dsimp [trackDirection,truncatedScale] <;> ring

theorem truncatedScale_pos (P : PolygonalChain O a b) (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) (i : ℕ) :
    0 < P.truncatedScale r i := by
  have hs := radialPort_parameter_half (P.vertices 0) (P.vertices 1) r hr hfirst
  have he := radialPort_parameter_half (P.vertices (P.pieces-1)) (P.vertices P.pieces) r hr hlast
  change 0 < P.startFraction r ∧ P.startFraction r < 1/2 at hs
  change 0 < P.endFraction r ∧ P.endFraction r < 1/2 at he
  unfold truncatedScale
  split_ifs <;> linarith

theorem truncated_direction_ne_zero (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1)))
    (i : ℕ) (hi : i < P.pieces) : trackDirection (P.truncatedVertices r) i ≠ 0 := by
  rw [P.truncated_direction r i hi]
  exact smul_ne_zero (ne_of_gt (P.truncatedScale_pos r hr hfirst hlast i)) (P.minimum_piece_ne_zero hmin i hi)

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedTrackAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem truncated_bend_ne_zero (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1)))
    (i : ℕ) (hi : 0 < i) (hi' : i < P.pieces) :
    det2 (trackDirection (P.truncatedVertices r) (i-1)) (trackDirection (P.truncatedVertices r) i) ≠ 0 := by
  rw [P.truncated_direction r (i-1) (by omega),P.truncated_direction r i hi',det2_smul_left,det2_smul_right]
  apply mul_ne_zero (ne_of_gt (P.truncatedScale_pos r hr hfirst hlast (i-1)))
  apply mul_ne_zero (ne_of_gt (P.truncatedScale_pos r hr hfirst hlast i))
  have h := P.minimum_bend_det_ne_zero hmin (i-1) (by omega)
  simpa only [trackDirection,show i-1+1=i by omega,show i-1+2=i+1 by omega] using h

theorem truncated_offset_avoidance (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ i j : Fin P.pieces,
      ¬ ClosedSegmentsMeet (P.truncatedVertices r i.val) (P.truncatedVertices r (i.val+1))
        (shiftedTrack (P.truncatedVertices r) P.pieces t j.val)
        (shiftedTrack (P.truncatedVertices r) P.pieces t (j.val+1)) := by
  apply exists_shared_track_avoidance_radius (P.truncatedVertices r) P.pieces
    (P.truncated_direction_ne_zero hmin r hr hfirst hlast)
    (P.truncated_bend_ne_zero hmin r hr hfirst hlast)
  intro i j hij
  have hdis : Disjoint (segment ℝ (P.vertices i.val) (P.vertices (i.val+1)))
      (segment ℝ (P.vertices j.val) (P.vertices (j.val+1))) := by
    rcases hij with h | h
    · exact P.minimum_nonadjacent_disjoint hmin i.val j.val h j.isLt
    · exact (P.minimum_nonadjacent_disjoint hmin j.val i.val h i.isLt).symm
  have hfst : r^2 < squaredLength (P.vertices 1-P.vertices 0) := by nlinarith [sq_nonneg r]
  have hlst : r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1)) := by nlinarith [sq_nonneg r]
  exact not_closedSegmentsMeet_of_disjoint _ _ _ _ (hdis.mono
    (P.truncated_piece_subset r hr hfst hlst i.val i.isLt)
    (P.truncated_piece_subset r hr hfst hlst j.val j.isLt))

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedRadialEnds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem radial_segment_of_coefficients (o p q v : Plane) (r α β : ℝ)
    (hr : 0 < r) (hα : 0 < α) (hβ : 0 < β)
    (hp : p-o=α • v) (hq : q-p=β • v) (hc : squaredLength (p-o)=r^2) :
    segment ℝ p q ⊆ insert p {x | r^2 < squaredLength (x-o)} := by
  have he : q=p+(β/α) • (p-o) := by
    rw [hp,smul_smul,div_mul_cancel₀ _ (ne_of_gt hα)]
    rw [← hq]
    abel
  rw [he]
  exact radial_spur_exterior o p r (β/α) hc hr (div_pos hβ hα)

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem truncated_first_exterior (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces) (hp : 0 < P.pieces)
    (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    segment ℝ (P.truncatedVertices r 0) (P.truncatedVertices r 1) ⊆
      insert (P.startPort r) {x | r^2 < squaredLength (x-P.vertices 0)} := by
  have hα := (radialPort_parameter_half (P.vertices 0) (P.vertices 1) r hr hfirst).1
  have hβ := P.truncatedScale_pos r hr hfirst hlast 0
  rw [P.truncatedVertices_first]
  apply radial_segment_of_coefficients (P.vertices 0) (P.startPort r) (P.truncatedVertices r 1)
    (trackDirection P.vertices 0) r (P.startFraction r) (P.truncatedScale r 0) hr hα hβ
  · exact radialPort_sub (P.vertices 0) (P.vertices 1) r
  · simpa only [trackDirection,P.truncatedVertices_first] using P.truncated_direction r 0 hp
  · exact radialPort_on_circle (P.vertices 0) (P.vertices 1)
      (P.minimum_vertices_ne hmin 0 1 (by omega) hp) r

theorem truncated_last_exterior (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces) (hp : 0 < P.pieces)
    (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    segment ℝ (P.truncatedVertices r (P.pieces-1)) (P.truncatedVertices r P.pieces) ⊆
      insert (P.endPort r) {x | r^2 < squaredLength (x-P.vertices P.pieces)} := by
  have hi : P.pieces-1 < P.pieces := by omega
  have hα := (radialPort_parameter_half (P.vertices (P.pieces-1)) (P.vertices P.pieces) r hr hlast).1
  have hβ := P.truncatedScale_pos r hr hfirst hlast (P.pieces-1)
  rw [P.truncatedVertices_last hp,segment_symm]
  apply radial_segment_of_coefficients (P.vertices P.pieces) (P.endPort r)
    (P.truncatedVertices r (P.pieces-1)) (-(trackDirection P.vertices (P.pieces-1)))
    r (P.endFraction r) (P.truncatedScale r (P.pieces-1)) hr hα hβ
  · rw [P.endPort_eq_fraction]
    simp only [trackDirection,show P.pieces-1+1=P.pieces by omega,smul_neg]
    abel
  · have h := P.truncated_direction r (P.pieces-1) hi
    simp only [trackDirection,show P.pieces-1+1=P.pieces by omega,P.truncatedVertices_last hp] at h ⊢
    rw [smul_neg,← h]
    abel
  · have hn := Ne.symm (P.minimum_vertices_ne hmin (P.pieces-1) P.pieces hi (by omega))
    exact radialPort_on_circle (P.vertices P.pieces) (P.vertices (P.pieces-1)) hn r

end PolygonalChain
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedDrawingDisks
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem truncated_piece_vertex_disk_cases (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, 4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (j : BipartiteVertex m n) (e : BipartiteEdge m n) (i : Fin (P e).pieces) (x : Plane)
    (hx : x ∈ segment ℝ ((P e).truncatedVertices r i.val) ((P e).truncatedVertices r (i.val+1))) :
    (j=Sum.inl e.1 ∧ x=(P e).startPort r) ∨
      (j=Sum.inr e.2 ∧ x=(P e).endPort r) ∨ r^2 < squaredLength (x-D.vertex j) := by
  have hp := drawing_chain_pieces_pos D e (P e)
  by_cases hfirst : j=Sum.inl e.1 ∧ i.val=0
  · have hh := (P e).truncated_first_exterior (hmin e) hp r hr (hshort e).1 (hshort e).2
      (by simpa only [hfirst.2] using hx)
    rcases Set.mem_insert_iff.mp hh with he | he
    · exact Or.inl ⟨hfirst.1,he⟩
    · right; right
      simpa only [Set.mem_ofPred_eq,(P e).first,hfirst.1] using he
  by_cases hlast : j=Sum.inr e.2 ∧ i.val+1=(P e).pieces
  · have hi : i.val=(P e).pieces-1 := by omega
    have hh := (P e).truncated_last_exterior (hmin e) hp r hr (hshort e).1 (hshort e).2
      (by simpa only [hi,show (P e).pieces-1+1=(P e).pieces by omega] using hx)
    rcases Set.mem_insert_iff.mp hh with he | he
    · exact Or.inr (Or.inl ⟨hlast.1,he⟩)
    · right; right
      simpa only [Set.mem_ofPred_eq,(P e).last,hlast.1] using he
  · right; right
    have hs : r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) := by nlinarith [(hshort e).1,sq_nonneg r]
    have ht : r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)) := by
      nlinarith [(hshort e).2,sq_nonneg r]
    have hxi := (P e).truncated_piece_subset r hr hs ht i.val i.isLt hx
    by_contra h
    exact Set.disjoint_left.mp (hclear j e i (fun h => h.elim hfirst hlast)) (le_of_not_gt h) hxi

theorem truncated_path_vertex_disk_cases (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, 4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (j : BipartiteVertex m n) (e : BipartiteEdge m n) (x : Plane)
    (hx : x ∈ Set.range (polygonalArcPath ((P e).truncatedVertices r) (P e).pieces)) :
    (j=Sum.inl e.1 ∧ x=(P e).startPort r) ∨
      (j=Sum.inr e.2 ∧ x=(P e).endPort r) ∨ r^2 < squaredLength (x-D.vertex j) := by
  obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece ((P e).truncatedVertices r) (P e).pieces
    (drawing_chain_pieces_pos D e (P e)) x hx
  exact truncated_piece_vertex_disk_cases D P hmin r hr hshort hclear j e ⟨i,hi⟩ x hxi

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_VertexDisksCrossingFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem vertex_disks_crossing_free (D : AdmissibleDrawing m n) (hnorm : NoAdjacentCrossings D)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (r : ℝ)
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (j : BipartiteVertex m n) :
    Disjoint (closedRoundDisk (D.vertex j) r) (crossingPoints D.toContinuousDrawing) := by
  apply Set.disjoint_left.mpr
  rintro x hxd ⟨e,f,hef,hxe,hxf⟩
  have hincident (g : BipartiteEdge m n) (hxg : x ∈ edgeInterior D.toContinuousDrawing g) :
      j=Sum.inl g.1 ∨ j=Sum.inr g.2 := by
    have hx := edgeInterior_subset_range D.toContinuousDrawing g hxg
    rw [← drawing_chain_range_eq D.toContinuousDrawing g (P g)] at hx
    obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece (P g).vertices (P g).pieces
      (drawing_chain_pieces_pos D.toContinuousDrawing g (P g)) x hx
    by_contra h
    have hbad : ¬ ((j=Sum.inl g.1 ∧ i=0) ∨ (j=Sum.inr g.2 ∧ i+1=(P g).pieces)) :=
      fun hh => h (hh.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1))
    exact Set.disjoint_left.mp (hclear j g ⟨i,hi⟩ hbad) hxd hxi
  have hadj := incident_edges_adjacent j ⟨e,hincident e hxe⟩ ⟨f,hincident f hxf⟩
  have hh : x ∈ edgeInterior D.toContinuousDrawing e ∩ edgeInterior D.toContinuousDrawing f := ⟨hxe,hxf⟩
  rw [hnorm e f hef hadj] at hh
  exact hh

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedDrawingInteriors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem truncated_range_subset_edgeInterior (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, 4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (e : BipartiteEdge m n) :
    Set.range (polygonalArcPath ((P e).truncatedVertices r) (P e).pieces) ⊆ edgeInterior D e := by
  intro x hx
  have hs : r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) := by nlinarith [(hshort e).1,sq_nonneg r]
  have ht : r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)) := by
    nlinarith [(hshort e).2,sq_nonneg r]
  apply edgeInterior_of_range_not_vertices D e x
  · exact ((P e).truncated (drawing_chain_pieces_pos D e (P e)) r hr hs ht).path_range_subset hx
  · intro j he
    rcases truncated_path_vertex_disk_cases D P hmin r hr hshort hclear j e x hx with ⟨hj,hp⟩ | ⟨hj,hp⟩ | hout
    · have hpi := drawing_chain_startPort_interior D e (P e) (hmin e) r hr hs
      exact edgeInterior_not_vertex D e _ hpi j (hp.symm.trans he)
    · have hpi := drawing_chain_endPort_interior D e (P e) (hmin e) r hr ht
      exact edgeInterior_not_vertex D e _ hpi j (hp.symm.trans he)
    · rw [he,sub_self] at hout
      have hz : squaredLength (0 : Plane)=0 := by simp [squaredLength]
      rw [hz] at hout
      exact (sq_nonneg r).not_gt hout

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedCrossingCorners
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem truncated_vertices_not_crossing (D : AdmissibleDrawing m n)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (r : ℝ)
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (e : BipartiteEdge m n) (i : ℕ) (hi : i ≤ (P e).pieces) :
    (P e).truncatedVertices r i ∉ crossingPoints D.toContinuousDrawing := by
  by_cases h0 : i=0
  · subst i
    rw [(P e).truncatedVertices_first]
    intro hx
    have hc := (drawing_chain_startPort_circle D.toContinuousDrawing e (P e) (hmin e) r).le
    exact Set.disjoint_left.mp (vertex_disks_crossing_free D hnorm P r hclear (.inl e.1)) hc hx
  by_cases hn : i=(P e).pieces
  · subst i
    rw [(P e).truncatedVertices_last (drawing_chain_pieces_pos D.toContinuousDrawing e (P e))]
    intro hx
    have hc := (drawing_chain_endPort_circle D.toContinuousDrawing e (P e) (hmin e) r).le
    exact Set.disjoint_left.mp (vertex_disks_crossing_free D hnorm P r hclear (.inr e.2)) hc hx
  · simp only [PolygonalChain.truncatedVertices,ite_eq_right h0,ite_eq_right hn]
    exact minimum_vertices_not_crossing D hstraight e (P e) (hmin e) i hi

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedSegmentTransversality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segment_parameter_strict_of_avoids_endpoints (a b x : Plane) (S : Set Plane)
    (hx : x ∈ S) (ha : a ∉ S) (hb : b ∉ S) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (he : segmentPoint a b t=x) : t ∈ Set.Ioo (0 : ℝ) 1 := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h,segmentPoint_zero] at he
    exact ha (he.symm ▸ hx)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h,segmentPoint_one] at he
    exact hb (he.symm ▸ hx)
  exact ⟨lt_of_le_of_ne ht.1 ht0.symm,lt_of_le_of_ne ht.2 ht1⟩

theorem truncated_segment_pair_transverse {m n : ℕ} (D : AdmissibleDrawing m n)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D)
    (htrans : LocallyTransverseCrossings D)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, 4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (e f : BipartiteEdge m n) (hef : e ≠ f) (i : Fin (P e).pieces) (j : Fin (P f).pieces) :
    SegmentPairTransverse ((P e).truncatedVertices r i.val) ((P e).truncatedVertices r (i.val+1))
      ((P f).truncatedVertices r j.val) ((P f).truncatedVertices r (j.val+1)) := by
  intro s hs t ht he
  let x := segmentPoint ((P e).truncatedVertices r i.val) ((P e).truncatedVertices r (i.val+1)) s
  have hxe : x ∈ segment ℝ ((P e).truncatedVertices r i.val) ((P e).truncatedVertices r (i.val+1)) := by
    rw [← Path.range_segment]
    exact ⟨⟨s,hs⟩,by simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint,x]⟩
  have hxf : x ∈ segment ℝ ((P f).truncatedVertices r j.val) ((P f).truncatedVertices r (j.val+1)) := by
    rw [← Path.range_segment]
    refine ⟨⟨t,ht⟩,?_⟩
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,x,segmentPoint] using he.symm
  have hie := truncated_range_subset_edgeInterior D.toContinuousDrawing P hmin r hr hshort hclear e
    (polygonalArcPath_piece_subset_range _ _ i.val i.isLt hxe)
  have hif := truncated_range_subset_edgeInterior D.toContinuousDrawing P hmin r hr hshort hclear f
    (polygonalArcPath_piece_subset_range _ _ j.val j.isLt hxf)
  have hcross : x ∈ crossingPoints D.toContinuousDrawing := ⟨e,f,hef,hie,hif⟩
  have hcorner := truncated_vertices_not_crossing D hnorm hstraight P hmin r hclear
  have hsi := segment_parameter_strict_of_avoids_endpoints _ _ x _ hcross
    (hcorner e i.val (by omega)) (hcorner e (i.val+1) (by omega)) s hs rfl
  have hti := segment_parameter_strict_of_avoids_endpoints _ _ x _ hcross
    (hcorner f j.val (by omega)) (hcorner f (j.val+1) (by omega)) t ht he.symm
  refine ⟨?_,hsi,hti⟩
  have hweak (g : BipartiteEdge m n) :
      r^2 < squaredLength ((P g).vertices 1-(P g).vertices 0) ∧
      r^2 < squaredLength ((P g).vertices (P g).pieces-(P g).vertices ((P g).pieces-1)) := by
    constructor <;> nlinarith [(hshort g).1,(hshort g).2,sq_nonneg r]
  have hde := minimum_piece_det_at_crossing D hstraight htrans e f hef (P e) (P f) (hmin e) (hmin f)
    i.val j.val i.isLt j.isLt x hie hif
    ((P e).truncated_piece_subset r hr (hweak e).1 (hweak e).2 i.val i.isLt hxe)
    ((P f).truncated_piece_subset r hr (hweak f).1 (hweak f).2 j.val j.isLt hxf)
  change det2 (trackDirection ((P e).truncatedVertices r) i.val) (trackDirection ((P f).truncatedVertices r) j.val) ≠ 0
  rw [(P e).truncated_direction r i.val i.isLt,(P f).truncated_direction r j.val j.isLt,
    det2_smul_left,det2_smul_right]
  exact mul_ne_zero (ne_of_gt ((P e).truncatedScale_pos r hr (hshort e).1 (hshort e).2 i.val))
    (mul_ne_zero (ne_of_gt ((P f).truncatedScale_pos r hr (hshort f).1 (hshort f).2 j.val)) hde)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_VertexTruncationGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
variable {m n : ℕ}

theorem offset_avoidance {D : ContinuousDrawing m n} (V : VertexTruncation D) (e : BipartiteEdge m n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ i j : Fin (V.pieces e),
      ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
        (shiftedTrack (V.vertices e) (V.pieces e) t j.val)
        (shiftedTrack (V.vertices e) (V.pieces e) t (j.val+1)) :=
  (V.chain e).truncated_offset_avoidance (V.minimal e) V.radius V.radius_pos (V.short e).1 (V.short e).2

theorem pair_transverse {D : AdmissibleDrawing m n} (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (e f : BipartiteEdge m n) (hef : e ≠ f) (i : Fin (V.pieces e)) (j : Fin (V.pieces f)) :
    SegmentPairTransverse (V.vertices e i.val) (V.vertices e (i.val+1))
      (V.vertices f j.val) (V.vertices f (j.val+1)) :=
  truncated_segment_pair_transverse D hnorm hstraight htrans V.chain V.minimal V.radius V.radius_pos
    V.short V.piece_clearance e f hef i j

end Zarankiewicz.VertexTruncation

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedTrackStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem exists_distinct_edge_shift_radius (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ e f : BipartiteEdge m n, e ≠ f →
      ∀ i : Fin (V.pieces e), ∀ j : Fin (V.pieces f),
        SegmentPairTransverse (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices f) (V.pieces f) t j.val)
          (shiftedTrack (V.vertices f) (V.pieces f) t (j.val+1)) ∧
        segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices f) (V.pieces f) t j.val)
          (shiftedTrack (V.vertices f) (V.pieces f) t (j.val+1)) =
          segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
            (V.vertices f j.val) (V.vertices f (j.val+1)) := by
  classical
  let Pair := Σ e : BipartiteEdge m n, Σ f : {f : BipartiteEdge m n // e ≠ f},
    Fin (V.pieces e) × Fin (V.pieces f.val)
  let a : Pair → Plane := fun k => V.vertices k.1 k.2.2.1.val
  let b : Pair → Plane := fun k => V.vertices k.1 (k.2.2.1.val+1)
  let c : Pair → Plane := fun k => V.vertices k.2.1.val k.2.2.2.val
  let d : Pair → Plane := fun k => V.vertices k.2.1.val (k.2.2.2.val+1)
  let qc : Pair → Plane := fun k => trackOffset (V.vertices k.2.1.val) (V.pieces k.2.1.val) k.2.2.2.val
  let qd : Pair → Plane := fun k => trackOffset (V.vertices k.2.1.val) (V.pieces k.2.1.val) (k.2.2.2.val+1)
  have hh (k : Pair) : SegmentPairTransverse (a k) (b k) (c k) (d k) :=
    V.pair_transverse hnorm hstraight htrans k.1 k.2.1.val k.2.1.property k.2.2.1 k.2.2.2
  obtain ⟨δ,hδ,hstable⟩ := exists_shifted_segment_pairs_radius a b c d qc qd hh
  refine ⟨δ,hδ,?_⟩
  intro t ht e f hef i j
  exact hstable t ht ⟨e,⟨f,hef⟩,i,j⟩

end Zarankiewicz.VertexTruncation

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_UniformTrackPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
open scoped BigOperators
variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem exists_all_edge_shift_radius_oai (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ e f : BipartiteEdge m n,
      ∀ i : Fin (V.pieces e), ∀ j : Fin (V.pieces f),
        SegmentPairTransverse (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices f) (V.pieces f) t j.val)
          (shiftedTrack (V.vertices f) (V.pieces f) t (j.val+1)) ∧
        segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices f) (V.pieces f) t j.val)
          (shiftedTrack (V.vertices f) (V.pieces f) t (j.val+1)) =
          if e=f then 0 else segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
            (V.vertices f j.val) (V.vertices f (j.val+1)) := by
  classical
  obtain ⟨δ₀,hδ₀,hother⟩ := V.exists_distinct_edge_shift_radius hnorm hstraight htrans
  choose radius hpos hself using V.offset_avoidance
  obtain ⟨δ₁,hδ₁,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun e _ => hpos e)
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro t ht hsmall e f i j
  by_cases hef : e=f
  · subst f
    have hno := hself e t ht ((hsmall.trans_le (min_le_right _ _)).trans (hbound e (Finset.mem_univ _))) i j
    refine ⟨?_,?_⟩
    · intro s hs u hu he
      exact False.elim (hno ⟨s,hs,u,hu,he⟩)
    · have hp : ¬ SegmentsCrossProperly (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices e) (V.pieces e) t j.val)
          (shiftedTrack (V.vertices e) (V.pieces e) t (j.val+1)) :=
        fun h => hno (closedSegmentsMeet_of_proper _ _ _ _ h)
      simp [segmentCrossingSign,hp]
  · obtain ⟨hT,hS⟩ := hother t (hsmall.trans_le (min_le_left _ _)) e f hef i j
    exact ⟨hT,by simpa only [ite_eq_right hef] using hS⟩

end Zarankiewicz.VertexTruncation

end

end OAI
end

theorem solution : type_of% @OAI.Zarankiewicz.VertexTruncation.exists_all_edge_shift_radius_oai := @OAI.Zarankiewicz.VertexTruncation.exists_all_edge_shift_radius_oai
