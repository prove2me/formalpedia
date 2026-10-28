-- Prove2me | solution 1 for OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_cycle_block_radius
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T13:17:58.812987+00:00
-- url     : https://prove2.me/submissions/fa57e654-fa14-4c16-9350-dbd5503d6283

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr003
import Definitions.Def_OAIB3Zr004
import Theorems.Thm_OAI_Zarankiewicz_TruncatedSpokeCoordinates_exists_cross_type_radius
import Theorems.Thm_OAI_Zarankiewicz_VertexTruncation_exists_all_edge_shift_radius
import Theorems.Thm_OAI_Zarankiewicz_VertexTruncation_exists_uniform_track_intersections

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

theorem finite_node_separation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (hn : Function.Injective node) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j, i ≠ j → ε < |node i-node j| := by
  obtain ⟨ε,hε,hb⟩ := finite_positive_lower_bound
    (Finset.univ.filter (fun ij : ι × ι => ij.1 ≠ ij.2))
    (fun ij => |node ij.1-node ij.2|) (by
      intro ij hij
      exact abs_pos.mpr (sub_ne_zero.mpr (hn.ne (Finset.mem_filter.mp hij).2)))
  exact ⟨ε,hε,fun i j hij => hb (i,j) (by simpa using hij)⟩

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

theorem det2_neg_right (u v : Plane) : det2 u (-v) = -det2 u v := by
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

theorem segmentsCrossProperly_reverse_left (a b c d : Plane) :
    SegmentsCrossProperly b a c d ↔ SegmentsCrossProperly a b c d := by
  have forward : ∀ a b c d : Plane,
      SegmentsCrossProperly a b c d → SegmentsCrossProperly b a c d := by
    intro a b c d h
    obtain ⟨hn,t,ht,u,hu,he⟩ := h
    refine ⟨?_,1-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,u,hu,?_⟩
    · rw [← neg_sub b a, det2_neg_left]
      exact neg_ne_zero.mpr hn
    · rwa [segmentPoint_reverse]
  exact ⟨forward b a c d, forward a b c d⟩

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

theorem segmentCrossingSign_reverse_left (a b c d : Plane) :
    segmentCrossingSign b a c d = -segmentCrossingSign a b c d := by
  unfold segmentCrossingSign
  rw [segmentsCrossProperly_reverse_left]
  by_cases h : SegmentsCrossProperly a b c d
  · rw [ite_eq_left h, ite_eq_left h, ← neg_sub b a, det2_neg_left]
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
-- module Solutions.OAIB3_Zar.Crossing_SegmentSides
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem orient2_other_difference (a b c d : Plane) :
    orient2 c d a-orient2 c d b = det2 (b-a) (d-c) := by
  dsimp [orient2,det2]
  ring

theorem segmentCrossingSign_of_positive_sides (a b c d : Plane)
    (hc : orient2 a b c < 0) (hd : 0 < orient2 a b d)
    (ha : 0 < orient2 c d a) (hb : orient2 c d b < 0) :
    segmentCrossingSign a b c d = 1 := by
  have hdiff := orient2_difference a b c d
  have hother := orient2_other_difference a b c d
  have hdet : 0 < det2 (b-a) (d-c) := by linarith
  have hcros : SegmentsCrossProperly a b c d := by
    apply (segmentsCrossProperly_iff_parameters a b c d (ne_of_gt hdet)).mpr
    constructor
    · change 0 < orient2 c d a / det2 (b-a) (d-c) ∧ orient2 c d a / det2 (b-a) (d-c) < 1
      exact ⟨div_pos ha hdet, (div_lt_one hdet).mpr (by linarith)⟩
    · change 0 < -orient2 a b c / det2 (b-a) (d-c) ∧ -orient2 a b c / det2 (b-a) (d-c) < 1
      exact ⟨div_pos (neg_pos.mpr hc) hdet, (div_lt_one hdet).mpr (by linarith)⟩
  simp [segmentCrossingSign,hcros,hdet]

theorem not_segmentsCrossProperly_of_same_side (a b c d : Plane)
    (hside : (0 < orient2 a b c ∧ 0 < orient2 a b d) ∨
      (orient2 a b c < 0 ∧ orient2 a b d < 0)) : ¬ SegmentsCrossProperly a b c d := by
  rintro ⟨_,t,ht,u,hu,he⟩
  have hzero := congrArg (orient2 a b) he
  rw [orient2_self_segment,orient2_segment] at hzero
  have hpos : 0 < 1-u := by linarith [hu.2]
  rcases hside with ⟨hc,hd⟩ | ⟨hc,hd⟩
  · have := add_pos (mul_pos hpos hc) (mul_pos hu.1 hd)
    linarith
  · have := add_neg (mul_neg_of_pos_of_neg hpos hc) (mul_neg_of_pos_of_neg hu.1 hd)
    linarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CircleChords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem circle_denominator_pos (t : ℝ) : 0 < 1+t^2 := by nlinarith [sq_nonneg t]

theorem circlePoint_on_unit_circle (t : ℝ) : (circlePoint t).1^2+(circlePoint t).2^2 = 1 := by
  have h := ne_of_gt (circle_denominator_pos t)
  dsimp [circlePoint]
  field_simp
  ring

theorem circlePoint_parameter (t : ℝ) : (circlePoint t).2/(1+(circlePoint t).1) = t := by
  have h := ne_of_gt (circle_denominator_pos t)
  have hden : 1+(circlePoint t).1 = 2/(1+t^2) := by
    dsimp [circlePoint]
    field_simp
    ring
  rw [hden]
  dsimp [circlePoint]
  field_simp

theorem circle_orient_formula (a b c : ℝ) :
    orient2 (circlePoint a) (circlePoint b) (circlePoint c) =
      4*(b-a)*(c-a)*(c-b)/((1+a^2)*(1+b^2)*(1+c^2)) := by
  have ha := ne_of_gt (circle_denominator_pos a)
  have hb := ne_of_gt (circle_denominator_pos b)
  have hc := ne_of_gt (circle_denominator_pos c)
  dsimp [orient2,det2,circlePoint]
  field_simp
  ring

theorem circle_orient_pos (a b c : ℝ) (hab : a<b) (hbc : b<c) :
    0 < orient2 (circlePoint a) (circlePoint b) (circlePoint c) := by
  rw [circle_orient_formula]
  exact div_pos
    (mul_pos (mul_pos (mul_pos (by norm_num) (sub_pos.mpr hab))
      (sub_pos.mpr (hab.trans hbc))) (sub_pos.mpr hbc))
    (mul_pos (mul_pos (circle_denominator_pos a) (circle_denominator_pos b)) (circle_denominator_pos c))

theorem orient2_cycle (a b c : Plane) : orient2 b c a = orient2 a b c := by
  dsimp [orient2,det2]
  ring

theorem orient2_swap_ends (a b c : Plane) : orient2 a c b = -orient2 a b c := by
  exact det2_swap (b-a) (c-a)

theorem circle_chords_alternating_positive (a c b d : ℝ) (hac : a<c) (hcb : c<b) (hbd : b<d) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) = 1 := by
  apply segmentCrossingSign_of_positive_sides
  · rw [orient2_swap_ends]
    exact neg_neg_of_pos (circle_orient_pos a c b hac hcb)
  · exact circle_orient_pos a b d (hac.trans hcb) hbd
  · rw [orient2_cycle]
    exact circle_orient_pos a c d hac (hcb.trans hbd)
  · rw [orient2_swap_ends]
    exact neg_neg_of_pos (circle_orient_pos c b d hcb hbd)

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

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem polygonIntersection_swap (v w : ℕ → Plane) (n m : ℕ) :
    polygonIntersection w v m n = -polygonIntersection v w n m := by
  unfold polygonIntersection
  rw [Finset.sum_comm]
  calc
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
        -segmentCrossingSign (v i) (v (i+1)) (w j) (w (j+1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact segmentCrossingSign_swap _ _ _ _
    _ = _ := by simp only [Finset.sum_neg_distrib]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem polygonIntersection_join_left (v w z : ℕ → Plane) (n m k : ℕ) (h : v n=w 0) :
    polygonIntersection (joinedSequence v w n) z (n+m) k =
      polygonIntersection v z n k+polygonIntersection w z m k := by
  unfold polygonIntersection
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hin := Finset.mem_range.mp hi
    rw [joinedSequence_left v w n h i (by omega),joinedSequence_left v w n h (i+1) (by omega)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [joinedSequence_right,show n+i+1=n+(i+1) by omega,joinedSequence_right]

theorem polygonIntersection_join_right (v w z : ℕ → Plane) (n m k : ℕ) (h : w m=z 0) :
    polygonIntersection v (joinedSequence w z m) n (m+k) =
      polygonIntersection v w n m+polygonIntersection v z n k := by
  have hh := polygonIntersection_join_left w z v m k n h
  rw [polygonIntersection_swap v (joinedSequence w z m) n (m+k),
    polygonIntersection_swap v w n m,polygonIntersection_swap v z n k] at hh
  linarith

theorem polygonIntersection_reverse_left (v w : ℕ → Plane) (n m : ℕ) :
    polygonIntersection (reversedSequence v n) w n m = -polygonIntersection v w n m := by
  unfold polygonIntersection
  have he : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
      segmentCrossingSign (v (n-1-i)) (v (n-1-i+1)) (w j) (w (j+1))) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
        segmentCrossingSign (v i) (v (i+1)) (w j) (w (j+1)) :=
    Finset.sum_range_reflect (fun i => ∑ j ∈ Finset.range m,
      segmentCrossingSign (v i) (v (i+1)) (w j) (w (j+1))) n
  rw [← he,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hin := Finset.mem_range.mp hi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have h₀ : n-i=n-1-i+1 := by omega
  have h₁ : n-(i+1)=n-1-i := by omega
  simp only [reversedSequence,h₀,h₁]
  exact segmentCrossingSign_reverse_left _ _ _ _

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

end PolygonalChain
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

theorem PolygonalChain.piece_subset_path_range {O : Set Plane} {a b : Plane}
    (P : PolygonalChain O a b) (i : ℕ) (hi : i < P.pieces) :
    segment ℝ (P.vertices i) (P.vertices (i+1)) ⊆ Set.range P.path := by
  exact polygonalArcPath_piece_subset_range P.vertices P.pieces i hi

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
-- module Solutions.OAIB3_Zar.Crossing_TransversalityStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology Classical

theorem segmentPairTransverse_swap (a b c d : Plane) (h : SegmentPairTransverse a b c d) :
    SegmentPairTransverse c d a b := by
  intro t ht u hu he
  obtain ⟨hn,hu',ht'⟩ := h u hu t ht he.symm
  refine ⟨?_,ht',hu'⟩
  rw [det2_swap]
  exact neg_ne_zero.mpr hn

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalChainComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b c : Plane}

theorem intersection_join_left (P : PolygonalChain O a b) (Q : PolygonalChain O b c)
    (w : ℕ → Plane) (k : ℕ) :
    polygonIntersection (P.join Q).vertices w (P.join Q).pieces k=
      polygonIntersection P.vertices w P.pieces k+polygonIntersection Q.vertices w Q.pieces k :=
  polygonIntersection_join_left _ _ _ _ _ _ (P.last.trans Q.first.symm)

theorem intersection_join_right (P : PolygonalChain O a b) (Q : PolygonalChain O b c)
    (w : ℕ → Plane) (k : ℕ) :
    polygonIntersection w (P.join Q).vertices k (P.join Q).pieces=
      polygonIntersection w P.vertices k P.pieces+polygonIntersection w Q.vertices k Q.pieces :=
  polygonIntersection_join_right _ _ _ _ _ _ (P.last.trans Q.first.symm)

theorem intersection_reverse_left (P : PolygonalChain O a b) (w : ℕ → Plane) (k : ℕ) :
    polygonIntersection P.reverse.vertices w P.reverse.pieces k = -polygonIntersection P.vertices w P.pieces k :=
  polygonIntersection_reverse_left _ _ _ _

theorem intersection_reverse_right (P : PolygonalChain O a b) (w : ℕ → Plane) (k : ℕ) :
    polygonIntersection w P.reverse.vertices k P.reverse.pieces = -polygonIntersection w P.vertices k P.pieces := by
  rw [polygonIntersection_swap,P.intersection_reverse_left,polygonIntersection_swap]
  ring

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalChainTransversality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O T : Set Plane} {a b c d e : Plane}

theorem transverse_swap (P : PolygonalChain O a b) (Q : PolygonalChain T d e)
    (h : P.Transverse Q) : Q.Transverse P :=
  fun j i => segmentPairTransverse_swap _ _ _ _ (h i j)

theorem transverse_join_left (P : PolygonalChain O a b) (Q : PolygonalChain O b c)
    (R : PolygonalChain T d e) (hP : P.Transverse R) (hQ : Q.Transverse R) :
    (P.join Q).Transverse R := by
  intro i j
  change SegmentPairTransverse (joinedSequence P.vertices Q.vertices P.pieces i.val)
    (joinedSequence P.vertices Q.vertices P.pieces (i.val+1)) _ _
  have hi : i.val<P.pieces+Q.pieces := i.isLt
  by_cases hip : i.val<P.pieces
  · rw [joinedSequence_left _ _ _ (P.last.trans Q.first.symm) i.val hip.le,
      joinedSequence_left _ _ _ (P.last.trans Q.first.symm) (i.val+1) (by omega)]
    exact hP ⟨i.val,hip⟩ j
  · have he : i.val=P.pieces+(i.val-P.pieces) := by omega
    have he' : i.val+1=P.pieces+(i.val-P.pieces+1) := by omega
    have h₀ : joinedSequence P.vertices Q.vertices P.pieces i.val=Q.vertices (i.val-P.pieces) := by
      conv_lhs => rw [he]
      exact joinedSequence_right _ _ _ _
    have h₁ : joinedSequence P.vertices Q.vertices P.pieces (i.val+1)=Q.vertices (i.val-P.pieces+1) := by
      rw [he',joinedSequence_right]
    rw [h₀,h₁]
    exact hQ ⟨i.val-P.pieces,by omega⟩ j

theorem transverse_join_right (P : PolygonalChain O a b) (Q : PolygonalChain O b c)
    (R : PolygonalChain T d e) (hP : R.Transverse P) (hQ : R.Transverse Q) :
    R.Transverse (P.join Q) :=
  (P.join Q).transverse_swap R (P.transverse_join_left Q R (R.transverse_swap P hP) (R.transverse_swap Q hQ))

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SegmentTraversalReversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segmentPairTransverse_of_not_meet (a b c d : Plane) (h : ¬ ClosedSegmentsMeet a b c d) :
    SegmentPairTransverse a b c d := by
  intro s hs t ht he
  exact False.elim (h ⟨s,hs,t,ht,he⟩)

theorem segmentCrossingSign_eq_zero_of_not_meet (a b c d : Plane) (h : ¬ ClosedSegmentsMeet a b c d) :
    segmentCrossingSign a b c d=0 := by
  have hn : ¬ SegmentsCrossProperly a b c d := fun hh => h (closedSegmentsMeet_of_proper _ _ _ _ hh)
  simp [segmentCrossingSign,hn]

theorem segmentPairTransverse_reverse_left (a b c d : Plane) (h : SegmentPairTransverse a b c d) :
    SegmentPairTransverse b a c d := by
  intro s hs t ht he
  have hs' : 1-s ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have he' : segmentPoint a b (1-s)=segmentPoint c d t := (segmentPoint_reverse b a s).trans he
  obtain ⟨hdet,hsp,htp⟩ := h (1-s) hs' t ht he'
  refine ⟨?_,⟨by linarith [hsp.2],by linarith [hsp.1]⟩,htp⟩
  have hab : a-b=-(b-a) := by abel
  rw [hab,det2_neg_left]
  exact neg_ne_zero.mpr hdet

namespace PolygonalChain
variable {O T : Set Plane} {a b c d : Plane}

theorem transverse_reverse_left (P : PolygonalChain O a b) (Q : PolygonalChain T c d)
    (h : P.Transverse Q) : P.reverse.Transverse Q := by
  intro i j
  have hi : i.val<P.pieces := i.isLt
  have h₀ : P.pieces-i.val=P.pieces-1-i.val+1 := by omega
  have h₁ : P.pieces-(i.val+1)=P.pieces-1-i.val := by omega
  change SegmentPairTransverse (P.vertices (P.pieces-i.val)) (P.vertices (P.pieces-(i.val+1))) _ _
  rw [h₀,h₁]
  exact segmentPairTransverse_reverse_left _ _ _ _ (h ⟨P.pieces-1-i.val,by omega⟩ j)

theorem transverse_reverse_right (P : PolygonalChain O a b) (Q : PolygonalChain T c d)
    (h : P.Transverse Q) : P.Transverse Q.reverse :=
  Q.reverse.transverse_swap P (Q.transverse_reverse_left P (P.transverse_swap Q h))

end PolygonalChain
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CircleParameterChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem circlePoint_one_add_x (t : ℝ) : 1+(circlePoint t).1 = 2/(1+t^2) := by
  have h := ne_of_gt (circle_denominator_pos t)
  dsimp [circlePoint]
  field_simp
  ring

theorem circlePoint_avoids_cut (t : ℝ) : (circlePoint t).1 ≠ -1 := by
  have hh : 0 < 1+(circlePoint t).1 := by
    rw [circlePoint_one_add_x]
    exact div_pos (by norm_num) (circle_denominator_pos t)
  linarith

theorem circlePoint_surjective_away_cut (z : Plane) (hz : z.1^2+z.2^2 = 1) (hcut : z.1 ≠ -1) :
    circlePoint (z.2/(1+z.1)) = z := by
  have hx : 0 < 1+z.1 := by
    have hy := sq_nonneg z.2
    have hnonneg : 0 ≤ 1+z.1 := by nlinarith
    rcases hnonneg.eq_or_lt with he | he
    · exfalso
      apply hcut
      linarith
    · exact he
  have hxn := ne_of_gt hx
  have hden : 1+(z.2/(1+z.1))^2 = 2/(1+z.1) := by
    field_simp
    nlinarith
  apply Prod.ext
  · change (1-(z.2/(1+z.1))^2)/(1+(z.2/(1+z.1))^2) = z.1
    rw [hden]
    field_simp
    nlinarith [congrArg (fun t : ℝ => (1+z.1)*t) hz]
  · change (2*(z.2/(1+z.1)))/(1+(z.2/(1+z.1))^2) = z.2
    rw [hden]
    field_simp

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CircleOffset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem circleOffset_on_circle (u : Plane) (hu : squaredLength u=1) (δ : ℝ) (hδ : |δ|≤1) :
    squaredLength (circleOffset u δ)=1 := by
  have hnon : 0 ≤ 1-δ^2 := by
    have h := abs_le.mp hδ
    nlinarith
  have hs := Real.sq_sqrt hnon
  have he : squaredLength (circleOffset u δ)=
      ((Real.sqrt (1-δ^2))^2+δ^2)*squaredLength u := by
    dsimp [squaredLength,circleOffset,rotateQuarter]
    ring
  rw [he,hu,hs]
  ring

theorem circleOffset_side (u : Plane) (hu : squaredLength u=1) (δ : ℝ) :
    det2 u (circleOffset u δ)=δ := by
  dsimp [circleOffset,det2,rotateQuarter,squaredLength] at *
  linear_combination δ*hu

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CircleDeterminantOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem circle_det_formula (a b : ℝ) :
    det2 (circlePoint a) (circlePoint b) =
      2*(b-a)*(1+a*b)/((1+a^2)*(1+b^2)) := by
  have ha := ne_of_gt (circle_denominator_pos a)
  have hb := ne_of_gt (circle_denominator_pos b)
  dsimp [det2,circlePoint]
  field_simp
  ring

theorem circle_det_pos_iff (a b : ℝ) (h : 0<1+a*b) :
    0<det2 (circlePoint a) (circlePoint b) ↔ a<b := by
  rw [circle_det_formula,div_pos_iff_of_pos_right (mul_pos (circle_denominator_pos a) (circle_denominator_pos b)),
    mul_pos_iff_of_pos_right h,mul_pos_iff_of_pos_left (show (0 : ℝ)<2 by norm_num),sub_pos]

theorem circle_det_neg_iff (a b : ℝ) (h : 0<1+a*b) :
    det2 (circlePoint a) (circlePoint b)<0 ↔ b<a := by
  have hh : 0<1+b*a := by nlinarith
  have he := circle_det_pos_iff b a hh
  rw [det2_swap,neg_pos] at he
  exact he

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CircleOffsetParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem continuous_circleOffset (u : Plane) : Continuous (circleOffset u) := by
  change Continuous (fun δ : ℝ => Real.sqrt (1-δ^2) • u+δ • rotateQuarter u)
  fun_prop

@[simp] theorem offsetParameter_zero (a : ℝ) : offsetParameter a 0=a := by
  simp only [offsetParameter,circleOffset_zero,circlePoint_parameter]

theorem continuousAt_offsetParameter_zero (a : ℝ) : ContinuousAt (offsetParameter a) 0 := by
  apply ContinuousAt.div
  · exact (continuous_circleOffset (circlePoint a)).continuousAt.snd
  · exact continuousAt_const.add (continuous_circleOffset (circlePoint a)).continuousAt.fst
  · rw [circleOffset_zero,circlePoint_one_add_x]
    exact div_ne_zero (by norm_num) (ne_of_gt (circle_denominator_pos a))

theorem exists_circle_offset_parameter_radius (a ε : ℝ) (hε : 0<ε) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ δ : ℝ, |δ|<ρ →
      circlePoint (offsetParameter a δ)=circleOffset (circlePoint a) δ ∧
      |offsetParameter a δ-a|<ε ∧
      (0<δ → a<offsetParameter a δ) ∧ (δ<0 → offsetParameter a δ<a) := by
  have hp := continuousAt_offsetParameter_zero a
  have hnear : ∀ᶠ δ : ℝ in 𝓝 0, offsetParameter a δ ∈ Set.Ioo (a-ε) (a+ε) :=
    hp.eventually (isOpen_Ioo.mem_nhds (by rw [offsetParameter_zero]; constructor <;> linarith))
  have hsmall : ∀ᶠ δ : ℝ in 𝓝 0, |δ|<1 := by
    apply Metric.eventually_nhds_iff.mpr
    exact ⟨1,by norm_num,by intro delta; simp [Real.dist_eq]⟩
  have hcut : ∀ᶠ δ : ℝ in 𝓝 0, (circleOffset (circlePoint a) δ).1 ≠ -1 :=
    (continuous_circleOffset (circlePoint a)).continuousAt.fst.eventually_ne
      (by simpa using circlePoint_avoids_cut a)
  have hprodcont : ContinuousAt (fun δ : ℝ => 1+a*offsetParameter a δ) 0 :=
    continuousAt_const.add (continuousAt_const.mul hp)
  have hprod : ∀ᶠ δ : ℝ in 𝓝 0, 0<1+a*offsetParameter a δ :=
    continuousAt_const.eventually_lt hprodcont (by rw [offsetParameter_zero]; nlinarith [sq_nonneg a])
  have hevent : ∀ᶠ δ : ℝ in 𝓝 0,
      circlePoint (offsetParameter a δ)=circleOffset (circlePoint a) δ ∧
      |offsetParameter a δ-a|<ε ∧
      (0<δ → a<offsetParameter a δ) ∧ (δ<0 → offsetParameter a δ<a) := by
    filter_upwards [hnear,hsmall,hcut,hprod] with δ hnear hsmall hcut hprod
    have hunit : squaredLength (circlePoint a)=1 := circlePoint_on_unit_circle a
    have he := circlePoint_surjective_away_cut (circleOffset (circlePoint a) δ)
      (circleOffset_on_circle _ hunit δ hsmall.le) hcut
    change circlePoint (offsetParameter a δ)=circleOffset (circlePoint a) δ at he
    have hdet : det2 (circlePoint a) (circlePoint (offsetParameter a δ))=δ := by
      rw [he]
      exact circleOffset_side _ hunit δ
    refine ⟨he,?_,?_,?_⟩
    · exact abs_lt.mpr ⟨by linarith [hnear.1],by linarith [hnear.2]⟩
    · intro hδ
      apply (circle_det_pos_iff a _ hprod).mp
      rwa [hdet]
    · intro hδ
      apply (circle_det_neg_iff a _ hprod).mp
      rwa [hdet]
  obtain ⟨ρ,hρ,hh⟩ := Metric.eventually_nhds_iff.mp hevent
  exact ⟨ρ,hρ,fun δ hδ => hh (by simpa [Real.dist_eq] using hδ)⟩

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

theorem closedSegmentsMeet_symm (a b c d : Plane) : ClosedSegmentsMeet a b c d ↔ ClosedSegmentsMeet c d a b := by
  constructor <;> rintro ⟨t,ht,u,hu,he⟩ <;> exact ⟨u,hu,t,ht,he.symm⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_MovingSegmentStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem moving_endpoints_tendsto (C D : ℝ → Plane) (c d : Plane)
    (hC : ContinuousAt C 0) (hD : ContinuousAt D 0) (hC0 : C 0=c) (hD0 : D 0=d) :
    Filter.Tendsto (fun t : ℝ => (C t,D t)) (𝓝 0) (𝓝 (c,d)) := by
  simpa [ContinuousAt,hC0,hD0] using hC.prodMk hD

theorem eventually_moving_disjoint_segments (a b c d : Plane) (C D : ℝ → Plane)
    (hC : ContinuousAt C 0) (hD : ContinuousAt D 0) (hC0 : C 0=c) (hD0 : D 0=d)
    (h : ¬ ClosedSegmentsMeet a b c d) :
    ∀ᶠ t : ℝ in 𝓝 0, ¬ ClosedSegmentsMeet a b (C t) (D t) := by
  have hn : (c,d) ∈ {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 a b}ᶜ := by
    intro hx
    exact h ((closedSegmentsMeet_symm c d a b).mp hx)
  have he := (moving_endpoints_tendsto C D c d hC hD hC0 hD0).eventually
    ((isClosed_closedSegmentsMeet a b).isOpen_compl.mem_nhds hn)
  filter_upwards [he] with t ht
  intro hx
  exact ht ((closedSegmentsMeet_symm a b _ _).mp hx)

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
-- module Solutions.OAIB3_Zar.Crossing_OrientedSimilarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem similarityPoint_injective (o u : Plane) (hu : u ≠ 0) : Function.Injective (similarityPoint o u) := by
  intro x y he
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  dsimp [similarityPoint] at h₁ h₂
  have hs := ne_of_gt (squaredLength_pos u hu)
  have hx : squaredLength u*(x.1-y.1)=0 := by
    dsimp [squaredLength]
    linear_combination u.1*h₁+u.2*h₂
  have hy : squaredLength u*(x.2-y.2)=0 := by
    dsimp [squaredLength]
    linear_combination -u.2*h₁+u.1*h₂
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hs))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hs))

theorem similarityPoint_segment (o u a b : Plane) (t : ℝ) :
    similarityPoint o u (segmentPoint a b t) =
      segmentPoint (similarityPoint o u a) (similarityPoint o u b) t := by
  apply Prod.ext <;> dsimp [similarityPoint,segmentPoint] <;> ring

theorem similarityPoint_det (o u a b c d : Plane) :
    det2 (similarityPoint o u b-similarityPoint o u a)
      (similarityPoint o u d-similarityPoint o u c) = squaredLength u*det2 (b-a) (d-c) := by
  dsimp [similarityPoint,squaredLength,det2]
  ring

theorem segmentsCrossProperly_similarity (o u a b c d : Plane) (hu : u ≠ 0) :
    SegmentsCrossProperly (similarityPoint o u a) (similarityPoint o u b)
      (similarityPoint o u c) (similarityPoint o u d) ↔ SegmentsCrossProperly a b c d := by
  have hs := ne_of_gt (squaredLength_pos u hu)
  unfold SegmentsCrossProperly
  rw [similarityPoint_det,mul_ne_zero_iff]
  simp only [← similarityPoint_segment,(similarityPoint_injective o u hu).eq_iff]
  exact ⟨fun hh => ⟨hh.1.2,hh.2⟩,fun hh => ⟨⟨hs,hh.1⟩,hh.2⟩⟩

theorem segmentCrossingSign_similarity (o u a b c d : Plane) (hu : u ≠ 0) :
    segmentCrossingSign (similarityPoint o u a) (similarityPoint o u b)
      (similarityPoint o u c) (similarityPoint o u d) = segmentCrossingSign a b c d := by
  unfold segmentCrossingSign
  rw [segmentsCrossProperly_similarity o u a b c d hu]
  simp only [similarityPoint_det,mul_pos_iff_of_pos_left (squaredLength_pos u hu)]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FiniteScaledRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem finite_scaled_radius {ι : Type*} [Fintype ι] (a r : ι → ℝ) (hr : ∀ i, 0<r i) :
    ∃ δ : ℝ, 0<δ ∧ ∀ t : ℝ, |t|<δ → ∀ i, |a i*t|<r i := by
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ
    (fun i => r i/(|a i|+1)) (fun i _ => div_pos (hr i) (by positivity))
  refine ⟨δ,hδ,?_⟩
  intro t ht i
  have hd : 0 < |a i|+1 := by positivity
  have hb : δ*(|a i|+1)<r i := (lt_div_iff₀ hd).mp (hbound i (Finset.mem_univ _))
  calc
    |a i*t| = |t| *|a i| := by rw [abs_mul,mul_comm]
    _ ≤ |t| *(|a i|+1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
    _ < δ*(|a i|+1) := mul_lt_mul_of_pos_right ht hd
    _ < r i := hb

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ChordPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem chordEndpointPairing_reverse_left (a b c d : ℝ) :
    chordEndpointPairing b a c d = -chordEndpointPairing a b c d := by
  unfold chordEndpointPairing
  ring

theorem circle_chords_separated (a b c d : ℝ) (hab : a<b) (hbc : b<c) (hcd : c<d) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) = 0 := by
  have hh := not_segmentsCrossProperly_of_same_side (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d)
    (Or.inl ⟨circle_orient_pos a b c hab hbc,circle_orient_pos a b d hab (hbc.trans hcd)⟩)
  simp [segmentCrossingSign,hh]

theorem circle_chords_nested (a c d b : ℝ) (hac : a<c) (hcd : c<d) (hdb : d<b) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) = 0 := by
  have hc : orient2 (circlePoint a) (circlePoint b) (circlePoint c) < 0 := by
    rw [orient2_swap_ends]
    exact neg_neg_of_pos (circle_orient_pos a c b hac (hcd.trans hdb))
  have hd : orient2 (circlePoint a) (circlePoint b) (circlePoint d) < 0 := by
    rw [orient2_swap_ends]
    exact neg_neg_of_pos (circle_orient_pos a d b (hac.trans hcd) hdb)
  have hh := not_segmentsCrossProperly_of_same_side _ _ _ _ (Or.inr ⟨hc,hd⟩)
  simp [segmentCrossingSign,hh]

theorem circle_chord_pairing_ordered (a b c d : ℝ) (hab : a<b) (hcd : c<d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) =
      chordEndpointPairing a b c d := by
  by_cases hac' : a<c
  · by_cases hbc' : b<c
    · rw [circle_chords_separated a b c d hab hbc' hcd]
      unfold chordEndpointPairing orderSign
      split_ifs <;> norm_num <;> linarith
    · have hcb : c<b := lt_of_le_of_ne (le_of_not_gt hbc') (Ne.symm hbc)
      by_cases hbd' : b<d
      · rw [circle_chords_alternating_positive a c b d hac' hcb hbd']
        unfold chordEndpointPairing orderSign
        split_ifs <;> norm_num <;> linarith
      · have hdb : d<b := lt_of_le_of_ne (le_of_not_gt hbd') (Ne.symm hbd)
        rw [circle_chords_nested a c d b hac' hcd hdb]
        unfold chordEndpointPairing orderSign
        split_ifs <;> norm_num <;> linarith
  · have hca : c<a := lt_of_le_of_ne (le_of_not_gt hac') (Ne.symm hac)
    by_cases hda : d < a
    · rw [segmentCrossingSign_swap, circle_chords_separated c d a b hcd hda hab]
      unfold chordEndpointPairing orderSign
      split_ifs <;> norm_num <;> linarith
    · have had' : a<d := lt_of_le_of_ne (le_of_not_gt hda) had
      by_cases hdb : d < b
      · rw [segmentCrossingSign_swap, circle_chords_alternating_positive c a d b hca had' hdb]
        unfold chordEndpointPairing orderSign
        split_ifs <;> norm_num <;> linarith
      · have hbd' : b<d := lt_of_le_of_ne (le_of_not_gt hdb) hbd
        rw [segmentCrossingSign_swap, circle_chords_nested c a b d hca hab hbd']
        unfold chordEndpointPairing orderSign
        split_ifs <;> norm_num <;> linarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ChordOrientations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segmentCrossingSign_reverse_right (a b c d : Plane) :
    segmentCrossingSign a b d c = -segmentCrossingSign a b c d := by
  rw [segmentCrossingSign_swap d c a b,segmentCrossingSign_reverse_left c d a b,
    neg_neg,segmentCrossingSign_swap a b c d]

theorem chordEndpointPairing_reverse_right (a b c d : ℝ) :
    chordEndpointPairing a b d c = -chordEndpointPairing a b c d := by
  unfold chordEndpointPairing
  ring

theorem circle_chord_pairing_first_ordered (a b c d : ℝ) (hab : a<b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) =
      chordEndpointPairing a b c d := by
  rcases lt_or_gt_of_ne hcd with hcd | hdc
  · exact circle_chord_pairing_ordered a b c d hab hcd hac had hbc hbd
  · have hh := circle_chord_pairing_ordered a b d c hab hdc had hac hbd hbc
    rw [segmentCrossingSign_reverse_right, chordEndpointPairing_reverse_right] at hh
    exact neg_injective hh

theorem circle_chord_pairing (a b c d : ℝ) (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) =
      (orderSign a c-orderSign a d-orderSign b c+orderSign b d)/2 := by
  change _ = chordEndpointPairing a b c d
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact circle_chord_pairing_first_ordered a b c d hab hcd hac had hbc hbd
  · have hh := circle_chord_pairing_first_ordered b a c d hba hcd hbc hbd hac had
    rw [segmentCrossingSign_reverse_left, chordEndpointPairing_reverse_left] at hh
    exact neg_injective hh

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_GeneralOrderAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem orderSign_of_close (a b z ε : ℝ) (hgap : ε < |a-b|) (hz : |z-b| < ε) :
    orderSign a z = orderSign a b := by
  have ha : a ≠ b := by intro h; subst a; simp at hgap; have := abs_nonneg (z-b); linarith
  have hzb := abs_lt.mp hz
  rcases lt_or_gt_of_ne ha with hab | hba
  · have hgz : a < z := by rw [abs_of_neg (sub_neg.mpr hab)] at hgap; linarith
    simp [orderSign,hab,hgz]
  · have hgz : z < a := by rw [abs_of_pos (sub_pos.mpr hba)] at hgap; linarith
    simp [orderSign,not_lt.mpr hba.le,not_lt.mpr hgz.le,hba,hgz]

theorem orderSign_straddling_average (a b p q ε : ℝ)
    (hgap : a ≠ b → ε < |a-b|) (hp : |p-b| < ε) (hq : |q-b| < ε)
    (hstraddle : (p<b ∧ b<q) ∨ (q<b ∧ b<p)) :
    (orderSign a p+orderSign a q)/2 = orderSign a b := by
  by_cases hab : a=b
  · subst a
    rcases hstraddle with ⟨hp,hq⟩ | ⟨hq,hp⟩
    · simp [orderSign,hp,hq,not_lt.mpr hp.le]
    · simp [orderSign,hp,hq,not_lt.mpr hq.le]
  · rw [orderSign_of_close a b p ε (hgap hab) hp,orderSign_of_close a b q ε (hgap hab) hq]
    ring

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_GeneralSpokeAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {ι : Type*}

theorem small_perturbation_injective (node f : ι → ℝ)
    (ε : ℝ) (hgap : ∀ i j, i ≠ j → 2*ε < |node i-node j|)
    (hf : ∀ i, |f i-node i| < ε) : Function.Injective f := by
  intro i j hij
  by_contra hne
  have h₀ := hf i
  have h₁ := hf j
  have hh := abs_sub_le (node i) (f i) (node j)
  rw [abs_sub_comm (node i) (f i),hij] at hh
  have hg := hgap i j hne
  rw [hij] at h₀
  linarith

theorem fixed_node_ne_small_perturbation (node f : ι → ℝ)
    (ε : ℝ) (hε : 0<ε) (hgap : ∀ i j, i ≠ j → 2*ε < |node i-node j|)
    (hf : ∀ i, |f i-node i| < ε) (hself : ∀ i, node i ≠ f i) (i j : ι) : node i ≠ f j := by
  by_cases hij : i=j
  · subst j
    exact hself i
  · intro he
    have hg := hgap i j hij
    have hh := hf j
    rw [← he] at hh
    linarith

theorem local_spoke_straddling_average (node plus minus : ι → ℝ) (hn : Function.Injective node)
    (ε : ℝ) (hε : 0<ε) (hgap : ∀ i j, i ≠ j → 2*ε < |node i-node j|)
    (hp : ∀ i, |plus i-node i| < ε) (hm : ∀ i, |minus i-node i| < ε)
    (hs : ∀ i, (plus i<node i ∧ node i< minus i) ∨ (minus i<node i ∧ node i<plus i))
    (a b c d : ι) (hab : a ≠ b) (hcd : c ≠ d) :
    (segmentCrossingSign (circlePoint (node a)) (circlePoint (node b))
        (circlePoint (plus c)) (circlePoint (plus d)) +
      segmentCrossingSign (circlePoint (node a)) (circlePoint (node b))
        (circlePoint (minus c)) (circlePoint (minus d))) / 2 =
      chordEndpointPairing (node a) (node b) (node c) (node d) := by
  have hpne (i : ι) : node i ≠ plus i := by
    rcases hs i with h | h
    · exact ne_of_gt h.1
    · exact ne_of_lt h.2
  have hmne (i : ι) : node i ≠ minus i := by
    rcases hs i with h | h
    · exact ne_of_lt h.2
    · exact ne_of_gt h.1
  have hpall := fixed_node_ne_small_perturbation node plus ε hε hgap hp hpne
  have hmall := fixed_node_ne_small_perturbation node minus ε hε hgap hm hmne
  have hpinj := small_perturbation_injective node plus ε hgap hp
  have hminj := small_perturbation_injective node minus ε hgap hm
  rw [circle_chord_pairing _ _ _ _ (hn.ne hab) (hpinj.ne hcd) (hpall a c) (hpall a d) (hpall b c) (hpall b d),
    circle_chord_pairing _ _ _ _ (hn.ne hab) (hminj.ne hcd) (hmall a c) (hmall a d) (hmall b c) (hmall b d)]
  have hav (i j : ι) : (orderSign (node i) (plus j)+orderSign (node i) (minus j))/2 = orderSign (node i) (node j) := by
    apply orderSign_straddling_average _ _ _ _ ε _ (hp j) (hm j) (hs j)
    intro hne
    have hg := hgap i j (fun he => hne (congrArg node he))
    linarith
  have h₁ := hav a c
  have h₂ := hav a d
  have h₃ := hav b c
  have h₄ := hav b d
  unfold chordEndpointPairing
  linarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PhysicalSpokeAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_physical_spoke_average (node scale : ι → ℝ) (hn : Function.Injective node)
    (hs : ∀ i, scale i ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ a b c d : ι, a ≠ b → c ≠ d →
      (segmentCrossingSign (circlePoint (node a)) (circlePoint (node b))
          (circleOffset (circlePoint (node c)) (scale c*t))
          (circleOffset (circlePoint (node d)) (scale d*t)) +
        segmentCrossingSign (circlePoint (node a)) (circlePoint (node b))
          (circleOffset (circlePoint (node c)) (scale c*(-t)))
          (circleOffset (circlePoint (node d)) (scale d*(-t)))) / 2 =
        chordEndpointPairing (node a) (node b) (node c) (node d) := by
  obtain ⟨γ,hγ,hgap⟩ := finite_node_separation node hn
  let ε := γ/3
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsep (i j : ι) (hij : i ≠ j) : 2*ε < |node i-node j| := by
    have hh := hgap i j hij
    dsimp [ε]
    linarith
  have hex (i : ι) := exists_circle_offset_parameter_radius (node i) ε hε
  choose radius hpos hprop using hex
  obtain ⟨δ,hδ,hbound⟩ := finite_scaled_radius scale radius hpos
  refine ⟨δ,hδ,?_⟩
  intro t ht htδ a b c d hab hcd
  have hbt : |t| < δ := by simpa [abs_of_pos ht] using htδ
  have hbmt : |-t| < δ := by simpa [abs_neg] using hbt
  let plus : ι → ℝ := fun i => offsetParameter (node i) (scale i*t)
  let minus : ι → ℝ := fun i => offsetParameter (node i) (scale i*(-t))
  have hp (i : ι) := hprop i (scale i*t) (hbound t hbt i)
  have hm (i : ι) := hprop i (scale i*(-t)) (hbound (-t) hbmt i)
  have hpnear (i : ι) : |plus i-node i| < ε := (hp i).2.1
  have hmnear (i : ι) : |minus i-node i| < ε := (hm i).2.1
  have hstraddle (i : ι) : (plus i<node i ∧ node i< minus i) ∨
      (minus i<node i ∧ node i<plus i) := by
    have hne : scale i*t ≠ 0 := mul_ne_zero (hs i) (ne_of_gt ht)
    rcases lt_or_gt_of_ne hne with hi | hi
    · exact Or.inl ⟨(hp i).2.2.2 hi,(hm i).2.2.1 (by nlinarith)⟩
    · exact Or.inr ⟨(hm i).2.2.2 (by nlinarith),(hp i).2.2.1 hi⟩
  have havg := local_spoke_straddling_average node plus minus hn ε hε hsep hpnear hmnear hstraddle a b c d hab hcd
  have hpe (i : ι) : circlePoint (plus i)=circleOffset (circlePoint (node i)) (scale i*t) := (hp i).1
  have hme (i : ι) : circlePoint (minus i)=circleOffset (circlePoint (node i)) (scale i*(-t)) := (hm i).1
  simpa only [hpe,hme] using havg

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PhysicalCircleAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem physical_spoke_average_in_similarity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o u : Plane) (hu : u ≠ 0) (node scale : ι → ℝ)
    (hn : Function.Injective node) (hs : ∀ i, scale i ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ a b c d : ι, a ≠ b → c ≠ d →
      (segmentCrossingSign
          (similarityPoint o u (circlePoint (node a))) (similarityPoint o u (circlePoint (node b)))
          (similarityPoint o u (circleOffset (circlePoint (node c)) (scale c*t)))
          (similarityPoint o u (circleOffset (circlePoint (node d)) (scale d*t))) +
        segmentCrossingSign
          (similarityPoint o u (circlePoint (node a))) (similarityPoint o u (circlePoint (node b)))
          (similarityPoint o u (circleOffset (circlePoint (node c)) (scale c*(-t))))
          (similarityPoint o u (circleOffset (circlePoint (node d)) (scale d*(-t))))) / 2 =
        chordEndpointPairing (node a) (node b) (node c) (node d) := by
  obtain ⟨δ,hδ,hh⟩ := exists_physical_spoke_average node scale hn hs
  refine ⟨δ,hδ,?_⟩
  intro t ht hsmall a b c d hab hcd
  simpa only [segmentCrossingSign_similarity o u _ _ _ _ hu] using hh t ht hsmall a b c d hab hcd

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CircleOffsetLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem similarity_circleOffset (o u v : Plane) (δ : ℝ) :
    similarityPoint o u (circleOffset v δ)-o =
      Real.sqrt (1-δ^2) • (similarityPoint o u v-o) +
        δ • rotateQuarter (similarityPoint o u v-o) := by
  apply Prod.ext <;> dsimp [similarityPoint,circleOffset,rotateQuarter] <;> ring

theorem rotated_parallel_det_ne_zero (d w : Plane) (hd : d ≠ 0) (hw : w ≠ 0)
    (hpar : det2 d w=0) : det2 d (rotateQuarter w) ≠ 0 := by
  have hp := vector_parallel_of_det_zero d w hd hpar
  have hc : dot2 d w/squaredLength d ≠ 0 := by
    intro h
    rw [h,zero_smul] at hp
    exact hw hp
  have he : det2 d (rotateQuarter w)=(dot2 d w/squaredLength d)*squaredLength d := by
    conv_lhs => rw [hp]
    dsimp [det2,rotateQuarter,squaredLength]
    ring
  rw [he]
  exact mul_ne_zero hc (ne_of_gt (squaredLength_pos d hd))

theorem circleTrackScale_ne_zero (d w : Plane) (hd : d ≠ 0) (hw : w ≠ 0)
    (hpar : det2 d w=0) : circleTrackScale d w ≠ 0 :=
  inv_ne_zero (rotated_parallel_det_ne_zero d w hd hw hpar)

theorem circleOffset_track_level (o u v d : Plane) (hd : d ≠ 0)
    (hw : similarityPoint o u v-o ≠ 0)
    (hpar : det2 d (similarityPoint o u v-o)=0) (ε : ℝ) :
    det2 d (similarityPoint o u (circleOffset v (circleTrackScale d (similarityPoint o u v-o)*ε))-
      similarityPoint o u v)=ε := by
  let w := similarityPoint o u v-o
  let δ := circleTrackScale d w*ε
  have he : similarityPoint o u (circleOffset v δ)-similarityPoint o u v =
      (Real.sqrt (1-δ^2)-1) • w+δ • rotateQuarter w := by
    have hh := similarity_circleOffset o u v δ
    calc
      _ = (similarityPoint o u (circleOffset v δ)-o)-(similarityPoint o u v-o) := by abel
      _ = Real.sqrt (1-δ^2) • w+δ • rotateQuarter w-w := by rw [hh]
      _ = _ := by rw [sub_smul,one_smul]; abel
  change det2 d (similarityPoint o u (circleOffset v δ)-similarityPoint o u v)=ε
  rw [he,det2_add_right,det2_smul_right,det2_smul_right,hpar,mul_zero,zero_add]
  have hn := rotated_parallel_det_ne_zero d w hd hw hpar
  dsimp [δ,circleTrackScale]
  field_simp

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

theorem drawingSpokePort_interior (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (j : BipartiteVertex m n) (e : IncidentEdges j) :
    drawingSpokePort D P r j e ∈ edgeInterior D e.val := by
  unfold drawingSpokePort
  split_ifs
  · exact drawing_chain_startPort_interior D e.val (P e.val) (hmin e.val) r hr (hshort e.val).1
  · exact drawing_chain_endPort_interior D e.val (P e.val) (hmin e.val) r hr (hshort e.val).2

theorem drawingSpokePort_circle (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (j : BipartiteVertex m n) (e : IncidentEdges j) :
    squaredLength (drawingSpokePort D P r j e-D.vertex j)=r^2 := by
  unfold drawingSpokePort
  split_ifs with h
  · simpa only [h] using drawing_chain_startPort_circle D e.val (P e.val) (hmin e.val) r
  · have he := e.property.resolve_left h
    simpa only [he] using drawing_chain_endPort_circle D e.val (P e.val) (hmin e.val) r

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SpokeTrackDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem drawingSpokeDirection_port_parallel (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (r : ℝ) (j : BipartiteVertex m n) (e : IncidentEdges j)
    (hpos : 0 < (P e.val).pieces) :
    det2 (drawingSpokeDirection D P j e) (drawingSpokePort D P r j e-D.vertex j)=0 := by
  unfold drawingSpokeDirection drawingSpokePort
  split_ifs with h
  · have hc : D.vertex j=(P e.val).vertices 0 := (congrArg D.vertex h).trans (P e.val).first.symm
    rw [hc]
    change det2 ((P e.val).vertices 1-(P e.val).vertices 0)
      (radialPort ((P e.val).vertices 0) ((P e.val).vertices 1) r-(P e.val).vertices 0)=0
    rw [radialPort_sub,det2_smul_right,det2_self,mul_zero]
  · have he := e.property.resolve_left h
    have hc : D.vertex j=(P e.val).vertices (P e.val).pieces :=
      (congrArg D.vertex he).trans (P e.val).last.symm
    rw [hc]
    simp only [trackDirection,PolygonalChain.endPort,
      show (P e.val).pieces-1+1=(P e.val).pieces by omega,radialPort_sub,det2_smul_right]
    have hn : (P e.val).vertices ((P e.val).pieces-1)-(P e.val).vertices (P e.val).pieces =
        -((P e.val).vertices (P e.val).pieces-(P e.val).vertices ((P e.val).pieces-1)) := by abel
    rw [hn,det2_neg_right,det2_self,neg_zero,mul_zero]

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
-- module Solutions.OAIB3_Zar.Crossing_VertexTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

namespace VertexTruncation
variable {D : ContinuousDrawing m n} (V : VertexTruncation D)

theorem range_subset_edgeInterior (e : BipartiteEdge m n) : Set.range (V.path e) ⊆ edgeInterior D e :=
  truncated_range_subset_edgeInterior D V.chain V.minimal V.radius V.radius_pos V.short V.piece_clearance e

theorem direction_ne_zero (e : BipartiteEdge m n) (i : ℕ) (hi : i < V.pieces e) :
    trackDirection (V.vertices e) i ≠ 0 :=
  (V.chain e).truncated_direction_ne_zero (V.minimal e) V.radius V.radius_pos (V.short e).1 (V.short e).2 i hi

end VertexTruncation
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

theorem crossing_free_disks {D : AdmissibleDrawing m n} (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (j : BipartiteVertex m n) :
    Disjoint (closedRoundDisk (D.vertex j) V.radius) (crossingPoints D.toContinuousDrawing) :=
  vertex_disks_crossing_free D hnorm V.chain V.radius V.piece_clearance j

end Zarankiewicz.VertexTruncation

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedSpokeDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

theorem spokeIndex_lt (j : BipartiteVertex m n) (e : IncidentEdges j) :
    V.spokeIndex j e < V.pieces e.val := by
  have hp := V.pieces_pos e.val
  unfold spokeIndex
  split_ifs <;> omega

theorem spokeDirection_ne_zero (j : BipartiteVertex m n) (e : IncidentEdges j) :
    V.spokeDirection j e ≠ 0 := V.direction_ne_zero e.val _ (V.spokeIndex_lt j e)

theorem spokeDirection_eq_scale (j : BipartiteVertex m n) (e : IncidentEdges j) :
    V.spokeDirection j e =
      (V.chain e.val).truncatedScale V.radius (V.spokeIndex j e) •
        drawingSpokeDirection D V.chain j e := by
  change trackDirection ((V.chain e.val).truncatedVertices V.radius) (V.spokeIndex j e)=_
  rw [(V.chain e.val).truncated_direction V.radius _ (V.spokeIndex_lt j e)]
  congr 1
  unfold spokeIndex drawingSpokeDirection
  split_ifs <;> rfl

theorem spokePort_circle (j : BipartiteVertex m n) (e : IncidentEdges j) :
    squaredLength (V.spokePort j e-D.vertex j)=V.radius^2 :=
  drawingSpokePort_circle D V.chain V.minimal V.radius j e

theorem spokePort_ne_center (j : BipartiteVertex m n) (e : IncidentEdges j) :
    V.spokePort j e-D.vertex j ≠ 0 := by
  intro h
  have hc := V.spokePort_circle j e
  rw [h] at hc
  have hz : squaredLength (0 : Plane)=0 := by simp [squaredLength]
  rw [hz] at hc
  nlinarith [V.radius_pos]

theorem spokeDirection_parallel (j : BipartiteVertex m n) (e : IncidentEdges j) :
    det2 (V.spokeDirection j e) (V.spokePort j e-D.vertex j)=0 := by
  rw [V.spokeDirection_eq_scale,det2_smul_left]
  have hp := drawingSpokeDirection_port_parallel D V.chain V.radius j e (V.pieces_pos e.val)
  change det2 (drawingSpokeDirection D V.chain j e) (V.spokePort j e-D.vertex j)=0 at hp
  rw [hp,mul_zero]

theorem spokeScale_ne_zero (j : BipartiteVertex m n) (e : IncidentEdges j) :
    V.spokeScale j e ≠ 0 :=
  circleTrackScale_ne_zero _ _ (V.spokeDirection_ne_zero j e)
    (V.spokePort_ne_center j e) (V.spokeDirection_parallel j e)

end Zarankiewicz.VertexTruncation

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedSpokeCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D : ContinuousDrawing m n}

namespace TruncatedSpokeCoordinates
variable {V : VertexTruncation D} (C : TruncatedSpokeCoordinates V)

theorem shiftedPort_level (j : BipartiteVertex m n) (e : IncidentEdges j) (ε : ℝ) :
    det2 (V.spokeDirection j e) (C.shiftedPort j e ε-V.spokePort j e)=ε := by
  have hh := circleOffset_track_level (D.vertex j) (C.frame j) (circlePoint (C.node j e))
    (V.spokeDirection j e) (V.spokeDirection_ne_zero j e)
    (by simpa only [C.point_eq] using V.spokePort_ne_center j e)
    (by simpa only [C.point_eq] using V.spokeDirection_parallel j e) ε
  simpa only [C.point_eq,VertexTruncation.spokeScale,shiftedPort] using hh

theorem exists_vertex_average_radius (j : BipartiteVertex m n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ a b c d : IncidentEdges j,
      a ≠ b → c ≠ d →
      (segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c t) (C.shiftedPort j d t)+
        segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c (-t)) (C.shiftedPort j d (-t)))/2 =
      chordEndpointPairing (C.node j a) (C.node j b) (C.node j c) (C.node j d) := by
  classical
  obtain ⟨δ,hδ,hh⟩ := physical_spoke_average_in_similarity (D.vertex j) (C.frame j) (C.frame_ne_zero j)
    (C.node j) (V.spokeScale j) (C.node_injective j) (V.spokeScale_ne_zero j)
  refine ⟨δ,hδ,?_⟩
  intro t ht hsmall a b c d hab hcd
  simpa only [C.point_eq,shiftedPort] using hh t ht hsmall a b c d hab hcd

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawnEdgeChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
namespace TruncatedSpokeCoordinates
variable {m n : ℕ} {D : ContinuousDrawing m n} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem shiftedEdgeChain_intersection_right (e : BipartiteEdge m n) (ε : ℝ)
    (w : ℕ → Plane) (k : ℕ) :
    polygonIntersection w (C.shiftedEdgeChain e ε).vertices k (C.shiftedEdgeChain e ε).pieces =
      polygonIntersection w (C.connectorChain (Sum.inl e.1) (V.leftIncident e) ε).vertices k 1 +
      polygonIntersection w (shiftedTrack (V.vertices e) (V.pieces e) ε) k (V.pieces e) -
      polygonIntersection w (C.connectorChain (Sum.inr e.2) (V.rightIncident e) ε).vertices k 1 := by
  unfold shiftedEdgeChain
  rw [PolygonalChain.intersection_join_right,PolygonalChain.intersection_join_right,
    PolygonalChain.intersection_reverse_right]
  rfl

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_StraightChainIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
open scoped BigOperators
variable {O T : Set Plane} {a b c d : Plane}

theorem intersection_single_right (P : PolygonalChain O a b) (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T) :
    polygonIntersection P.vertices (single T c d hc hcd).vertices P.pieces 1=
      ∑ i ∈ Finset.range P.pieces, segmentCrossingSign (P.vertices i) (P.vertices (i+1)) c d := by
  simp [polygonIntersection,single]

theorem intersection_single_left (P : PolygonalChain O a b) (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T) :
    polygonIntersection (single T c d hc hcd).vertices P.vertices 1 P.pieces=
      ∑ i ∈ Finset.range P.pieces, segmentCrossingSign c d (P.vertices i) (P.vertices (i+1)) := by
  simp [polygonIntersection,single]

theorem transverse_single_right (P : PolygonalChain O a b) (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T)
    (h : ∀ i : Fin P.pieces, SegmentPairTransverse (P.vertices i.val) (P.vertices (i.val+1)) c d) :
    P.Transverse (single T c d hc hcd) := by
  intro i j
  have hj : j.val=0 := by have hj : j.val<1 := j.isLt; omega
  simpa [single,hj] using h i

theorem transverse_single_left (P : PolygonalChain O a b) (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T)
    (h : ∀ i : Fin P.pieces, SegmentPairTransverse c d (P.vertices i.val) (P.vertices (i.val+1))) :
    (single T c d hc hcd).Transverse P :=
  P.transverse_swap _ (P.transverse_single_right hc hcd (fun i => segmentPairTransverse_swap _ _ _ _ (h i)))

theorem intersection_single_right_zero (P : PolygonalChain O a b) (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T)
    (h : ∀ i : Fin P.pieces, ¬ ClosedSegmentsMeet (P.vertices i.val) (P.vertices (i.val+1)) c d) :
    polygonIntersection P.vertices (single T c d hc hcd).vertices P.pieces 1=0 := by
  rw [P.intersection_single_right]
  apply Finset.sum_eq_zero
  intro i hi
  exact segmentCrossingSign_eq_zero_of_not_meet _ _ _ _ (h ⟨i,Finset.mem_range.mp hi⟩)

theorem intersection_single_single (ha : a ∈ O) (hab : segment ℝ a b ⊆ O)
    (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T) :
    polygonIntersection (single O a b ha hab).vertices (single T c d hc hcd).vertices 1 1=
      segmentCrossingSign a b c d := by simp [polygonIntersection,single]

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_StraightChainTransversality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
open scoped BigOperators
variable {O T : Set Plane} {a b c d : Plane}

theorem transverse_single_single (ha : a ∈ O) (hab : segment ℝ a b ⊆ O)
    (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T) (h : SegmentPairTransverse a b c d) :
    (single O a b ha hab).Transverse (single T c d hc hcd) := by
  intro i j
  have hi : i.val=0 := by have hh : i.val<1 := i.isLt; omega
  have hj : j.val=0 := by have hh : j.val<1 := j.isLt; omega
  simpa [single,hi,hj] using h

theorem intersection_single_left_zero (P : PolygonalChain O a b) (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T)
    (h : ∀ i : Fin P.pieces, ¬ ClosedSegmentsMeet c d (P.vertices i.val) (P.vertices (i.val+1))) :
    polygonIntersection (single T c d hc hcd).vertices P.vertices 1 P.pieces=0 := by
  rw [P.intersection_single_left]
  apply Finset.sum_eq_zero
  intro i hi
  exact segmentCrossingSign_eq_zero_of_not_meet _ _ _ _ (h ⟨i,Finset.mem_range.mp hi⟩)

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SpokeEndpointSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : ContinuousDrawing m n} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem continuous_shiftedPort (j : BipartiteVertex m n) (e : IncidentEdges j) :
    Continuous (C.shiftedPort j e) := by
  change Continuous (fun ε : ℝ => similarityPoint (D.vertex j) (C.frame j)
    (circleOffset (circlePoint (C.node j e)) (V.spokeScale j e*ε)))
  dsimp [similarityPoint,circleOffset,rotateQuarter]
  fun_prop

theorem shiftedPort_zero (j : BipartiteVertex m n) (e : IncidentEdges j) :
    C.shiftedPort j e 0=V.spokePort j e := by
  simp only [shiftedPort,mul_zero,circleOffset_zero,C.point_eq]

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedSignedIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
open scoped BigOperators
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

theorem piece_subset_range (e : BipartiteEdge m n) (i : ℕ) (hi : i<V.pieces e) :
    segment ℝ (V.vertices e i) (V.vertices e (i+1)) ⊆ Set.range (V.path e) := by
  exact ((V.chain e).truncated (V.pieces_pos e) V.radius V.radius_pos
    (V.weak_short e).1 (V.weak_short e).2).piece_subset_path_range i hi

end Zarankiewicz.VertexTruncation

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SpokePieceIsolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
variable {m n : ℕ}

theorem spokePort_interior {D : ContinuousDrawing m n} (V : VertexTruncation D)
    (j : BipartiteVertex m n) (f : IncidentEdges j) : V.spokePort j f ∈ edgeInterior D f.val :=
  drawingSpokePort_interior D V.chain V.minimal V.radius V.radius_pos V.weak_short j f

theorem spokePort_piece_unique {D : AdmissibleDrawing m n} (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (j : BipartiteVertex m n) (f : IncidentEdges j)
    (e : BipartiteEdge m n) (i : Fin (V.pieces e))
    (hx : V.spokePort j f ∈ segment ℝ (V.vertices e i.val) (V.vertices e (i.val+1))) :
    e=f.val ∧ i.val=V.spokeIndex j f := by
  have hcircle : V.spokePort j f ∈ closedRoundDisk (D.vertex j) V.radius := by
    change squaredLength (V.spokePort j f-D.vertex j) ≤ V.radius^2
    rw [V.spokePort_circle]
  have he : e=f.val := by
    by_contra hef
    have hcross : V.spokePort j f ∈ crossingPoints D.toContinuousDrawing :=
      ⟨e,f.val,hef,V.range_subset_edgeInterior e (V.piece_subset_range e i.val i.isLt hx),V.spokePort_interior j f⟩
    exact Set.disjoint_left.mp (V.crossing_free_disks hnorm j) hcircle hcross
  have hcase : (j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=V.pieces e) := by
    by_contra hh
    have hold := (V.chain e).truncated_piece_subset V.radius V.radius_pos
      (V.weak_short e).1 (V.weak_short e).2 i.val i.isLt hx
    exact Set.disjoint_left.mp (V.piece_clearance j e i hh) hcircle hold
  refine ⟨he,?_⟩
  unfold spokeIndex
  split_ifs with hj
  · rcases hcase with hh | hh
    · exact hh.2
    · have hbad : Sum.inl f.val.1=Sum.inr e.2 := hj.symm.trans hh.1
      cases hbad
  · rcases hcase with hh | hh
    · exact False.elim (hj (hh.1.trans (congrArg (fun g : BipartiteEdge m n => Sum.inl g.1) he)))
    · have hn : V.pieces e=V.pieces f.val := congrArg V.pieces he
      omega

end Zarankiewicz.VertexTruncation

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ConnectorSupportingLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem det2_segmentPoint_sub (d p a b : Plane) (t : ℝ) :
    det2 d (segmentPoint a b t-p)=(1-t)*det2 d (a-p)+t*det2 d (b-p) := by
  dsimp [det2,segmentPoint]
  ring

theorem segment_line_level_zero (a b p : Plane) (hp : p=a ∨ p=b) (t : ℝ) :
    det2 (b-a) (segmentPoint a b t-p)=0 := by
  rcases hp with rfl | rfl <;> dsimp [det2,segmentPoint] <;> ring

namespace VertexTruncation
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

theorem spokePort_is_piece_endpoint (j : BipartiteVertex m n) (e : IncidentEdges j) :
    V.spokePort j e=V.vertices e.val (V.spokeIndex j e) ∨
      V.spokePort j e=V.vertices e.val (V.spokeIndex j e+1) := by
  unfold spokePort drawingSpokePort spokeIndex
  split_ifs
  · exact Or.inl (V.vertices_first e.val).symm
  · right
    have hp := V.pieces_pos e.val
    rw [show V.pieces e.val-1+1=V.pieces e.val by omega]
    exact (V.vertices_last e.val).symm

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {m n : ℕ} {D : ContinuousDrawing m n} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem continuous_tangentPort (j : BipartiteVertex m n) (e : IncidentEdges j) :
    Continuous (C.tangentPort j e) := by
  change Continuous (fun ε : ℝ => V.spokePort j e+ε • normalShift (V.spokeDirection j e))
  fun_prop

theorem tangentPort_zero (j : BipartiteVertex m n) (e : IncidentEdges j) :
    C.tangentPort j e 0=V.spokePort j e := by simp [tangentPort]

theorem tangentPort_level (j : BipartiteVertex m n) (e : IncidentEdges j) (ε : ℝ) :
    det2 (V.spokeDirection j e) (C.tangentPort j e ε-V.spokePort j e)=ε := by
  simp only [tangentPort,add_sub_cancel_left,det2_smul_right,
    det2_normalShift _ (V.spokeDirection_ne_zero j e),mul_one]

theorem connector_level (j : BipartiteVertex m n) (e : IncidentEdges j) (ε t : ℝ) :
    det2 (V.spokeDirection j e)
      (segmentPoint (C.shiftedPort j e ε) (C.tangentPort j e ε) t-V.spokePort j e)=ε := by
  rw [det2_segmentPoint_sub,C.shiftedPort_level,C.tangentPort_level]
  ring

theorem connector_avoids_incident_piece (j : BipartiteVertex m n) (e : IncidentEdges j)
    (ε : ℝ) (hε : ε ≠ 0) :
    ¬ ClosedSegmentsMeet (V.vertices e.val (V.spokeIndex j e))
      (V.vertices e.val (V.spokeIndex j e+1)) (C.shiftedPort j e ε) (C.tangentPort j e ε) := by
  rintro ⟨s,hs,t,ht,he⟩
  have hzero := segment_line_level_zero (V.vertices e.val (V.spokeIndex j e))
    (V.vertices e.val (V.spokeIndex j e+1)) (V.spokePort j e) (V.spokePort_is_piece_endpoint j e) s
  change det2 (V.spokeDirection j e)
    (segmentPoint (V.vertices e.val (V.spokeIndex j e)) (V.vertices e.val (V.spokeIndex j e+1)) s-V.spokePort j e)=0 at hzero
  rw [he,C.connector_level] at hzero
  exact hε hzero

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_UniformSpokeRadii
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : ContinuousDrawing m n} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem exists_uniform_average_radius :
    ∃ δ : ℝ, 0<δ ∧ ∀ t : ℝ, 0<t → t<δ → ∀ j (a b c d : IncidentEdges j),
      a ≠ b → c ≠ d →
      (segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c t) (C.shiftedPort j d t)+
        segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c (-t)) (C.shiftedPort j d (-t)))/2 =
      chordEndpointPairing (C.node j a) (C.node j b) (C.node j c) (C.node j d) := by
  classical
  choose radius hpos hprop using C.exists_vertex_average_radius
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun j _ => hpos j)
  exact ⟨δ,hδ,fun t ht hsmall j => hprop j t ht (hsmall.trans (hbound j (Finset.mem_univ _)))⟩

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ConnectorTrackAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
open scoped Topology
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_nonincident_connector_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ j (f : IncidentEdges j) e (i : Fin (V.pieces e)),
      ¬ (e=f.val ∧ i.val=V.spokeIndex j f) →
      ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
        (C.shiftedPort j f ε) (C.tangentPort j f ε) := by
  classical
  let Bad := Σ j : BipartiteVertex m n, Σ f : IncidentEdges j, Σ e : BipartiteEdge m n,
    {i : Fin (V.pieces e) // ¬ (e=f.val ∧ i.val=V.spokeIndex j f)}
  have hnot (b : Bad) : ¬ ClosedSegmentsMeet
      (V.vertices b.2.2.1 b.2.2.2.val.val) (V.vertices b.2.2.1 (b.2.2.2.val.val+1))
      (V.spokePort b.1 b.2.1) (V.spokePort b.1 b.2.1) := by
    rintro ⟨s,hs,t,ht,he⟩
    have he0 : segmentPoint (V.spokePort b.1 b.2.1) (V.spokePort b.1 b.2.1) t=V.spokePort b.1 b.2.1 := by
      unfold segmentPoint
      rw [← add_smul]
      simp
    rw [he0] at he
    have hx : V.spokePort b.1 b.2.1 ∈
        segment ℝ (V.vertices b.2.2.1 b.2.2.2.val.val) (V.vertices b.2.2.1 (b.2.2.2.val.val+1)) := by
      rw [← Path.range_segment]
      refine ⟨⟨s,hs⟩,?_⟩
      simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he
    exact b.2.2.2.property (V.spokePort_piece_unique hnorm b.1 b.2.1 b.2.2.1 b.2.2.2.val hx)
  have hevent (b : Bad) := eventually_moving_disjoint_segments
    (V.vertices b.2.2.1 b.2.2.2.val.val) (V.vertices b.2.2.1 (b.2.2.2.val.val+1))
    (V.spokePort b.1 b.2.1) (V.spokePort b.1 b.2.1) (C.shiftedPort b.1 b.2.1) (C.tangentPort b.1 b.2.1)
    (C.continuous_shiftedPort b.1 b.2.1).continuousAt (C.continuous_tangentPort b.1 b.2.1).continuousAt
    (C.shiftedPort_zero b.1 b.2.1) (C.tangentPort_zero b.1 b.2.1) (hnot b)
  have hex (b : Bad) := Metric.eventually_nhds_iff.mp (hevent b)
  choose radius hpos hprop using hex
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun b _ => hpos b)
  refine ⟨δ,hδ,?_⟩
  intro ε hε j f e i hi
  exact hprop ⟨j,f,e,⟨i,hi⟩⟩ (by simpa [Real.dist_eq] using hε.trans (hbound ⟨j,f,e,⟨i,hi⟩⟩ (Finset.mem_univ _)))

theorem exists_all_connector_track_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j (f : IncidentEdges j) e (i : Fin (V.pieces e)),
      ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
        (C.shiftedPort j f ε) (C.tangentPort j f ε) := by
  obtain ⟨δ,hδ,hh⟩ := C.exists_nonincident_connector_radius hnorm
  refine ⟨δ,hδ,?_⟩
  intro ε hε hsmall j f e i
  by_cases hi : e=f.val ∧ i.val=V.spokeIndex j f
  · rcases hi with ⟨rfl,hi⟩
    simpa only [hi] using C.connector_avoids_incident_piece j f ε hε
  · exact hh ε hsmall j f e i hi

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ChordEdgeIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_chord_edge_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ →
      (∀ j (a b : IncidentEdges j) e,
        (V.chordChain j a b).Transverse (C.shiftedEdgeChain e ε) ∧
        polygonIntersection (V.chordChain j a b).vertices (C.shiftedEdgeChain e ε).vertices
          (V.chordChain j a b).pieces (C.shiftedEdgeChain e ε).pieces=0) ∧
      (∀ j (a b : IncidentEdges j) e,
        (V.trackChain e).Transverse (C.shiftedChordChain j a b ε) ∧
        polygonIntersection (V.trackChain e).vertices (C.shiftedChordChain j a b ε).vertices
          (V.trackChain e).pieces (C.shiftedChordChain j a b ε).pieces=0) := by
  obtain ⟨δ,hδ,hh⟩ := C.exists_cross_type_radius hnorm
  refine ⟨δ,hδ,?_⟩
  intro ε hε hsmall
  obtain ⟨hTC,hTChord,hChordT,hChordC,hChordChord,hOther⟩ := hh ε hε hsmall
  constructor
  · intro j a b e
    have hconn (k : BipartiteVertex m n) (f : IncidentEdges k) :
        (V.chordChain j a b).Transverse (C.connectorChain k f ε) := by
      apply PolygonalChain.transverse_single_single
      exact segmentPairTransverse_of_not_meet _ _ _ _ (hChordC j k a b f)
    have hmid : (V.chordChain j a b).Transverse (C.shiftedTrackChain e ε) := by
      apply PolygonalChain.transverse_single_left
      intro i
      exact segmentPairTransverse_of_not_meet _ _ _ _ (hChordT j a b e i)
    have hzconn (k : BipartiteVertex m n) (f : IncidentEdges k) :
        polygonIntersection (V.chordChain j a b).vertices (C.connectorChain k f ε).vertices 1 1=0 := by
      rw [VertexTruncation.chordChain,connectorChain,PolygonalChain.intersection_single_single]
      exact segmentCrossingSign_eq_zero_of_not_meet _ _ _ _ (hChordC j k a b f)
    have hzmid : polygonIntersection (V.chordChain j a b).vertices
        (shiftedTrack (V.vertices e) (V.pieces e) ε) 1 (V.pieces e)=0 := by
      apply (C.shiftedTrackChain e ε).intersection_single_left_zero
      intro i
      exact hChordT j a b e i
    constructor
    · change (V.chordChain j a b).Transverse
        (((C.connectorChain (Sum.inl e.1) (V.leftIncident e) ε).join (C.shiftedTrackChain e ε)).join
          (C.connectorChain (Sum.inr e.2) (V.rightIncident e) ε).reverse)
      apply PolygonalChain.transverse_join_right
      · exact PolygonalChain.transverse_join_right _ _ _ (hconn _ _) hmid
      · exact (V.chordChain j a b).transverse_reverse_right _ (hconn _ _)
    · change polygonIntersection (V.chordChain j a b).vertices (C.shiftedEdgeChain e ε).vertices 1 _=0
      rw [C.shiftedEdgeChain_intersection_right,hzconn,hzconn,hzmid]
      norm_num
  · intro j a b e
    constructor
    · apply PolygonalChain.transverse_single_right
      intro i
      exact segmentPairTransverse_of_not_meet _ _ _ _ (hTChord j a b e i)
    · apply PolygonalChain.intersection_single_right_zero
      intro i
      exact hTChord j a b e i

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DartCyclePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem dartPassage_ne (d : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (i : ℕ)
    (hne : bipartiteDartEdge (d (i+1)) ≠ bipartiteDartEdge (d i)) :
    dartTargetIncident (d i) ≠ dartPassageNext d hd i := by
  intro he
  exact hne (congrArg Subtype.val he).symm

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ShiftedEdgeIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_complete_edge_intersection_radius (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ e f : BipartiteEdge m n,
      (V.trackChain e).Transverse (C.shiftedEdgeChain f ε) ∧
      polygonIntersection (V.trackChain e).vertices (C.shiftedEdgeChain f ε).vertices
        (V.trackChain e).pieces (C.shiftedEdgeChain f ε).pieces=V.signedIntersection e f := by
  obtain ⟨δ₀,hδ₀,hT⟩ := V.exists_all_edge_shift_radius hnorm hstraight htrans
  obtain ⟨δ₁,hδ₁,hI⟩ := V.exists_uniform_track_intersections hnorm hstraight htrans
  obtain ⟨δ₂,hδ₂,hC⟩ := C.exists_all_connector_track_radius hnorm
  let δ := min δ₀ (min δ₁ δ₂)
  have hδ : 0<δ := lt_min hδ₀ (lt_min hδ₁ hδ₂)
  have hb₀ : δ≤δ₀ := min_le_left _ _
  have hb₁ : δ≤δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hb₂ : δ≤δ₂ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,hδ,?_⟩
  intro ε hε hsmall e f
  have hconn (j : BipartiteVertex m n) (g : IncidentEdges j) :
      (V.trackChain e).Transverse (C.connectorChain j g ε) := by
    apply PolygonalChain.transverse_single_right
    intro i
    exact segmentPairTransverse_of_not_meet _ _ _ _ (hC ε hε (hsmall.trans_le hb₂) j g e i)
  have hmid : (V.trackChain e).Transverse (C.shiftedTrackChain f ε) := by
    intro i j
    exact (hT ε hε (hsmall.trans_le hb₀) e f i j).1
  have hzero (j : BipartiteVertex m n) (g : IncidentEdges j) :
      polygonIntersection (V.trackChain e).vertices (C.connectorChain j g ε).vertices (V.trackChain e).pieces 1=0 := by
    apply PolygonalChain.intersection_single_right_zero
    intro i
    exact hC ε hε (hsmall.trans_le hb₂) j g e i
  constructor
  · change (V.trackChain e).Transverse
      (((C.connectorChain (Sum.inl f.1) (V.leftIncident f) ε).join (C.shiftedTrackChain f ε)).join
        (C.connectorChain (Sum.inr f.2) (V.rightIncident f) ε).reverse)
    apply PolygonalChain.transverse_join_right
    · exact PolygonalChain.transverse_join_right _ _ _ (hconn _ _) hmid
    · exact (V.trackChain e).transverse_reverse_right _ (hconn _ _)
  · rw [C.shiftedEdgeChain_intersection_right,hzero,hzero,zero_add,sub_zero]
    exact hI ε hε (hsmall.trans_le hb₁) e f

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DartPairIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem dart_pair_intersection {ε : ℝ} (a b : (completeBipartite m n).Dart)
    (h : ∀ e f, (V.trackChain e).Transverse (C.shiftedEdgeChain f ε) ∧
      polygonIntersection (V.trackChain e).vertices (C.shiftedEdgeChain f ε).vertices
        (V.trackChain e).pieces (C.shiftedEdgeChain f ε).pieces=V.signedIntersection e f) :
    (V.dartTrackChain a).Transverse (C.shiftedDartChain b ε) ∧
      polygonIntersection (V.dartTrackChain a).vertices (C.shiftedDartChain b ε).vertices
        (V.dartTrackChain a).pieces (C.shiftedDartChain b ε).pieces=
          bipartiteDartSign a*bipartiteDartSign b*V.signedIntersection (bipartiteDartEdge a) (bipartiteDartEdge b) := by
  rcases bipartiteDart_cases a with ⟨e,rfl⟩ | ⟨e,rfl⟩ <;>
    rcases bipartiteDart_cases b with ⟨f,rfl⟩ | ⟨f,rfl⟩
  · obtain ⟨hT,hI⟩ := h e f
    refine ⟨hT,?_⟩
    change polygonIntersection (V.trackChain e).vertices (C.shiftedEdgeChain f ε).vertices
      (V.trackChain e).pieces (C.shiftedEdgeChain f ε).pieces=1*1*V.signedIntersection e f
    simpa only [one_mul] using hI
  · obtain ⟨hT,hI⟩ := h e f
    refine ⟨(V.trackChain e).transverse_reverse_right _ hT,?_⟩
    change polygonIntersection (V.trackChain e).vertices (C.shiftedEdgeChain f ε).reverse.vertices
      (V.trackChain e).pieces (C.shiftedEdgeChain f ε).reverse.pieces=1*(-1)*V.signedIntersection e f
    rw [PolygonalChain.intersection_reverse_right,hI]
    ring
  · obtain ⟨hT,hI⟩ := h e f
    refine ⟨(V.trackChain e).transverse_reverse_left _ hT,?_⟩
    change polygonIntersection (V.trackChain e).reverse.vertices (C.shiftedEdgeChain f ε).vertices
      (V.trackChain e).reverse.pieces (C.shiftedEdgeChain f ε).pieces=(-1)*1*V.signedIntersection e f
    rw [PolygonalChain.intersection_reverse_left,hI]
    ring
  · obtain ⟨hT,hI⟩ := h e f
    refine ⟨(V.trackChain e).reverse.transverse_reverse_right _
      ((V.trackChain e).transverse_reverse_left _ hT),?_⟩
    change polygonIntersection (V.trackChain e).reverse.vertices (C.shiftedEdgeChain f ε).reverse.vertices
      (V.trackChain e).reverse.pieces (C.shiftedEdgeChain f ε).reverse.pieces=(-1)*(-1)*V.signedIntersection e f
    rw [PolygonalChain.intersection_reverse_left,PolygonalChain.intersection_reverse_right,hI]
    ring

theorem chord_dart_intersection {ε : ℝ} (j : BipartiteVertex m n) (a b : IncidentEdges j)
    (d : (completeBipartite m n).Dart)
    (h : ∀ e, (V.chordChain j a b).Transverse (C.shiftedEdgeChain e ε) ∧
      polygonIntersection (V.chordChain j a b).vertices (C.shiftedEdgeChain e ε).vertices
        (V.chordChain j a b).pieces (C.shiftedEdgeChain e ε).pieces=0) :
    (V.chordChain j a b).Transverse (C.shiftedDartChain d ε) ∧
      polygonIntersection (V.chordChain j a b).vertices (C.shiftedDartChain d ε).vertices
        (V.chordChain j a b).pieces (C.shiftedDartChain d ε).pieces=0 := by
  rcases bipartiteDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩
  · exact h e
  · obtain ⟨hT,hI⟩ := h e
    refine ⟨(V.chordChain j a b).transverse_reverse_right _ hT,?_⟩
    change polygonIntersection (V.chordChain j a b).vertices (C.shiftedEdgeChain e ε).reverse.vertices
      (V.chordChain j a b).pieces (C.shiftedEdgeChain e ε).reverse.pieces=0
    rw [PolygonalChain.intersection_reverse_right,hI,neg_zero]

theorem dart_chord_intersection {ε : ℝ} (j : BipartiteVertex m n) (a b : IncidentEdges j)
    (d : (completeBipartite m n).Dart)
    (h : ∀ e, (V.trackChain e).Transverse (C.shiftedChordChain j a b ε) ∧
      polygonIntersection (V.trackChain e).vertices (C.shiftedChordChain j a b ε).vertices
        (V.trackChain e).pieces (C.shiftedChordChain j a b ε).pieces=0) :
    (V.dartTrackChain d).Transverse (C.shiftedChordChain j a b ε) ∧
      polygonIntersection (V.dartTrackChain d).vertices (C.shiftedChordChain j a b ε).vertices
        (V.dartTrackChain d).pieces (C.shiftedChordChain j a b ε).pieces=0 := by
  rcases bipartiteDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩
  · exact h e
  · obtain ⟨hT,hI⟩ := h e
    refine ⟨(V.trackChain e).transverse_reverse_left _ hT,?_⟩
    change polygonIntersection (V.trackChain e).reverse.vertices (C.shiftedChordChain j a b ε).vertices
      (V.trackChain e).reverse.pieces (C.shiftedChordChain j a b ε).pieces=0
    rw [PolygonalChain.intersection_reverse_left,hI,neg_zero]

theorem exists_dart_intersection_radius (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε| < δ →
      (∀ a b : (completeBipartite m n).Dart,
        (V.dartTrackChain a).Transverse (C.shiftedDartChain b ε) ∧
        polygonIntersection (V.dartTrackChain a).vertices (C.shiftedDartChain b ε).vertices
          (V.dartTrackChain a).pieces (C.shiftedDartChain b ε).pieces=
            bipartiteDartSign a*bipartiteDartSign b*V.signedIntersection (bipartiteDartEdge a) (bipartiteDartEdge b)) ∧
      (∀ j (a b : IncidentEdges j) d,
        (V.chordChain j a b).Transverse (C.shiftedDartChain d ε) ∧
        polygonIntersection (V.chordChain j a b).vertices (C.shiftedDartChain d ε).vertices
          (V.chordChain j a b).pieces (C.shiftedDartChain d ε).pieces=0) ∧
      (∀ j (a b : IncidentEdges j) d,
        (V.dartTrackChain d).Transverse (C.shiftedChordChain j a b ε) ∧
        polygonIntersection (V.dartTrackChain d).vertices (C.shiftedChordChain j a b ε).vertices
          (V.dartTrackChain d).pieces (C.shiftedChordChain j a b ε).pieces=0) := by
  obtain ⟨δ₀,hδ₀,h₀⟩ := C.exists_complete_edge_intersection_radius hnorm hstraight htrans
  obtain ⟨δ₁,hδ₁,h₁⟩ := C.exists_chord_edge_radius hnorm
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro ε hε hs
  have he := h₀ ε hε (hs.trans_le (min_le_left _ _))
  obtain ⟨hcd,hdc⟩ := h₁ ε hε (hs.trans_le (min_le_right _ _))
  exact ⟨fun a b => C.dart_pair_intersection a b he,
    fun j a b d => C.chord_dart_intersection j a b d (hcd j a b),
    fun j a b d => C.dart_chord_intersection j a b d (hdc j a b)⟩

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_VertexChordIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem chordChain_intersection (j k : BipartiteVertex m n) (a b : IncidentEdges j)
    (c d : IncidentEdges k) (ε : ℝ) :
    polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain k c d ε).vertices 1 1=
      segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε) := by
  rw [VertexTruncation.chordChain,shiftedChordChain,PolygonalChain.intersection_single_single]

theorem exists_vertex_chord_chain_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧
      (∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j k (a b : IncidentEdges j) (c d : IncidentEdges k),
        a ≠ b → c ≠ d → (V.chordChain j a b).Transverse (C.shiftedChordChain k c d ε)) ∧
      (∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j k, j ≠ k → ∀ (a b : IncidentEdges j) (c d : IncidentEdges k),
        polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain k c d ε).vertices 1 1=0) ∧
      (∀ t : ℝ, 0<t → t<δ → ∀ j (a b c d : IncidentEdges j), a ≠ b → c ≠ d →
        (polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain j c d t).vertices 1 1+
          polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain j c d (-t)).vertices 1 1)/2=
            chordEndpointPairing (C.node j a) (C.node j b) (C.node j c) (C.node j d)) := by
  obtain ⟨δ₀,hδ₀,hgeo⟩ := C.exists_cross_type_radius hnorm
  obtain ⟨δ₁,hδ₁,havg⟩ := C.exists_uniform_average_radius
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_,?_,?_⟩
  · intro ε hε hsmall j k a b c d hab hcd
    have hh := (hgeo ε hε (hsmall.trans_le (min_le_left _ _))).2.2.2.2.1 j k a b c d hab hcd
    exact PolygonalChain.transverse_single_single _ _ _ _ hh
  · intro ε hε hsmall j k hjk a b c d
    rw [C.chordChain_intersection]
    exact segmentCrossingSign_eq_zero_of_not_meet _ _ _ _
      ((hgeo ε hε (hsmall.trans_le (min_le_left _ _))).2.2.2.2.2 j k hjk a b c d)
  · intro t ht hsmall j a b c d hab hcd
    rw [C.chordChain_intersection,C.chordChain_intersection]
    exact havg t ht (hsmall.trans_le (min_le_right _ _)) j a b c d hab hcd

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CycleBlockIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

namespace PolygonalChain
variable {O T : Set Plane} {a b c d e f : Plane}

theorem intersection_join_join (P : PolygonalChain O a b) (Q : PolygonalChain O b c)
    (R : PolygonalChain T d e) (S : PolygonalChain T e f) :
    polygonIntersection (P.join Q).vertices (R.join S).vertices (P.join Q).pieces (R.join S).pieces=
      polygonIntersection P.vertices R.vertices P.pieces R.pieces+
      polygonIntersection P.vertices S.vertices P.pieces S.pieces+
      polygonIntersection Q.vertices R.vertices Q.pieces R.pieces+
      polygonIntersection Q.vertices S.vertices Q.pieces S.pieces := by
  rw [intersection_join_left,intersection_join_right,intersection_join_right]
  ring

theorem transverse_join_join (P : PolygonalChain O a b) (Q : PolygonalChain O b c)
    (R : PolygonalChain T d e) (S : PolygonalChain T e f)
    (hPR : P.Transverse R) (hPS : P.Transverse S) (hQR : Q.Transverse R) (hQS : Q.Transverse S) :
    (P.join Q).Transverse (R.join S) :=
  P.transverse_join_left Q (R.join S)
    (R.transverse_join_right S P hPR hPS) (R.transverse_join_right S Q hQR hQS)

end PolygonalChain
namespace TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_cycle_block_radius_oai (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε| < δ →
      ∀ (d f : ℕ → (completeBipartite m n).Dart)
        (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst) (i j : ℕ),
      bipartiteDartEdge (d (i+1)) ≠ bipartiteDartEdge (d i) →
      bipartiteDartEdge (f (j+1)) ≠ bipartiteDartEdge (f j) →
      (V.dartCycleBlock d hd i).Transverse (C.shiftedCycleBlock f hf ε j) ∧
      polygonIntersection (V.dartCycleBlock d hd i).vertices (C.shiftedCycleBlock f hf ε j).vertices
        (V.dartCycleBlock d hd i).pieces (C.shiftedCycleBlock f hf ε j).pieces=
          bipartiteDartSign (d i)*bipartiteDartSign (f j)*
            V.signedIntersection (bipartiteDartEdge (d i)) (bipartiteDartEdge (f j))+
              C.passageIntersection d f hd hf i j ε := by
  obtain ⟨δ₀,hδ₀,h₀⟩ := C.exists_dart_intersection_radius hnorm hstraight htrans
  obtain ⟨δ₁,hδ₁,h₁,-,-⟩ := C.exists_vertex_chord_chain_radius hnorm
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro ε hε hs d f hd hf i j hdi hfj
  obtain ⟨hdd,hcd,hdc⟩ := h₀ ε hε (hs.trans_le (min_le_left _ _))
  have hcc := h₁ ε hε (hs.trans_le (min_le_right _ _))
    (d i).snd (f j).snd (dartTargetIncident (d i)) (dartPassageNext d hd i)
      (dartTargetIncident (f j)) (dartPassageNext f hf j)
        (dartPassage_ne d hd i hdi) (dartPassage_ne f hf j hfj)
  obtain ⟨hDD,hDI⟩ := hdd (d i) (f j)
  obtain ⟨hCD,hCI⟩ := hcd (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i) (f j)
  obtain ⟨hDC,hIC⟩ := hdc (f j).snd (dartTargetIncident (f j)) (dartPassageNext f hf j) (d i)
  constructor
  · exact PolygonalChain.transverse_join_join _ _ _ _ hDD hDC hCD hcc
  · change polygonIntersection
      ((V.dartTrackChain (d i)).join (V.chordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i))).vertices
      ((C.shiftedDartChain (f j) ε).join (C.shiftedChordChain (f j).snd (dartTargetIncident (f j)) (dartPassageNext f hf j) ε)).vertices
      ((V.dartTrackChain (d i)).join (V.chordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i))).pieces
      ((C.shiftedDartChain (f j) ε).join (C.shiftedChordChain (f j).snd (dartTargetIncident (f j)) (dartPassageNext f hf j) ε)).pieces=_
    rw [PolygonalChain.intersection_join_join,hDI,hIC,hCI,add_zero,add_zero]
    rfl

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
end

theorem solution : type_of% @OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_cycle_block_radius_oai := @OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_cycle_block_radius_oai
