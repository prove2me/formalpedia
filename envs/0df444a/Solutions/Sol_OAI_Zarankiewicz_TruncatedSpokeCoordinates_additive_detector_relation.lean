-- Prove2me | solution 1 for OAI.Zarankiewicz.TruncatedSpokeCoordinates.additive_detector_relation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T13:23:07.12882+00:00
-- url     : https://prove2.me/submissions/68cb9e51-e5a8-4a0c-8b12-41a6958b9560

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr003
import Definitions.Def_OAIB3Zr004
import Theorems.Thm_OAI_Zarankiewicz_TruncatedSpokeCoordinates_exists_closed_cycle_intersection_radius
import Theorems.Thm_OAI_Zarankiewicz_TruncatedSpokeCoordinates_exists_cross_type_radius

section
-- module Solutions.OAIB3_Zar.Crossing_FourCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open SimpleGraph
open scoped BigOperators

theorem fourCycleWalk_isCycle {m n : ℕ} (i i₀ : Fin m) (p p₀ : Fin n)
    (hi : i ≠ i₀) (hp : p ≠ p₀) : (fourCycleWalk i i₀ p p₀).IsCycle := by
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · apply Walk.IsPath.mk'
    change ([Sum.inr p, Sum.inl i₀, Sum.inr p₀, Sum.inl i] : List (Fin m ⊕ Fin n)).Nodup
    simp [hp, hi.symm]
  · change 3 ≤ (4 : ℕ)
    decide

theorem fourCycleWalk_chain {m n : ℕ} (i i₀ : Fin m) (p p₀ : Fin n) :
    walkEdgeChain (fourCycleWalk i i₀ p p₀) =
      Pi.single (i,p) 1 - Pi.single (i₀,p) 1 + Pi.single (i₀,p₀) 1 - Pi.single (i,p₀) 1 := by
  simp [fourCycleWalk, walkEdgeChain, orientedEdgeStep, sub_eq_add_neg, add_assoc]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CyclicSumArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz
open scoped BigOperators

theorem sum_range_cycle_succ {A : Type*} [AddCommGroup A] (f : ℕ → A) (N : ℕ)
    (hN : f N=f 0) : (∑ i ∈ Finset.range N, f (i+1))=∑ i ∈ Finset.range N, f i := by
  apply add_right_cancel (b := f 0)
  calc
    _ = ∑ i ∈ Finset.range (N+1), f i := (Finset.sum_range_succ' f N).symm
    _ = _ := by rw [Finset.sum_range_succ,hN]

theorem double_sum_cycle_shift_right {A B : Type*} (d : ℕ → A) (f : ℕ → B)
    (N K : ℕ) (hK : f K=f 0) (H : A → B → ℝ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, H (d i) (f (j+1)))=
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, H (d i) (f j) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_range_cycle_succ (fun j => H (d i) (f j)) K (congrArg (H (d i)) hK)

theorem double_sum_cycle_shift_left {A B : Type*} (d : ℕ → A) (f : ℕ → B)
    (N K : ℕ) (hN : d N=d 0) (H : A → B → ℝ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, H (d (i+1)) (f j))=
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, H (d i) (f j) :=
  sum_range_cycle_succ (fun i => ∑ j ∈ Finset.range K, H (d i) (f j)) N
    (congrArg (fun a => ∑ j ∈ Finset.range K, H a (f j)) hN)

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
-- module Solutions.OAIB3_Zar.Crossing_PeriodicPolygon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem cyclicIndex_of_lt (n : ℕ) (hn : 0 < n) (i : ℕ) (hi : i<n) :
    cyclicIndex n hn i = ⟨i,hi⟩ := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt hi

theorem cyclicIndex_period (n : ℕ) (hn : 0 < n) : cyclicIndex n hn n = cyclicIndex n hn 0 := by
  apply Fin.ext
  simp [cyclicIndex]

end Zarankiewicz

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

theorem segmentCrossingSign_eq_zero_of_not_meet (a b c d : Plane) (h : ¬ ClosedSegmentsMeet a b c d) :
    segmentCrossingSign a b c d=0 := by
  have hn : ¬ SegmentsCrossProperly a b c d := fun hh => h (closedSegmentsMeet_of_proper _ _ _ _ hh)
  simp [segmentCrossingSign,hn]

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
-- module Solutions.OAIB3_Zar.Crossing_PlanarDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

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

theorem direction_ne_zero (e : BipartiteEdge m n) (i : ℕ) (hi : i < V.pieces e) :
    trackDirection (V.vertices e) i ≠ 0 :=
  (V.chain e).truncated_direction_ne_zero (V.minimal e) V.radius V.radius_pos (V.short e).1 (V.short e).2 i hi

end VertexTruncation
end Zarankiewicz

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
-- module Solutions.OAIB3_Zar.Crossing_BipartiteDartGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem orientedEdgeStep_dart (d : (completeBipartite m n).Dart) :
    orientedEdgeStep d.fst d.snd=bipartiteDartSign d • Pi.single (bipartiteDartEdge d) 1 := by
  rcases bipartiteDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩ <;>
    simp [orientedEdgeStep,bipartiteDartSign,bipartiteDartEdge,forwardBipartiteDart,
      backwardBipartiteDart,SimpleGraph.Dart.symm]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CyclicWalkDarts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open SimpleGraph
variable {m n : ℕ} {u v : BipartiteVertex m n}

theorem cyclicWalkDart_period (p : (completeBipartite m n).Walk u u) (hp : 0 < p.length) :
    cyclicWalkDart p hp p.length=cyclicWalkDart p hp 0 :=
  congrArg (walkDart p) (cyclicIndex_period _ _)

theorem cyclicWalkDart_seam (p : (completeBipartite m n).Walk u u) (hp : 0 < p.length) (i : ℕ) :
    (cyclicWalkDart p hp i).snd=(cyclicWalkDart p hp (i+1)).fst := by
  change p.getVert (i%p.length+1)=p.getVert ((i+1)%p.length)
  have hi := Nat.mod_lt i hp
  have he : (i+1)%p.length=(i%p.length+1)%p.length := by simp only [Nat.add_mod,Nat.mod_mod]
  rw [he]
  by_cases hlast : i%p.length+1=p.length
  · rw [hlast,Nat.mod_self,p.getVert_length,p.getVert_zero]
  · rw [Nat.mod_eq_of_lt (by omega : i%p.length+1<p.length)]

theorem bipartiteDart_unoriented (d : (completeBipartite m n).Dart) :
    d.edge=s(Sum.inl (bipartiteDartEdge d).1,Sum.inr (bipartiteDartEdge d).2) := by
  rcases bipartiteDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩
  · rfl
  · exact Sym2.eq_swap

theorem walkDart_edge_injective (p : (completeBipartite m n).Walk u v) (hp : p.IsTrail) :
    Function.Injective (fun i : Fin p.length => bipartiteDartEdge (walkDart p i)) := by
  intro i j hij
  change bipartiteDartEdge (walkDart p i)=bipartiteDartEdge (walkDart p j) at hij
  apply Fin.ext
  have hd : (walkDart p i).edge=(walkDart p j).edge := by
    rw [bipartiteDart_unoriented,bipartiteDart_unoriented,hij]
  have he : p.edges[i.val]'(by simp)=p.edges[j.val]'(by simp) := by
    simpa only [Walk.getElem_edges,walkDart,Dart.edge] using hd
  exact hp.edges_nodup.getElem_inj_iff.mp he

theorem cyclicWalkDart_next_edge_ne (p : (completeBipartite m n).Walk u u) (hp : p.IsCycle)
    (i : ℕ) :
    bipartiteDartEdge (cyclicWalkDart p (by have := hp.three_le_length; omega) (i+1)) ≠
      bipartiteDartEdge (cyclicWalkDart p (by have := hp.three_le_length; omega) i) := by
  intro he
  have hn : 1 < p.length := by have := hp.three_le_length; omega
  have hh := walkDart_edge_injective p hp.isTrail he
  have hv := congrArg Fin.val hh
  change (i+1)%p.length=i%p.length at hv
  have hi := Nat.mod_lt i (by omega : 0 < p.length)
  have hadd : (i+1)%p.length=(i%p.length+1)%p.length := by simp only [Nat.add_mod,Nat.mod_mod]
  rw [hadd] at hv
  by_cases hlast : i%p.length+1=p.length
  · rw [hlast,Nat.mod_self] at hv
    omega
  · rw [Nat.mod_eq_of_lt (by omega : i%p.length+1<p.length)] at hv
    omega

end Zarankiewicz

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

end Zarankiewicz.PolygonalChain

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
-- module Solutions.OAIB3_Zar.Crossing_VertexPassagePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_vertex_pairing_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ j k (a b : IncidentEdges j) (c d : IncidentEdges k), a ≠ b → c ≠ d →
        (polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain k c d t).vertices 1 1+
          polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain k c d (-t)).vertices 1 1)/2=
            C.vertexChordPairing j k a b c d := by
  obtain ⟨δ,hδ,-,hzero,havg⟩ := C.exists_vertex_chord_chain_radius hnorm
  refine ⟨δ,hδ,?_⟩
  intro t ht hs j k a b c d hab hcd
  by_cases h : k=j
  · subst k
    have hc : incidentCast (rfl : j=j) c=c := Subtype.ext rfl
    have hd : incidentCast (rfl : j=j) d=d := Subtype.ext rfl
    rw [vertexChordPairing,dite_eq_left rfl,hc,hd]
    exact havg t ht hs j a b c d hab hcd
  · have hzplus := hzero t (ne_of_gt ht) (by simpa only [abs_of_pos ht] using hs) j k (Ne.symm h) a b c d
    have hzminus := hzero (-t) (neg_ne_zero.mpr (ne_of_gt ht)) (by simpa only [abs_neg,abs_of_pos ht] using hs)
      j k (Ne.symm h) a b c d
    rw [hzplus,hzminus,zero_add,zero_div]
    simp only [vertexChordPairing,dite_eq_right h]

theorem exists_passage_pairing_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ (d f : ℕ → (completeBipartite m n).Dart)
        (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst) (i j : ℕ),
      bipartiteDartEdge (d (i+1)) ≠ bipartiteDartEdge (d i) →
      bipartiteDartEdge (f (j+1)) ≠ bipartiteDartEdge (f j) →
      (C.passageIntersection d f hd hf i j t+C.passageIntersection d f hd hf i j (-t))/2=
        C.passagePairing d f hd hf i j := by
  obtain ⟨δ,hδ,hh⟩ := C.exists_vertex_pairing_radius hnorm
  refine ⟨δ,hδ,?_⟩
  intro t ht hs d f hd hf i j hi hj
  exact hh t ht hs _ _ _ _ _ _ (dartPassage_ne d hd i hi) (dartPassage_ne f hf j hj)

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_GlobalCycleAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
open scoped BigOperators
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem closed_cycle_averaged_sum (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (d f : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (N K : ℕ) (hN : d N=d 0) (hK : f K=f 0)
    (hdi : ∀ i, i < N → bipartiteDartEdge (d (i+1)) ≠ bipartiteDartEdge (d i))
    (hfj : ∀ j, j < K → bipartiteDartEdge (f (j+1)) ≠ bipartiteDartEdge (f j)) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
      (bipartiteDartSign (d i)*bipartiteDartSign (f j)*
        V.signedIntersection (bipartiteDartEdge (d i)) (bipartiteDartEdge (f j))+
          C.passagePairing d f hd hf i j)=0 := by
  obtain ⟨δ₀,hδ₀,hglobal⟩ := C.exists_closed_cycle_intersection_radius hnorm hstraight htrans
  obtain ⟨δ₁,hδ₁,hlocal⟩ := C.exists_passage_pairing_radius hnorm
  let t := min δ₀ δ₁/2
  have ht : 0 < t := half_pos (lt_min hδ₀ hδ₁)
  have htmin : t < min δ₀ δ₁ := half_lt_self (lt_min hδ₀ hδ₁)
  have ht₀ : t < δ₀ := htmin.trans_le (min_le_left _ _)
  have ht₁ : t < δ₁ := htmin.trans_le (min_le_right _ _)
  have hzplus := hglobal t (ne_of_gt ht) (by simpa only [abs_of_pos ht] using ht₀) d f hd hf N K hN hK hdi hfj
  have hzminus := hglobal (-t) (neg_ne_zero.mpr (ne_of_gt ht))
    (by simpa only [abs_neg,abs_of_pos ht] using ht₀) d f hd hf N K hN hK hdi hfj
  let E : ℕ → ℕ → ℝ := fun i j => bipartiteDartSign (d i)*bipartiteDartSign (f j)*
    V.signedIntersection (bipartiteDartEdge (d i)) (bipartiteDartEdge (f j))
  calc
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        ((E i j+C.passageIntersection d f hd hf i j t)+
          (E i j+C.passageIntersection d f hd hf i j (-t)))/2 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [← hlocal t ht ht₁ d f hd hf i j (hdi i (Finset.mem_range.mp hi)) (hfj j (Finset.mem_range.mp hj))]
      dsimp only [E]
      ring
    _ = ((∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, (E i j+C.passageIntersection d f hd hf i j t))+
        (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, (E i j+C.passageIntersection d f hd hf i j (-t))))/2 := by
      simp only [div_eq_mul_inv,Finset.sum_add_distrib,Finset.sum_mul,add_mul]
    _ = 0 := by rw [hzplus,hzminus]; norm_num

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_EndpointFlagPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem incidentCast_refl {j : BipartiteVertex m n} (e : IncidentEdges j) :
    incidentCast (rfl : j=j) e=e := Subtype.ext rfl

theorem incidentFlag_cast {j k : BipartiteVertex m n} (h : j=k) (e : IncidentEdges j) :
    (⟨k,incidentCast h e⟩ : IncidentFlag m n)=⟨j,e⟩ := by
  subst k
  rw [incidentCast_refl]

theorem dartPassageNext_flag (d : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (i : ℕ) :
    (⟨(d i).snd,dartPassageNext d hd i⟩ : IncidentFlag m n)=dartSourceFlag (d (i+1)) :=
  incidentFlag_cast (hd i).symm _

namespace TruncatedSpokeCoordinates
variable {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem vertexChordPairing_flags (j k : BipartiteVertex m n)
    (a b : IncidentEdges j) (c d : IncidentEdges k) :
    C.vertexChordPairing j k a b c d=
      C.flagPairing ⟨j,a⟩ ⟨k,c⟩-C.flagPairing ⟨j,a⟩ ⟨k,d⟩-
        C.flagPairing ⟨j,b⟩ ⟨k,c⟩+C.flagPairing ⟨j,b⟩ ⟨k,d⟩ := by
  by_cases h : k=j
  · subst k
    simp only [vertexChordPairing,flagPairing,dite_eq_left rfl,incidentCast_refl,chordEndpointPairing,dite_true]
    ring
  · simp only [vertexChordPairing,flagPairing,dite_eq_right h,sub_zero,add_zero]

theorem passagePairing_flags (d f : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst) (i j : ℕ) :
    C.passagePairing d f hd hf i j=
      C.flagPairing (dartTargetFlag (d i)) (dartTargetFlag (f j))-
        C.flagPairing (dartTargetFlag (d i)) (dartSourceFlag (f (j+1)))-
        C.flagPairing (dartSourceFlag (d (i+1))) (dartTargetFlag (f j))+
        C.flagPairing (dartSourceFlag (d (i+1))) (dartSourceFlag (f (j+1))) := by
  rw [passagePairing,C.vertexChordPairing_flags,dartPassageNext_flag,dartPassageNext_flag]
  rfl

theorem flagPairing_source_target (e f : BipartiteEdge m n) :
    C.flagPairing (dartSourceFlag (forwardBipartiteDart e)) (dartTargetFlag (forwardBipartiteDart f))=0 := by
  simp [flagPairing,dartSourceFlag,dartTargetFlag,forwardBipartiteDart]

theorem flagPairing_target_source (e f : BipartiteEdge m n) :
    C.flagPairing (dartTargetFlag (forwardBipartiteDart e)) (dartSourceFlag (forwardBipartiteDart f))=0 := by
  simp [flagPairing,dartSourceFlag,dartTargetFlag,forwardBipartiteDart]

theorem dart_endpoint_pairing (a b : (completeBipartite m n).Dart) :
    C.flagPairing (dartTargetFlag a) (dartTargetFlag b)-
      C.flagPairing (dartTargetFlag a) (dartSourceFlag b)-
      C.flagPairing (dartSourceFlag a) (dartTargetFlag b)+
      C.flagPairing (dartSourceFlag a) (dartSourceFlag b)=
        bipartiteDartSign a*bipartiteDartSign b*C.edgeEndpointPairing (bipartiteDartEdge a) (bipartiteDartEdge b) := by
  rcases bipartiteDart_cases a with ⟨e,rfl⟩ | ⟨e,rfl⟩ <;>
    rcases bipartiteDart_cases b with ⟨f,rfl⟩ | ⟨f,rfl⟩
  all_goals
    change _ = _*_*C.edgeEndpointPairing e f
    have hST := C.flagPairing_source_target e f
    have hTS := C.flagPairing_target_source e f
    simp only [edgeEndpointPairing] at *
    change C.flagPairing _ _=0 at hST hTS
  · rw [hST,hTS]
    change _ = 1*1*_
    ring
  · change C.flagPairing (dartTargetFlag (forwardBipartiteDart e)) (dartSourceFlag (forwardBipartiteDart f))-
      C.flagPairing (dartTargetFlag (forwardBipartiteDart e)) (dartTargetFlag (forwardBipartiteDart f))-
      C.flagPairing (dartSourceFlag (forwardBipartiteDart e)) (dartSourceFlag (forwardBipartiteDart f))+
      C.flagPairing (dartSourceFlag (forwardBipartiteDart e)) (dartTargetFlag (forwardBipartiteDart f))=1*(-1)*_
    rw [hST,hTS]
    ring
  · change C.flagPairing (dartSourceFlag (forwardBipartiteDart e)) (dartTargetFlag (forwardBipartiteDart f))-
      C.flagPairing (dartSourceFlag (forwardBipartiteDart e)) (dartSourceFlag (forwardBipartiteDart f))-
      C.flagPairing (dartTargetFlag (forwardBipartiteDart e)) (dartTargetFlag (forwardBipartiteDart f))+
      C.flagPairing (dartTargetFlag (forwardBipartiteDart e)) (dartSourceFlag (forwardBipartiteDart f))=(-1)*1*_
    rw [hST,hTS]
    ring
  · change C.flagPairing (dartSourceFlag (forwardBipartiteDart e)) (dartSourceFlag (forwardBipartiteDart f))-
      C.flagPairing (dartSourceFlag (forwardBipartiteDart e)) (dartTargetFlag (forwardBipartiteDart f))-
      C.flagPairing (dartTargetFlag (forwardBipartiteDart e)) (dartSourceFlag (forwardBipartiteDart f))+
      C.flagPairing (dartTargetFlag (forwardBipartiteDart e)) (dartTargetFlag (forwardBipartiteDart f))=(-1)*(-1)*_
    rw [hST,hTS]
    ring

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RectangleAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem edgePairing_single (J : Matrix ι ι ℝ) (e f : ι) :
    edgePairing J (Pi.single e 1) (Pi.single f 1) = J e f := by
  simp [edgePairing, Pi.single_apply]

theorem edgePairing_add_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (z z' y : ι → ℝ) :
    edgePairing J (z+z') y = edgePairing J z y + edgePairing J z' y := by
  simp [edgePairing, add_mul, Finset.sum_add_distrib]

theorem edgePairing_add_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (z y y' : ι → ℝ) :
    edgePairing J z (y+y') = edgePairing J z y + edgePairing J z y' := by
  simp [edgePairing, mul_add, Finset.sum_add_distrib]

theorem edgePairing_sub_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (z z' y : ι → ℝ) :
    edgePairing J (z-z') y = edgePairing J z y - edgePairing J z' y := by
  simp [edgePairing, sub_mul, Finset.sum_sub_distrib]

theorem edgePairing_sub_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (z y y' : ι → ℝ) :
    edgePairing J z (y-y') = edgePairing J z y - edgePairing J z y' := by
  simp [edgePairing, mul_sub, Finset.sum_sub_distrib]

theorem rectangle_additive
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (H : Matrix ι κ ℝ) (i₀ : ι) (j₀ : κ)
    (hrect : ∀ i i' j j', H i j-H i j'-H i' j+H i' j' = 0) :
    ∃ r : ι → ℝ, ∃ c : κ → ℝ, ∀ i j, H i j = r i+c j := by
  refine ⟨fun i => H i j₀, fun j => H i₀ j-H i₀ j₀, ?_⟩
  intro i j
  have hh := hrect i i₀ j j₀
  linarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CycleEndpointSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
open scoped BigOperators
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem passage_sum_eq_endpoint_sum (d f : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (N K : ℕ) (hN : d N=d 0) (hK : f K=f 0) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, C.passagePairing d f hd hf i j)=
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        bipartiteDartSign (d i)*bipartiteDartSign (f j)*
          C.edgeEndpointPairing (bipartiteDartEdge (d i)) (bipartiteDartEdge (f j)) := by
  have hTS := double_sum_cycle_shift_right d f N K hK
    (fun a b => C.flagPairing (dartTargetFlag a) (dartSourceFlag b))
  have hST := double_sum_cycle_shift_left d f N K hN
    (fun a b => C.flagPairing (dartSourceFlag a) (dartTargetFlag b))
  have hSS₀ := double_sum_cycle_shift_right (fun i => d (i+1)) f N K hK
    (fun a b => C.flagPairing (dartSourceFlag a) (dartSourceFlag b))
  have hSS₁ := double_sum_cycle_shift_left d f N K hN
    (fun a b => C.flagPairing (dartSourceFlag a) (dartSourceFlag b))
  simp_rw [C.passagePairing_flags,← C.dart_endpoint_pairing]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [hTS,hST,hSS₀,hSS₁]

theorem closed_cycle_matrix_sum (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (d f : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (N K : ℕ) (hN : d N=d 0) (hK : f K=f 0)
    (hdi : ∀ i, i < N → bipartiteDartEdge (d (i+1)) ≠ bipartiteDartEdge (d i))
    (hfj : ∀ j, j < K → bipartiteDartEdge (f (j+1)) ≠ bipartiteDartEdge (f j)) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
      bipartiteDartSign (d i)*bipartiteDartSign (f j)*
        C.cycleIntersectionMatrix (bipartiteDartEdge (d i)) (bipartiteDartEdge (f j))=0 := by
  have hh := C.closed_cycle_averaged_sum hnorm hstraight htrans d f hd hf N K hN hK hdi hfj
  simp only [Finset.sum_add_distrib] at hh
  rw [C.passage_sum_eq_endpoint_sum d f hd hf N K hN hK] at hh
  simpa only [cycleIntersectionMatrix,mul_add,Finset.sum_add_distrib] using hh

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_WalkVectorSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open SimpleGraph
open scoped BigOperators
variable {m n : ℕ} {u v : BipartiteVertex m n}

theorem walkEdgeChain_sum_steps (p : (completeBipartite m n).Walk u v) :
    walkEdgeChain p=∑ i ∈ Finset.range p.length, orientedEdgeStep (p.getVert i) (p.getVert (i+1)) := by
  induction p with
  | nil => simp [walkEdgeChain]
  | @cons u w v h p ih =>
    rw [walkEdgeChain,ih,Walk.length_cons,Finset.sum_range_succ']
    simp only [Walk.getVert_cons_succ,Walk.getVert_zero]
    abel

theorem walkEdgeChain_sum_cyclic_darts (p : (completeBipartite m n).Walk u u) (hp : 0 < p.length) :
    walkEdgeChain p=∑ i ∈ Finset.range p.length,
      bipartiteDartSign (cyclicWalkDart p hp i) • Pi.single (bipartiteDartEdge (cyclicWalkDart p hp i)) 1 := by
  rw [walkEdgeChain_sum_steps]
  apply Finset.sum_congr rfl
  intro i hi
  have hlt := Finset.mem_range.mp hi
  rw [cyclicWalkDart,cyclicIndex_of_lt _ _ _ hlt]
  exact orientedEdgeStep_dart (walkDart p ⟨i,hlt⟩)

theorem edgePairing_sum_left {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (s : Finset α) (z : α → ι → ℝ) (y : ι → ℝ) :
    edgePairing J (∑ a ∈ s, z a) y=∑ a ∈ s, edgePairing J (z a) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [edgePairing]
  | @insert a s ha ih => rw [Finset.sum_insert ha,edgePairing_add_left,ih,Finset.sum_insert ha]

theorem edgePairing_sum_right {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (s : Finset α) (z : ι → ℝ) (y : α → ι → ℝ) :
    edgePairing J z (∑ a ∈ s, y a)=∑ a ∈ s, edgePairing J z (y a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [edgePairing]
  | @insert a s ha ih => rw [Finset.sum_insert ha,edgePairing_add_right,ih,Finset.sum_insert ha]

theorem edgePairing_smul_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (e f : ι) (a b : ℝ) :
    edgePairing J (a • Pi.single e 1) (b • Pi.single f 1)=a*b*J e f := by
  simp [edgePairing,Pi.single_apply,mul_comm,mul_left_comm]

theorem edgePairing_walk_dart_sum (J : Matrix (BipartiteEdge m n) (BipartiteEdge m n) ℝ)
    (p : (completeBipartite m n).Walk u u) (q : (completeBipartite m n).Walk v v)
    (hp : 0 < p.length) (hq : 0 < q.length) :
    edgePairing J (walkEdgeChain p) (walkEdgeChain q)=
      ∑ i ∈ Finset.range p.length, ∑ j ∈ Finset.range q.length,
        bipartiteDartSign (cyclicWalkDart p hp i)*bipartiteDartSign (cyclicWalkDart q hq j)*
          J (bipartiteDartEdge (cyclicWalkDart p hp i)) (bipartiteDartEdge (cyclicWalkDart q hq j)) := by
  rw [walkEdgeChain_sum_cyclic_darts p hp,walkEdgeChain_sum_cyclic_darts q hq,edgePairing_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [edgePairing_sum_right]
  apply Finset.sum_congr rfl
  intro j hj
  exact edgePairing_smul_single _ _ _ _ _

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CyclePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem lemma3_1 (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    {u v : BipartiteVertex m n} (p : (completeBipartite m n).Walk u u)
    (q : (completeBipartite m n).Walk v v) (hp : p.IsCycle) (hq : q.IsCycle) :
    edgePairing C.cycleIntersectionMatrix (walkEdgeChain p) (walkEdgeChain q)=0 := by
  have hpl : 0 < p.length := by have := hp.three_le_length; omega
  have hql : 0 < q.length := by have := hq.three_le_length; omega
  rw [edgePairing_walk_dart_sum _ p q hpl hql]
  exact C.closed_cycle_matrix_sum hnorm hstraight htrans
    (cyclicWalkDart p hpl) (cyclicWalkDart q hql)
    (cyclicWalkDart_seam p hpl) (cyclicWalkDart_seam q hql) p.length q.length
    (cyclicWalkDart_period p hpl) (cyclicWalkDart_period q hql)
    (fun i _ => cyclicWalkDart_next_edge_ne p hp i) (fun j _ => cyclicWalkDart_next_edge_ne q hq j)

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FourCyclePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem fourCycle_pairing_rectangle {m n : ℕ}
    (J : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ)
    (i k i₀ : Fin m) (p p' q q' : Fin n) :
    edgePairing J (walkEdgeChain (fourCycleWalk i i₀ p p'))
      (walkEdgeChain (fourCycleWalk k i₀ q q')) =
      blockRectangle J i k i₀ p q - blockRectangle J i k i₀ p q' -
        blockRectangle J i k i₀ p' q + blockRectangle J i k i₀ p' q' := by
  rw [fourCycleWalk_chain, fourCycleWalk_chain]
  simp only [edgePairing_add_left, edgePairing_sub_left, edgePairing_add_right,
    edgePairing_sub_right, edgePairing_single]
  simp only [blockRectangle, edgeBlock, Matrix.add_apply, Matrix.sub_apply]
  ring

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AdditiveBlockRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem fourCycle_pairing_zero (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (i k i₀ : Fin m) (p p' q q' : Fin n) :
    edgePairing C.cycleIntersectionMatrix (walkEdgeChain (fourCycleWalk i i₀ p p'))
      (walkEdgeChain (fourCycleWalk k i₀ q q'))=0 := by
  by_cases hi : i=i₀
  · subst i
    have hz : walkEdgeChain (fourCycleWalk i₀ i₀ p p')=0 := by rw [fourCycleWalk_chain]; abel
    rw [hz]
    simp [edgePairing]
  by_cases hk : k=i₀
  · subst k
    have hz : walkEdgeChain (fourCycleWalk i₀ i₀ q q')=0 := by rw [fourCycleWalk_chain]; abel
    rw [hz]
    simp [edgePairing]
  by_cases hp : p=p'
  · subst p'
    have hz : walkEdgeChain (fourCycleWalk i i₀ p p)=0 := by rw [fourCycleWalk_chain]; abel
    rw [hz]
    simp [edgePairing]
  by_cases hq : q=q'
  · subst q'
    have hz : walkEdgeChain (fourCycleWalk k i₀ q q)=0 := by rw [fourCycleWalk_chain]; abel
    rw [hz]
    simp [edgePairing]
  exact C.lemma3_1 hnorm hstraight htrans _ _
    (fourCycleWalk_isCycle i i₀ p p' hi hp) (fourCycleWalk_isCycle k i₀ q q' hk hq)

theorem lemma3_2 (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (i k i₀ : Fin m) :
    ∃ r c : Fin n → ℝ, ∀ p q,
      blockRectangle C.cycleIntersectionMatrix i k i₀ p q=r p+c q := by
  cases n with
  | zero => exact ⟨0,0,fun p => Fin.elim0 p⟩
  | succ n =>
    apply rectangle_additive (blockRectangle C.cycleIntersectionMatrix i k i₀) 0 0
    intro p p' q q'
    rw [← fourCycle_pairing_rectangle]
    exact C.fourCycle_pairing_zero hnorm hstraight htrans i k i₀ p p' q q'

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_NodeMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem derivativeAtNode_eq_prod (node : ι → ℝ) (i : ι) :
    derivativeAtNode node i = ∏ j ∈ Finset.univ.erase i, (node i-node j) := by
  unfold derivativeAtNode nodePolynomial
  change (Lagrange.nodal Finset.univ node).derivative.eval (node i) = _
  rw [Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i), Lagrange.eval_nodal]

theorem node_polynomial_moment (node : ι → ℝ) (hn : Function.Injective node)
    (P : ℝ[X]) (hP : P.degree < (Fintype.card ι - 1 : ℕ)) :
    (∑ i, P.eval (node i) / derivativeAtNode node i) = 0 := by
  by_cases hcard : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    simp
  have hp' : P.degree < (Finset.univ : Finset ι).card :=
    hP.trans_le (by exact_mod_cast Nat.sub_le (Fintype.card ι) 1)
  have he := Lagrange.coeff_eq_sum (s := Finset.univ) (v := node) hn.injOn hp'
  rw [Finset.card_univ, coeff_eq_zero_of_degree_lt hP] at he
  simpa only [Finset.card_univ, derivativeAtNode_eq_prod] using he.symm

theorem node_power_moment (node : ι → ℝ) (hn : Function.Injective node)
    (k : ℕ) (hk : k+1 < Fintype.card ι) :
    (∑ i, node i ^ k / derivativeAtNode node i) = 0 := by
  have hdeg : (X^k : ℝ[X]).degree < (Fintype.card ι - 1 : ℕ) := by
    rw [degree_X_pow]
    exact_mod_cast (show k < Fintype.card ι-1 by omega)
  simpa only [eval_pow, eval_X] using node_polynomial_moment node hn (X^k) hdeg

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RankDetector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem detectorAtom_entry
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (node : ι → ℝ) (p q : ι) (ab cd : BiExponent s) :
    detectorAtom s node p q ab cd =
      (node p-node q) * node p^(ab.1.val+cd.1.val) * node q^(ab.2.val+cd.2.val) /
        (derivativeAtNode node p * derivativeAtNode node q) := by
  simp only [detectorAtom, detectorWeight, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, detectorVector, pow_add]
  ring

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DetectorAnnihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem detectorAtom_entry_split (s : ℕ) (node : ι → ℝ) (p q : ι) (ab cd : BiExponent s) :
    detectorAtom s node p q ab cd =
      (node p^(ab.1.val+cd.1.val+1) / derivativeAtNode node p) *
        (node q^(ab.2.val+cd.2.val) / derivativeAtNode node q) -
      (node p^(ab.1.val+cd.1.val) / derivativeAtNode node p) *
        (node q^(ab.2.val+cd.2.val+1) / derivativeAtNode node q) := by
  rw [detectorAtom_entry]
  simp only [pow_succ, div_eq_mul_inv, mul_inv_rev]
  ring

theorem detectorAtom_row_sum (s : ℕ) (node : ι → ℝ) (hn : Function.Injective node)
    (hcard : Fintype.card ι = 2*s+1) (p : ι) : ∑ q, detectorAtom s node p q = 0 := by
  funext ab cd
  simp only [Matrix.sum_apply, Matrix.zero_apply, detectorAtom_entry_split,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hb := ab.2.isLt
  have hd := cd.2.isLt
  rw [node_power_moment node hn _ (by omega), node_power_moment node hn _ (by omega)]
  ring

theorem detectorAtom_column_sum (s : ℕ) (node : ι → ℝ) (hn : Function.Injective node)
    (hcard : Fintype.card ι = 2*s+1) (q : ι) : ∑ p, detectorAtom s node p q = 0 := by
  funext ab cd
  simp only [Matrix.sum_apply, Matrix.zero_apply, detectorAtom_entry_split,
    Finset.sum_sub_distrib, ← Finset.sum_mul]
  have ha := ab.1.isLt
  have hc := cd.1.isLt
  rw [node_power_moment node hn _ (by omega), node_power_moment node hn _ (by omega)]
  ring

theorem rankDetector_additive (s : ℕ) (node : ι → ℝ) (hn : Function.Injective node)
    (hcard : Fintype.card ι = 2*s+1) (r c : ι → ℝ) :
    rankDetector s node (fun p q => r p+c q) = 0 := by
  change (∑ p, ∑ q, (r p+c q) • detectorAtom s node p q) = 0
  simp only [add_smul, Finset.sum_add_distrib]
  have hr : (∑ p, ∑ q, r p • detectorAtom s node p q) = 0 := by
    simp only [← Finset.smul_sum, detectorAtom_row_sum s node hn hcard, smul_zero, Finset.sum_const_zero]
  have hc : (∑ p, ∑ q, c q • detectorAtom s node p q) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum, detectorAtom_column_sum s node hn hcard, smul_zero,
      Finset.sum_const_zero]
  rw [hr, hc, add_zero]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_VertexOrderDetector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem additive_detector_relation_oai (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (s : ℕ) (node : Fin n → ℝ) (hn : Function.Injective node) (hcard : n=2*s+1)
    (i k i₀ : Fin m) :
    rankDetector s node (edgeBlock C.cycleIntersectionMatrix i k)-
      rankDetector s node (edgeBlock C.cycleIntersectionMatrix i i₀)-
      rankDetector s node (edgeBlock C.cycleIntersectionMatrix i₀ k)+
      rankDetector s node (edgeBlock C.cycleIntersectionMatrix i₀ i₀)=0 := by
  obtain ⟨r,c,hrc⟩ := C.lemma3_2 hnorm hstraight htrans i k i₀
  have he : blockRectangle C.cycleIntersectionMatrix i k i₀=(fun p q => r p+c q) := funext (fun p => funext (hrc p))
  have hz : rankDetector s node (blockRectangle C.cycleIntersectionMatrix i k i₀)=0 := by
    rw [he]
    exact rankDetector_additive s node hn (by simpa only [Fintype.card_fin] using hcard) r c
  simpa only [blockRectangle,map_add,map_sub] using hz

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

theorem solution : type_of% @OAI.Zarankiewicz.TruncatedSpokeCoordinates.additive_detector_relation_oai := @OAI.Zarankiewicz.TruncatedSpokeCoordinates.additive_detector_relation_oai
