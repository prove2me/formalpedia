-- Prove2me | solution 1 for OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_closed_cycle_intersection_radius
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T13:17:34.931034+00:00
-- url     : https://prove2.me/submissions/15510d02-7bde-4455-8244-ea6f1acf93f2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr003
import Definitions.Def_OAIB3Zr004
import Theorems.Thm_OAI_Zarankiewicz_TruncatedSpokeCoordinates_exists_cycle_block_radius

section
-- module Solutions.OAIB3_Zar.Crossing_StepEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem sum_stepEvent (n : ℕ) (r lo hi : Fin n → ℝ) (hr : StrictMono r)
    (h0 : ∀ i, r i ≠ 0) (h1 : ∀ i, r i ≠ 1) :
    (∑ i, stepEvent r lo hi i) =
      (∏ i, stepAt (r i) (lo i) (hi i) 1) - ∏ i, stepAt (r i) (lo i) (hi i) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    let rt := fun i : Fin n => r i.succ
    let lt := fun i : Fin n => lo i.succ
    let ht := fun i : Fin n => hi i.succ
    have hrt : StrictMono rt := hr.comp (fun _ _ h => Fin.succ_lt_succ_iff.mpr h)
    have hind := ih rt lt ht hrt (fun i => h0 i.succ) (fun i => h1 i.succ)
    have hfirst : ∀ i : Fin n, r 0 < r i.succ := fun i => hr (Fin.succ_pos i)
    have hhead : stepEvent r lo hi 0 =
        if 0 < r 0 ∧ r 0 < 1 then (hi 0-lo 0) * ∏ i : Fin n, lt i else 0 := by
      unfold stepEvent
      rw [Fin.prod_univ_succ]
      simp only [ite_true,one_mul,Fin.succ_ne_zero,ite_false]
      congr 1
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact ite_eq_left (hfirst i)
    have htail : ∀ i : Fin n, stepEvent r lo hi i.succ = hi 0 * stepEvent rt lt ht i := by
      intro i
      unfold stepEvent
      rw [Fin.prod_univ_succ]
      simp only [(Fin.succ_ne_zero i).symm,ite_false,Fin.succ_inj]
      rw [show stepAt (r 0) (lo 0) (hi 0) (r i.succ) = hi 0 from ite_eq_right (not_lt.mpr (hfirst i).le)]
      change (if 0 < rt i ∧ rt i < 1 then (ht i-lt i) *
        (hi 0 * ∏ j, if j=i then 1 else stepAt (rt j) (lt j) (ht j) (rt i)) else 0) = _
      split_ifs <;> ring
    rw [Fin.sum_univ_succ,hhead]
    simp_rw [htail]
    rw [← Finset.mul_sum,hind,Fin.prod_univ_succ,Fin.prod_univ_succ]
    rcases lt_or_gt_of_ne (h0 0) with hrneg | hrpos
    · have hn1 : ¬ 1 < r 0 := by linarith
      have hn0 : ¬ 0 < r 0 := by linarith
      simp only [hn0,false_and,ite_false,stepAt,hn1]
      ring
    · rcases lt_or_gt_of_ne (h1 0) with hrlt | hrgt
      · have hn1 : ¬ 1 < r 0 := by linarith
        have ht0 : (∏ i : Fin n, stepAt (rt i) (lt i) (ht i) 0) = ∏ i : Fin n, lt i := by
          apply Finset.prod_congr rfl
          intro i hi
          exact ite_eq_left (hrpos.trans (hfirst i))
        rw [ht0]
        simp only [hrpos,hrlt,and_self,ite_true,stepAt,hn1,ite_false]
        ring
      · have ht0 : (∏ i : Fin n, stepAt (rt i) (lt i) (ht i) 0) = ∏ i : Fin n, lt i := by
          apply Finset.prod_congr rfl
          intro i hi
          exact ite_eq_left (hrpos.trans (hfirst i))
        have ht1 : (∏ i : Fin n, stepAt (rt i) (lt i) (ht i) 1) = ∏ i : Fin n, lt i := by
          apply Finset.prod_congr rfl
          intro i hi
          exact ite_eq_left (hrgt.trans (hfirst i))
        rw [ht0,ht1]
        simp [stepAt,hrpos,hrgt,not_lt.mpr hrgt.le]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AffineSideEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem sideAfter_sub_before (b : ℝ) : sideAfter b-sideBefore b = slopeSign b := by
  unfold sideAfter sideBefore slopeSign
  split_ifs <;> norm_num

theorem positiveIndicator_factor (b r t : ℝ) (hb : b ≠ 0) (ht : t ≠ r) :
    positiveIndicator (b*(t-r)) = stepAt r (sideBefore b) (sideAfter b) t := by
  rcases lt_or_gt_of_ne hb with hb | hb
  · by_cases htr : t < r
    · have hprod := mul_pos_of_neg_of_neg hb (sub_neg.mpr htr)
      simp [positiveIndicator,stepAt,sideBefore,htr,hprod,not_lt.mpr hb.le]
    · have hrt : r<t := lt_of_le_of_ne (le_of_not_gt htr) ht.symm
      have hprod := mul_neg_of_neg_of_pos hb (sub_pos.mpr hrt)
      simp [positiveIndicator,stepAt,sideAfter,htr,not_lt.mpr hprod.le,not_lt.mpr hb.le]
  · by_cases htr : t < r
    · have hprod := mul_neg_of_pos_of_neg hb (sub_neg.mpr htr)
      simp [positiveIndicator,stepAt,sideBefore,htr,not_lt.mpr hprod.le,hb]
    · have hrt : r<t := lt_of_le_of_ne (le_of_not_gt htr) ht.symm
      have hprod := mul_pos hb (sub_pos.mpr hrt)
      simp [positiveIndicator,stepAt,sideAfter,htr,hprod,hb]

theorem sum_affine_side_events (n : ℕ) (r b : Fin n → ℝ)
    (hr : StrictMono r) (hb : ∀ i, b i ≠ 0) (h0 : ∀ i, r i ≠ 0) (h1 : ∀ i, r i ≠ 1) :
    (∑ i, if 0<r i ∧ r i<1 then slopeSign (b i) *
      (∏ j, if j=i then 1 else positiveIndicator (b j*(r i-r j))) else 0) =
      (∏ i, positiveIndicator (b i*(1-r i))) - ∏ i, positiveIndicator (b i*(0-r i)) := by
  have hh := sum_stepEvent n r (fun i => sideBefore (b i)) (fun i => sideAfter (b i)) hr h0 h1
  have he : ∀ i : Fin n, stepEvent r (fun i => sideBefore (b i)) (fun i => sideAfter (b i)) i =
      if 0<r i ∧ r i<1 then slopeSign (b i) *
        (∏ j, if j=i then 1 else positiveIndicator (b j*(r i-r j))) else 0 := by
    intro i
    unfold stepEvent
    rw [sideAfter_sub_before]
    congr 1
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hji : j=i
    · simp [hji]
    · rw [ite_eq_right hji,ite_eq_right hji]
      exact (positiveIndicator_factor (b j) (r j) (r i) (hb j) (hr.injective.ne (Ne.symm hji))).symm
  simp_rw [he] at hh
  rw [hh]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact (positiveIndicator_factor (b i) (r i) 1 (hb i) (h1 i).symm).symm
  · apply Finset.prod_congr rfl
    intro i hi
    exact (positiveIndicator_factor (b i) (r i) 0 (hb i) (h0 i).symm).symm

end Zarankiewicz

end

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

theorem telescoping_real_sum (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f i-f (i+1))) = f 0-f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    ring

theorem polygon_cone_cancellation (v : ℕ → Plane) (n : ℕ) (hv : v n = v 0)
    (o c d : Plane) :
    (∑ i ∈ Finset.range n, triangleSegmentIntersection o (v i) (v (i+1)) c d) =
      ∑ i ∈ Finset.range n, segmentCrossingSign (v i) (v (i+1)) c d := by
  unfold triangleSegmentIntersection
  have hrev : ∀ i, segmentCrossingSign (v (i+1)) o c d = -segmentCrossingSign o (v (i+1)) c d :=
    fun i => segmentCrossingSign_reverse_left o (v (i+1)) c d
  simp only [hrev, Finset.sum_add_distrib]
  have htele := telescoping_real_sum (fun i => segmentCrossingSign o (v i) c d) n
  rw [hv,sub_self] at htele
  rw [Finset.sum_sub_distrib] at htele
  rw [Finset.sum_neg_distrib]
  linarith

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
-- module Solutions.OAIB3_Zar.Crossing_PolygonStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical BigOperators

theorem exists_polygon_intersection_stability_radius (v w : ℕ → Plane) (n m : ℕ)
    (h : ∀ i : Fin n, ∀ j : Fin m,
      SegmentPairTransverse (v i.val) (v (i.val+1)) (w j.val) (w (j.val+1))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v' : ℕ → Plane,
      (∀ i : Fin (n+1), dist (v' i.val) (v i.val) < ε) →
      polygonIntersection v' w n m = polygonIntersection v w n m := by
  have hh : ∀ ij : Fin n × Fin m, ∃ ε : ℝ, 0 < ε ∧
      ∀ ab : Plane × Plane, dist ab (v ij.1.val,v (ij.1.val+1)) < ε →
        segmentCrossingSign ab.1 ab.2 (w ij.2.val) (w (ij.2.val+1)) =
          segmentCrossingSign (v ij.1.val) (v (ij.1.val+1)) (w ij.2.val) (w (ij.2.val+1)) := by
    intro ij
    obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp
      (eventually_segmentCrossingSign _ _ _ _ (h ij.1 ij.2))
    exact ⟨ε,hε,fun ab hab => he hab⟩
  choose radius hpos hstable using hh
  obtain ⟨ε,hε,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun ij _ => hpos ij)
  refine ⟨ε,hε,?_⟩
  intro v' hv'
  unfold polygonIntersection
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hin := Finset.mem_range.mp hi
  have hjm := Finset.mem_range.mp hj
  let ii : Fin n := ⟨i,hin⟩
  let jj : Fin m := ⟨j,hjm⟩
  apply hstable (ii,jj) (v' i,v' (i+1))
  rw [Prod.dist_eq]
  exact (max_lt (hv' ⟨i,by omega⟩) (hv' ⟨i+1,by omega⟩)).trans (hbound (ii,jj) (Finset.mem_univ _))

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
-- module Solutions.OAIB3_Zar.Crossing_PolygonTransversalityStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical

theorem exists_polygon_transversality_radius (v w : ℕ → Plane) (n m : ℕ)
    (h : ∀ i : Fin n, ∀ j : Fin m,
      SegmentPairTransverse (v i.val) (v (i.val+1)) (w j.val) (w (j.val+1))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v' : ℕ → Plane,
      (∀ i : Fin (n+1), dist (v' i.val) (v i.val) < ε) →
      (∀ i : Fin n, ∀ j : Fin m,
        SegmentPairTransverse (v' i.val) (v' (i.val+1)) (w j.val) (w (j.val+1))) ∧
      polygonIntersection v' w n m = polygonIntersection v w n m := by
  have hh : ∀ ij : Fin n × Fin m, ∃ ε : ℝ, 0 < ε ∧
      ∀ ab : Plane × Plane, dist ab (v ij.1.val,v (ij.1.val+1)) < ε →
        SegmentPairTransverse ab.1 ab.2 (w ij.2.val) (w (ij.2.val+1)) := by
    intro ij
    obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp
      (eventually_segmentPairTransverse _ _ _ _ (h ij.1 ij.2))
    exact ⟨ε,hε,fun ab hab => he hab⟩
  choose radius hpos hstable using hh
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun ij _ => hpos ij)
  obtain ⟨η,hη,hcount⟩ := exists_polygon_intersection_stability_radius v w n m h
  refine ⟨min δ η,lt_min hδ hη,?_⟩
  intro v' hv'
  constructor
  · intro i j
    apply hstable (i,j) (v' i.val,v' (i.val+1))
    rw [Prod.dist_eq]
    have h₀ := (hv' ⟨i.val,by omega⟩).trans_le (min_le_left δ η)
    have h₁ := (hv' ⟨i.val+1,by omega⟩).trans_le (min_le_left δ η)
    exact (max_lt h₀ h₁).trans (hbound (i,j) (Finset.mem_univ _))
  · exact hcount v' (fun i => (hv' i).trans_le (min_le_right δ η))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FiniteLineAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators Classical

theorem lineAvoidancePolynomial_eval (z a v : Plane) (t : ℝ) :
    (lineAvoidancePolynomial z a v).eval t = det2 (z+(t,t^2)-a) v := by
  simp [lineAvoidancePolynomial,det2]
  ring

theorem lineAvoidancePolynomial_ne_zero (z a v : Plane) (hv : v ≠ 0) :
    lineAvoidancePolynomial z a v ≠ 0 := by
  intro h
  have h₁ := congrArg (fun p : ℝ[X] => p.coeff 1) h
  have h₂ := congrArg (fun p : ℝ[X] => p.coeff 2) h
  norm_num [lineAvoidancePolynomial,coeff_C_mul] at h₁ h₂
  apply hv
  exact Prod.ext h₂ h₁

theorem exists_near_avoiding_lines {ι : Type*} [Fintype ι] (a v : ι → Plane)
    (hv : ∀ i, v i ≠ 0) (z : Plane) (ε : ℝ) (hε : 0 < ε) :
    ∃ o : Plane, dist o z < ε ∧ ∀ i, det2 (o-a i) (v i) ≠ 0 := by
  let bad : Finset ℝ := Finset.univ.biUnion (fun i => (lineAvoidancePolynomial z (a i) (v i)).roots.toFinset)
  have hδ : 0 < min ε 1 := lt_min hε (by norm_num)
  obtain ⟨t,ht⟩ := ((Set.Ioo_infinite hδ).sdiff bad.finite_toSet).nonempty
  have ht0 : 0 < t := ht.1.1
  have htε : t < ε := lt_of_lt_of_le ht.1.2 (min_le_left _ _)
  have ht1 : t < 1 := lt_of_lt_of_le ht.1.2 (min_le_right _ _)
  refine ⟨z+(t,t^2),?_,?_⟩
  · have ht2 : t^2 < ε := by nlinarith
    simp only [Prod.dist_eq,Prod.fst_add,Prod.snd_add,Real.dist_eq,add_sub_cancel_left]
    exact max_lt (by simpa [abs_of_pos ht0] using htε) (by simpa [abs_of_nonneg (sq_nonneg t)] using ht2)
  · intro i hi
    have hp : (lineAvoidancePolynomial z (a i) (v i)).eval t = 0 := by
      rwa [lineAvoidancePolynomial_eval]
    apply ht.2
    change t ∈ bad
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ i,?_⟩
    simpa [mem_roots (lineAvoidancePolynomial_ne_zero z (a i) (v i) (hv i))] using hp

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_GenericPointExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_generic_point_extension {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (p : ι → Plane) (q : ν → Plane) (a v : κ → Plane)
    (hv : ∀ k, v k ≠ 0) (hpq : ∀ i j, q j ≠ p i)
    (z : Plane) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : Plane, dist x z < ε ∧
      (∀ i, x ≠ p i) ∧ (∀ j, q j ≠ x) ∧
      (∀ k, det2 (x-a k) (v k) ≠ 0) ∧
      (∀ i k, det2 (x-p i) (v k) ≠ 0) ∧
      (∀ i j, orient2 (p i) x (q j) ≠ 0) := by
  let J := κ ⊕ (ν ⊕ (ι ⊕ ((ι × κ) ⊕ (ι × ν))))
  let base : J → Plane
    | .inl k => a k
    | .inr (.inl j) => q j
    | .inr (.inr (.inl i)) => p i
    | .inr (.inr (.inr (.inl (i,_)))) => p i
    | .inr (.inr (.inr (.inr (i,_)))) => p i
  let direction : J → Plane
    | .inl k => v k
    | .inr (.inl _) => (1,0)
    | .inr (.inr (.inl _)) => (1,0)
    | .inr (.inr (.inr (.inl (_,k)))) => v k
    | .inr (.inr (.inr (.inr (i,j)))) => q j-p i
  have hd : ∀ k, direction k ≠ 0 := by
    rintro (k|(j|(i|(⟨i,k⟩|⟨i,j⟩))))
    · exact hv k
    · norm_num [direction]
    · norm_num [direction]
    · exact hv k
    · exact sub_ne_zero.mpr (hpq i j)
  obtain ⟨x,hx,havoid⟩ := exists_near_avoiding_lines base direction hd z ε hε
  refine ⟨x,hx,?_,?_,?_,?_,?_⟩
  · intro i heq
    have hh := havoid (.inr (.inr (.inl i)))
    simp [base,direction,heq,det2] at hh
  · intro j heq
    have hh := havoid (.inr (.inl j))
    simp [base,direction,← heq,det2] at hh
  · intro k
    exact havoid (.inl k)
  · intro i k
    exact havoid (.inr (.inr (.inr (.inl (i,k)))))
  · intro i j
    exact havoid (.inr (.inr (.inr (.inr (i,j)))))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SortedSideEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem exists_sorted_permutation (n : ℕ) (r : Fin n → ℝ) (hr : Function.Injective r) :
    ∃ e : Equiv.Perm (Fin n), StrictMono (r ∘ e) := by
  let e := @Fintype.orderIsoFinOfCardEq (Fin n) (LinearOrder.lift' r hr)
    inferInstance n (Fintype.card_fin n)
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  exact @OrderIso.strictMono (Fin n) (Fin n) inferInstance
    (LinearOrder.lift' r hr).toPreorder e i j hij

theorem sum_affine_side_events_unordered (n : ℕ) (r b : Fin n → ℝ)
    (hr : Function.Injective r) (hb : ∀ i, b i ≠ 0) (h0 : ∀ i, r i ≠ 0) (h1 : ∀ i, r i ≠ 1) :
    (∑ i, if 0<r i ∧ r i<1 then slopeSign (b i) *
      (∏ j, if j=i then 1 else positiveIndicator (b j*(r i-r j))) else 0) =
      (∏ i, positiveIndicator (b i*(1-r i))) - ∏ i, positiveIndicator (b i*(0-r i)) := by
  obtain ⟨e,he⟩ := exists_sorted_permutation n r hr
  have h := sum_affine_side_events n (r ∘ e) (b ∘ e) he
    (fun i => hb (e i)) (fun i => h0 (e i)) (fun i => h1 (e i))
  simp only [Function.comp_apply] at h
  have hprod : ∀ i, (∏ j : Fin n, if j=i then (1 : ℝ) else
      positiveIndicator (b (e j)*(r (e i)-r (e j)))) =
      ∏ j : Fin n, if j=e i then 1 else positiveIndicator (b j*(r (e i)-r j)) := by
    intro i
    rw [← Equiv.prod_comp e (fun j => if j=e i then (1 : ℝ) else positiveIndicator (b j*(r (e i)-r j)))]
    simp only [e.injective.eq_iff]
  simp_rw [hprod] at h
  rw [Equiv.sum_comp e (fun i => if 0<r i ∧ r i<1 then slopeSign (b i) *
      (∏ j, if j=i then 1 else positiveIndicator (b j*(r i-r j))) else 0),
    Equiv.prod_comp e (fun i => positiveIndicator (b i*(1-r i))),
    Equiv.prod_comp e (fun i => positiveIndicator (b i*(0-r i)))] at h
  exact h

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TriangleSideEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical

theorem triangle_side_at_first_edge (a b c : Plane) (t : ℝ) :
    orient2 b c (segmentPoint a b t) = (1-t)*orient2 a b c := by
  dsimp [orient2,det2,segmentPoint]
  ring

theorem triangle_other_side_at_first_edge (a b c : Plane) (t : ℝ) :
    orient2 c a (segmentPoint a b t) = t*orient2 a b c := by
  dsimp [orient2,det2,segmentPoint]
  ring

theorem triangle_edge_side_tests (a b c d e : Plane)
    (harea : 0 < orient2 a b c) (hn : det2 (b-a) (e-d) ≠ 0) :
    (0 < orient2 b c (segmentPoint d e (secondIntersectionParameter a b d e)) ↔
      firstIntersectionParameter a b d e < 1) ∧
    (0 < orient2 c a (segmentPoint d e (secondIntersectionParameter a b d e)) ↔
      0 < firstIntersectionParameter a b d e) := by
  rw [← intersection_parameters_eq a b d e hn,
    triangle_side_at_first_edge, triangle_other_side_at_first_edge]
  constructor
  · rw [mul_pos_iff_of_pos_right harea]
    constructor <;> intro h <;> linarith
  · exact mul_pos_iff_of_pos_right harea

theorem segmentCrossingSign_triangle_event (a b c d e : Plane)
    (harea : 0 < orient2 a b c) (hn : det2 (b-a) (e-d) ≠ 0) :
    segmentCrossingSign a b d e =
      if 0 < secondIntersectionParameter a b d e ∧ secondIntersectionParameter a b d e < 1 then
        slopeSign (det2 (b-a) (e-d)) *
          (positiveIndicator (orient2 b c (segmentPoint d e (secondIntersectionParameter a b d e))) *
           positiveIndicator (orient2 c a (segmentPoint d e (secondIntersectionParameter a b d e))))
      else 0 := by
  obtain ⟨hleft,hright⟩ := triangle_edge_side_tests a b c d e harea hn
  rw [segmentCrossingSign, segmentsCrossProperly_iff_parameters a b d e hn]
  simp only [Set.mem_Ioo,positiveIndicator,hleft,hright]
  by_cases hu : 0 < secondIntersectionParameter a b d e ∧ secondIntersectionParameter a b d e < 1
  · by_cases ht0 : 0 < firstIntersectionParameter a b d e <;>
      by_cases ht1 : firstIntersectionParameter a b d e < 1 <;>
      simp [hu,ht0,ht1,slopeSign]
  · simp [hu]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TriangleEntryExit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical

theorem triangle_area_cycle (a b c : Plane) : orient2 b c a = orient2 a b c := by
  dsimp [orient2,det2]
  ring

theorem affine_side_factor (a b c d : Plane) (hn : det2 (b-a) (d-c) ≠ 0) (t : ℝ) :
    orient2 a b (segmentPoint c d t) =
      det2 (b-a) (d-c) * (t-secondIntersectionParameter a b c d) := by
  rw [orient2_segment]
  change (1-t)*orient2 a b c+t*orient2 a b d =
    det2 (b-a) (d-c)*(t-(-orient2 a b c / det2 (b-a) (d-c)))
  field_simp
  linear_combination t * (orient2_difference a b c d)

theorem triangle_segment_entry_exit (a b c d e : Plane)
    (harea : 0 < orient2 a b c)
    (hn : ∀ i : Fin 3, det2 (triangleEnd a b c i-triangleStart a b c i) (e-d) ≠ 0)
    (hr : Function.Injective (fun i : Fin 3 =>
      secondIntersectionParameter (triangleStart a b c i) (triangleEnd a b c i) d e))
    (h0 : ∀ i : Fin 3, secondIntersectionParameter (triangleStart a b c i) (triangleEnd a b c i) d e ≠ 0)
    (h1 : ∀ i : Fin 3, secondIntersectionParameter (triangleStart a b c i) (triangleEnd a b c i) d e ≠ 1) :
    triangleSegmentIntersection a b c d e = triangleIndicator a b c e-triangleIndicator a b c d := by
  let r := fun i : Fin 3 => secondIntersectionParameter (triangleStart a b c i) (triangleEnd a b c i) d e
  let b' := fun i : Fin 3 => det2 (triangleEnd a b c i-triangleStart a b c i) (e-d)
  have hf (i : Fin 3) (t : ℝ) : b' i*(t-r i) =
      orient2 (triangleStart a b c i) (triangleEnd a b c i) (segmentPoint d e t) :=
    (affine_side_factor _ _ d e (hn i) t).symm
  have hc1 : 0 < orient2 b c a := by rwa [triangle_area_cycle]
  have hc2 : 0 < orient2 c a b := by rwa [triangle_area_cycle,triangle_area_cycle]
  have hs (i : Fin 3) :
      segmentCrossingSign (triangleStart a b c i) (triangleEnd a b c i) d e =
        if 0<r i ∧ r i<1 then slopeSign (b' i) *
          (∏ j : Fin 3, if j=i then 1 else positiveIndicator
            (orient2 (triangleStart a b c j) (triangleEnd a b c j) (segmentPoint d e (r i)))) else 0 := by
    fin_cases i
    · simpa [r,b',triangleStart,triangleEnd,Fin.prod_univ_succ] using
        segmentCrossingSign_triangle_event a b c d e harea (hn 0)
    · simpa [r,b',triangleStart,triangleEnd,Fin.prod_univ_succ,mul_comm] using
        segmentCrossingSign_triangle_event b c a d e hc1 (hn 1)
    · simpa [r,b',triangleStart,triangleEnd,Fin.prod_univ_succ] using
        segmentCrossingSign_triangle_event c a b d e hc2 (hn 2)
  have h := sum_affine_side_events_unordered 3 r b' hr hn h0 h1
  simp_rw [hf] at h
  simp only [segmentPoint_one,segmentPoint_zero] at h
  calc
    triangleSegmentIntersection a b c d e =
        ∑ i : Fin 3, segmentCrossingSign (triangleStart a b c i) (triangleEnd a b c i) d e := by
      simp [triangleSegmentIntersection,triangleStart,triangleEnd,Fin.sum_univ_succ]
      ring
    _ = _ := by simpa only [hs,triangleIndicator] using h

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TriangleTransversality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem triangle_consecutive_roots_ne (a b c d e : Plane)
    (ha : orient2 a b c ≠ 0) (h₀ : det2 (b-a) (e-d) ≠ 0)
    (h₁ : det2 (c-b) (e-d) ≠ 0) (hb : orient2 d e b ≠ 0) :
    secondIntersectionParameter a b d e ≠ secondIntersectionParameter b c d e := by
  intro heq
  have hz : orient2 b c (segmentPoint a b (firstIntersectionParameter a b d e)) = 0 := by
    rw [intersection_parameters_eq a b d e h₀,heq,
      ← intersection_parameters_eq b c d e h₁,orient2_self_segment]
  rw [triangle_side_at_first_edge] at hz
  have ht : firstIntersectionParameter a b d e = 1 := by
    have := (mul_eq_zero.mp hz).resolve_right ha
    linarith
  have hp := intersection_parameters_eq a b d e h₀
  rw [ht,segmentPoint_one] at hp
  apply hb
  rw [hp,orient2_self_segment]

theorem second_parameter_ne_zero (a b c d : Plane)
    (hn : det2 (b-a) (d-c) ≠ 0) (hc : orient2 a b c ≠ 0) :
    secondIntersectionParameter a b c d ≠ 0 := by
  intro h
  have hh := affine_side_factor a b c d hn 0
  rw [h,segmentPoint_zero] at hh
  apply hc
  simpa using hh

theorem second_parameter_ne_one (a b c d : Plane)
    (hn : det2 (b-a) (d-c) ≠ 0) (hd : orient2 a b d ≠ 0) :
    secondIntersectionParameter a b c d ≠ 1 := by
  intro h
  have hh := affine_side_factor a b c d hn 1
  rw [h,segmentPoint_one] at hh
  apply hd
  simpa using hh

theorem triangle_roots_injective (a b c d e : Plane) (ha : orient2 a b c ≠ 0)
    (h : TriangleSegmentPosition a b c d e) :
    Function.Injective (fun i : Fin 3 =>
      secondIntersectionParameter (triangleStart a b c i) (triangleEnd a b c i) d e) := by
  have h₀ := triangle_consecutive_roots_ne a b c d e ha (h.1 0) (h.1 1) (h.2.1 1)
  have ha₁ : orient2 b c a ≠ 0 := by rwa [triangle_area_cycle]
  have ha₂ : orient2 c a b ≠ 0 := by rwa [triangle_area_cycle,triangle_area_cycle]
  have h₁ := triangle_consecutive_roots_ne b c a d e ha₁ (h.1 1) (h.1 2) (h.2.1 2)
  have h₂ := triangle_consecutive_roots_ne c a b d e ha₂ (h.1 2) (h.1 0) (h.2.1 0)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [triangleStart,triangleEnd]

theorem triangle_segment_entry_exit_of_position (a b c d e : Plane)
    (ha : 0 < orient2 a b c) (h : TriangleSegmentPosition a b c d e) :
    triangleSegmentIntersection a b c d e = triangleIndicator a b c e-triangleIndicator a b c d := by
  exact triangle_segment_entry_exit a b c d e ha h.1
    (triangle_roots_injective a b c d e (ne_of_gt ha) h)
    (fun i => second_parameter_ne_zero _ _ _ _ (h.1 i) (h.2.2 i).1)
    (fun i => second_parameter_ne_one _ _ _ _ (h.1 i) (h.2.2 i).2)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TriangleOrientations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical

theorem orient2_reverse_edge (a b c : Plane) : orient2 b a c = -orient2 a b c := by
  dsimp [orient2,det2]
  ring

theorem det2_reverse_edge (a b c d : Plane) : det2 (a-b) (d-c) = -det2 (b-a) (d-c) := by
  dsimp [det2]
  ring

theorem triangle_position_reverse (a b c d e : Plane)
    (h : TriangleSegmentPosition a b c d e) : TriangleSegmentPosition a c b d e := by
  refine ⟨?_,?_,?_⟩
  · intro i
    fin_cases i
    · change det2 (c-a) (e-d) ≠ 0
      rw [det2_reverse_edge c a d e]
      exact neg_ne_zero.mpr (h.1 2)
    · change det2 (b-c) (e-d) ≠ 0
      rw [det2_reverse_edge b c d e]
      exact neg_ne_zero.mpr (h.1 1)
    · change det2 (a-b) (e-d) ≠ 0
      rw [det2_reverse_edge a b d e]
      exact neg_ne_zero.mpr (h.1 0)
  · intro i
    fin_cases i
    · exact h.2.1 0
    · exact h.2.1 2
    · exact h.2.1 1
  · intro i
    fin_cases i
    · change orient2 a c d ≠ 0 ∧ orient2 a c e ≠ 0
      rw [orient2_reverse_edge c a d,orient2_reverse_edge c a e]
      exact ⟨neg_ne_zero.mpr (h.2.2 2).1,neg_ne_zero.mpr (h.2.2 2).2⟩
    · change orient2 c b d ≠ 0 ∧ orient2 c b e ≠ 0
      rw [orient2_reverse_edge b c d,orient2_reverse_edge b c e]
      exact ⟨neg_ne_zero.mpr (h.2.2 1).1,neg_ne_zero.mpr (h.2.2 1).2⟩
    · change orient2 b a d ≠ 0 ∧ orient2 b a e ≠ 0
      rw [orient2_reverse_edge a b d,orient2_reverse_edge a b e]
      exact ⟨neg_ne_zero.mpr (h.2.2 0).1,neg_ne_zero.mpr (h.2.2 0).2⟩

theorem triangle_intersection_reverse (a b c d e : Plane) :
    triangleSegmentIntersection a c b d e = -triangleSegmentIntersection a b c d e := by
  unfold triangleSegmentIntersection
  rw [segmentCrossingSign_reverse_left c a d e,
    segmentCrossingSign_reverse_left b c d e,segmentCrossingSign_reverse_left a b d e]
  ring

theorem oriented_triangle_entry_exit (a b c d e : Plane) (ha : orient2 a b c ≠ 0)
    (h : TriangleSegmentPosition a b c d e) :
    triangleSegmentIntersection a b c d e =
      orientedTriangleIndicator a b c e-orientedTriangleIndicator a b c d := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hac : 0 < orient2 a c b := by
      rw [triangle_area_cycle b a c,orient2_reverse_edge]
      exact neg_pos.mpr ha
    have hh := triangle_segment_entry_exit_of_position a c b d e hac (triangle_position_reverse a b c d e h)
    rw [triangle_intersection_reverse] at hh
    simp only [orientedTriangleIndicator,not_lt.mpr ha.le,ite_false]
    linarith
  · simpa only [orientedTriangleIndicator,ha,ite_true] using triangle_segment_entry_exit_of_position a b c d e ha h

theorem triangle_closed_walk_intersection_zero (a b c : Plane) (ha : orient2 a b c ≠ 0)
    (w : ℕ → Plane) (m : ℕ) (hw : w m = w 0)
    (h : ∀ j ∈ Finset.range m, TriangleSegmentPosition a b c (w j) (w (j+1))) :
    (∑ j ∈ Finset.range m, triangleSegmentIntersection a b c (w j) (w (j+1))) = 0 := by
  have hs := telescoping_real_sum (fun j => orientedTriangleIndicator a b c (w j)) m
  rw [hw,sub_self,Finset.sum_sub_distrib] at hs
  calc
    _ = ∑ j ∈ Finset.range m,
        (orientedTriangleIndicator a b c (w (j+1))-orientedTriangleIndicator a b c (w j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact oriented_triangle_entry_exit a b c _ _ ha (h j hj)
    _ = 0 := by rw [Finset.sum_sub_distrib]; linarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_GenericPointFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_generic_point_family {κ ν : Type*} [Fintype κ] [Fintype ν]
    (q : ν → Plane) (a v : κ → Plane) (hv : ∀ k, v k ≠ 0)
    (n : ℕ) (z : Fin n → Plane) (ε : Fin n → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ p : Fin n → Plane, (∀ i, dist (p i) (z i) < ε i) ∧ Function.Injective p ∧
      (∀ i j, q j ≠ p i) ∧
      (∀ i k, det2 (p i-a k) (v k) ≠ 0) ∧
      (∀ i j, i ≠ j → ∀ k, det2 (p j-p i) (v k) ≠ 0) ∧
      (∀ i j, i ≠ j → ∀ l, orient2 (p i) (p j) (q l) ≠ 0) := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0,?_,?_,?_,?_,?_,?_⟩ <;> intro i <;> exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨p,hp,hinj,hpq,hline,hpar,hcorn⟩ :=
      ih (fun i => z i.succ) (fun i => ε i.succ) (fun i => hε i.succ)
    obtain ⟨x,hx,hxp,hxq,hxl,hxpar,hxcorn⟩ :=
      exists_generic_point_extension p q a v hv hpq (z 0) (ε 0) (hε 0)
    refine ⟨Fin.cons x p,?_,?_,?_,?_,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hx
      · exact hp i
    · apply Fin.cons_injective_of_injective _ hinj
      rintro ⟨i,hi⟩
      exact hxp i hi.symm
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hxq
      · exact hpq i
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hxl
      · exact hline i
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro h
          exact False.elim (h rfl)
        · intro _ k
          change det2 (p j-x) (v k) ≠ 0
          have hh : det2 (p j-x) (v k) = -det2 (x-p j) (v k) := by
            dsimp [det2]
            ring
          rw [hh]
          exact neg_ne_zero.mpr (hxpar j k)
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _ k
          exact hxpar i k
        · intro hij k
          exact hpar i j (fun h => hij (congrArg Fin.succ h)) k
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro h
          exact False.elim (h rfl)
        · intro _ l
          change orient2 x (p j) (q l) ≠ 0
          rw [orient2_reverse_edge]
          exact neg_ne_zero.mpr (hxcorn j l)
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _ l
          exact hxcorn i l
        · intro hij l
          exact hcorn i j (fun h => hij (congrArg Fin.succ h)) l

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ConeIntersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem polygon_intersection_zero_of_cone (v w : ℕ → Plane) (n m : ℕ)
    (hv : v n = v 0) (hw : w m = w 0) (o : Plane)
    (ha : ∀ i ∈ Finset.range n, orient2 o (v i) (v (i+1)) ≠ 0)
    (hp : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range m,
      TriangleSegmentPosition o (v i) (v (i+1)) (w j) (w (j+1))) :
    polygonIntersection v w n m = 0 := by
  unfold polygonIntersection
  calc
    _ = ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range n,
        segmentCrossingSign (v i) (v (i+1)) (w j) (w (j+1)) := Finset.sum_comm
    _ = ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range n,
        triangleSegmentIntersection o (v i) (v (i+1)) (w j) (w (j+1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (polygon_cone_cancellation v n hv o _ _).symm
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
        triangleSegmentIntersection o (v i) (v (i+1)) (w j) (w (j+1)) := Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact triangle_closed_walk_intersection_zero o _ _ (ha i hi) w m hw (hp i hi)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FiniteConePoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_polygon_cone_point (v w : ℕ → Plane) (n m : ℕ)
    (hv : ∀ i : Fin n, v (i.val+1) ≠ v i.val)
    (hw : ∀ j : Fin m, w (j.val+1) ≠ w j.val)
    (hvw : ∀ i : Fin (n+1), ∀ j : Fin (m+1), w j.val ≠ v i.val) :
    ∃ o : Plane,
      (∀ i : Fin n, orient2 o (v i.val) (v (i.val+1)) ≠ 0) ∧
      (∀ j : Fin m, orient2 (w j.val) (w (j.val+1)) o ≠ 0) ∧
      (∀ i : Fin (n+1), ∀ j : Fin m, det2 (v i.val-o) (w (j.val+1)-w j.val) ≠ 0) ∧
      (∀ i : Fin (n+1), ∀ j : Fin (m+1), orient2 o (v i.val) (w j.val) ≠ 0) := by
  let ι := (Fin n ⊕ Fin m) ⊕ ((Fin (n+1) × Fin m) ⊕ (Fin (n+1) × Fin (m+1)))
  let base : ι → Plane
    | .inl (.inl i) => v i.val
    | .inl (.inr j) => w j.val
    | .inr (.inl (i,_)) => v i.val
    | .inr (.inr (i,_)) => v i.val
  let direction : ι → Plane
    | .inl (.inl i) => v (i.val+1)-v i.val
    | .inl (.inr j) => w (j.val+1)-w j.val
    | .inr (.inl (_,j)) => w (j.val+1)-w j.val
    | .inr (.inr (i,j)) => w j.val-v i.val
  have hd : ∀ k, direction k ≠ 0 := by
    rintro ((i|j)|(⟨i,j⟩|⟨i,j⟩))
    · exact sub_ne_zero.mpr (hv i)
    · exact sub_ne_zero.mpr (hw j)
    · exact sub_ne_zero.mpr (hw j)
    · exact sub_ne_zero.mpr (hvw i j)
  obtain ⟨o,_,ho⟩ := exists_near_avoiding_lines base direction hd (0 : Plane) 1 (by norm_num)
  refine ⟨o,?_,?_,?_,?_⟩
  · intro i
    rw [← triangle_area_cycle o (v i.val) (v (i.val+1))]
    change det2 (v (i.val+1)-v i.val) (o-v i.val) ≠ 0
    rw [det2_swap]
    exact neg_ne_zero.mpr (ho (.inl (.inl i)))
  · intro j
    change det2 (w (j.val+1)-w j.val) (o-w j.val) ≠ 0
    rw [det2_swap]
    exact neg_ne_zero.mpr (ho (.inl (.inr j)))
  · intro i j
    rw [det2_reverse_edge (v i.val) o (w j.val) (w (j.val+1))]
    exact neg_ne_zero.mpr (ho (.inr (.inl (i,j))))
  · intro i j
    rw [← triangle_area_cycle o (v i.val) (w j.val)]
    change det2 (w j.val-v i.val) (o-v i.val) ≠ 0
    rw [det2_swap]
    exact neg_ne_zero.mpr (ho (.inr (.inr (i,j))))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_GenericPolygonIntersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem polygon_intersection_zero_in_line_position (v w : ℕ → Plane) (n m : ℕ)
    (hc : v n = v 0) (hd : w m = w 0)
    (hv : ∀ i : Fin n, v (i.val+1) ≠ v i.val)
    (hw : ∀ j : Fin m, w (j.val+1) ≠ w j.val)
    (hvw : ∀ i : Fin (n+1), ∀ j : Fin (m+1), w j.val ≠ v i.val)
    (hp : PolygonLinePosition v w n m) : polygonIntersection v w n m = 0 := by
  obtain ⟨o,ha,hb,hpar,hcorn⟩ := exists_polygon_cone_point v w n m hv hw hvw
  apply polygon_intersection_zero_of_cone v w n m hc hd o
  · intro i hi
    exact ha ⟨i,Finset.mem_range.mp hi⟩
  · intro i hi j hj
    have hin := Finset.mem_range.mp hi
    have hjm := Finset.mem_range.mp hj
    let ii : Fin n := ⟨i,Finset.mem_range.mp hi⟩
    let jj : Fin m := ⟨j,Finset.mem_range.mp hj⟩
    let i₀ : Fin (n+1) := ⟨i,by omega⟩
    let i₁ : Fin (n+1) := ⟨i+1,by omega⟩
    let j₀ : Fin (m+1) := ⟨j,by omega⟩
    let j₁ : Fin (m+1) := ⟨j+1,by omega⟩
    refine ⟨?_,?_,?_⟩
    · intro k
      fin_cases k
      · exact hpar i₀ jj
      · exact hp.1 ii jj
      · change det2 (o-v (i+1)) (w (j+1)-w j) ≠ 0
        rw [det2_reverse_edge o (v (i+1)) (w j) (w (j+1))]
        exact neg_ne_zero.mpr (hpar i₁ jj)
    · intro k
      fin_cases k
      · exact hb jj
      · exact hp.2.1 i₀ jj
      · exact hp.2.1 i₁ jj
    · intro k
      fin_cases k
      · exact ⟨hcorn i₀ j₀,hcorn i₀ j₁⟩
      · exact ⟨hp.2.2 ii j₀,hp.2.2 ii j₁⟩
      · change orient2 (v (i+1)) o (w j) ≠ 0 ∧ orient2 (v (i+1)) o (w (j+1)) ≠ 0
        rw [orient2_reverse_edge o _ _,orient2_reverse_edge o _ _]
        exact ⟨neg_ne_zero.mpr (hcorn i₁ j₀),neg_ne_zero.mpr (hcorn i₁ j₁)⟩

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

theorem periodicPolygon_closed (n : ℕ) (hn : 0 < n) (p : Fin n → Plane) :
    periodicPolygon n hn p n = periodicPolygon n hn p 0 := by
  exact congrArg p (cyclicIndex_period n hn)

theorem cyclicIndex_succ_ne (n : ℕ) (hn : 1 < n) (i : Fin n) :
    cyclicIndex n (by omega) (i.val+1) ≠ cyclicIndex n (by omega) i.val := by
  intro h
  have he := congrArg Fin.val h
  change (i.val+1)%n = i.val%n at he
  rw [Nat.mod_eq_of_lt i.isLt] at he
  by_cases hh : i.val+1=n
  · rw [hh,Nat.mod_self] at he
    omega
  · have hlt : i.val+1<n := by omega
    rw [Nat.mod_eq_of_lt hlt] at he
    omega

theorem periodicPolygon_near (n : ℕ) (hn : 0 < n) (v : ℕ → Plane) (hv : v n=v 0)
    (p : Fin n → Plane) (ε : ℝ) (hp : ∀ i, dist (p i) (v i.val) < ε) :
    ∀ i : Fin (n+1), dist (periodicPolygon n hn p i.val) (v i.val) < ε := by
  intro i
  by_cases hi : i.val<n
  · simpa only [periodicPolygon,cyclicIndex_of_lt n hn i.val hi] using hp ⟨i.val,hi⟩
  · have hin : i.val=n := by omega
    rw [hin,periodicPolygon_closed,hv]
    simpa only [periodicPolygon,cyclicIndex_of_lt n hn 0 hn] using hp ⟨0,hn⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TransversePolygonIntersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segmentCrossingSign_self_left (a c d : Plane) : segmentCrossingSign a a c d = 0 := by
  simp [segmentCrossingSign,SegmentsCrossProperly,det2]

theorem polygon_intersection_zero_transverse (v w : ℕ → Plane) (n m : ℕ)
    (hc : v n=v 0) (hd : w m=w 0)
    (hw : ∀ j : Fin m, w (j.val+1) ≠ w j.val)
    (ht : ∀ i : Fin n, ∀ j : Fin m,
      SegmentPairTransverse (v i.val) (v (i.val+1)) (w j.val) (w (j.val+1))) :
    polygonIntersection v w n m = 0 := by
  by_cases hn : 1 < n
  · have hn0 : 0<n := by omega
    obtain ⟨ε,hε,hstable⟩ := exists_polygon_intersection_stability_radius v w n m ht
    obtain ⟨p,hnear,hinj,hpq,hline,hpar,hcorn⟩ := exists_generic_point_family
      (fun j : Fin (m+1) => w j.val) (fun j : Fin m => w j.val)
      (fun j : Fin m => w (j.val+1)-w j.val) (fun j => sub_ne_zero.mpr (hw j))
      n (fun i => v i.val) (fun _ => ε) (fun _ => hε)
    let v' := periodicPolygon n hn0 p
    have hclose : v' n=v' 0 := periodicPolygon_closed n hn0 p
    have hv' (i : Fin n) : v' (i.val+1) ≠ v' i.val :=
      hinj.ne (cyclicIndex_succ_ne n hn i)
    have hpoint (i : Fin (n+1)) (j : Fin (m+1)) : w j.val ≠ v' i.val := hpq _ j
    have hposition : PolygonLinePosition v' w n m := by
      refine ⟨?_,?_,?_⟩
      · intro i j
        exact hpar _ _ (Ne.symm (cyclicIndex_succ_ne n hn i)) j
      · intro i j
        change det2 (w (j.val+1)-w j.val) (p (cyclicIndex n hn0 i.val)-w j.val) ≠ 0
        rw [det2_swap]
        exact neg_ne_zero.mpr (hline _ j)
      · intro i j
        exact hcorn _ _ (Ne.symm (cyclicIndex_succ_ne n hn i)) j
    have hzero := polygon_intersection_zero_in_line_position v' w n m hclose hd hv' hw hpoint hposition
    have heq := hstable v' (periodicPolygon_near n hn0 v hc p ε hnear)
    rwa [heq] at hzero
  · have hn' : n=0 ∨ n=1 := by omega
    rcases hn' with rfl | rfl
    · simp [polygonIntersection]
    · simp only [polygonIntersection,Finset.sum_range_one]
      rw [hc]
      simp only [segmentCrossingSign_self_left,Finset.sum_const_zero]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ClosedPolygonIntersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem closed_polygon_intersection_zero (v w : ℕ → Plane) (n m : ℕ)
    (hc : v n=v 0) (hd : w m=w 0)
    (ht : ∀ i : Fin n, ∀ j : Fin m,
      SegmentPairTransverse (v i.val) (v (i.val+1)) (w j.val) (w (j.val+1))) :
    polygonIntersection v w n m = 0 := by
  by_cases hm : 1 < m
  · have hm0 : 0< m := by omega
    have hswap (j : Fin m) (i : Fin n) :
        SegmentPairTransverse (w j.val) (w (j.val+1)) (v i.val) (v (i.val+1)) :=
      segmentPairTransverse_swap _ _ _ _ (ht i j)
    obtain ⟨ε,hε,hstable⟩ := exists_polygon_transversality_radius w v m n hswap
    obtain ⟨p,hnear,hinj,_⟩ := exists_generic_point_family
      (fun i : Fin 0 => (Fin.elim0 i : Plane)) (fun i : Fin 0 => (Fin.elim0 i : Plane))
      (fun i : Fin 0 => (Fin.elim0 i : Plane)) (fun i => Fin.elim0 i)
      m (fun i => w i.val) (fun _ => ε) (fun _ => hε)
    let w' := periodicPolygon m hm0 p
    have hclose : w' m=w' 0 := periodicPolygon_closed m hm0 p
    have hw' (j : Fin m) : w' (j.val+1) ≠ w' j.val := hinj.ne (cyclicIndex_succ_ne m hm j)
    obtain ⟨htrans,heq⟩ := hstable w' (periodicPolygon_near m hm0 w hd p ε hnear)
    have hzero := polygon_intersection_zero_transverse v w' n m hc hclose hw'
      (fun i j => segmentPairTransverse_swap _ _ _ _ (htrans j i))
    have hrev := polygonIntersection_swap v w' n m
    rw [hzero,neg_zero,heq] at hrev
    rw [polygonIntersection_swap v w n m] at hrev
    exact neg_eq_zero.mp hrev
  · have hm' : m=0 ∨ m=1 := by omega
    rcases hm' with rfl | rfl
    · simp [polygonIntersection]
    · have hz : polygonIntersection w v 1 n = 0 := by
        simp only [polygonIntersection,Finset.sum_range_one]
        rw [hd]
        simp only [segmentCrossingSign_self_left,Finset.sum_const_zero]
      rw [polygonIntersection_swap v w n 1] at hz
      exact neg_eq_zero.mp hz

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

theorem closed_intersection_zero (P : PolygonalChain O a a) (Q : PolygonalChain T d d)
    (h : P.Transverse Q) : polygonIntersection P.vertices Q.vertices P.pieces Q.pieces=0 :=
  closed_polygon_intersection_zero _ _ _ _ (P.last.trans P.first.symm) (Q.last.trans Q.first.symm) h

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FinitePolygonalComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem finitePolygonalChain_intersection_left (O : Set Plane) (v : ℕ → Plane) (h0 : v 0 ∈ O)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) (w : ℕ → Plane) (k n : ℕ) :
    polygonIntersection (finitePolygonalChain O v h0 P n).vertices w (finitePolygonalChain O v h0 P n).pieces k=
      ∑ i ∈ Finset.range n, polygonIntersection (P i).vertices w (P i).pieces k := by
  induction n with
  | zero => simp [finitePolygonalChain,PolygonalChain.point,polygonIntersection]
  | succ n ih =>
    change polygonIntersection ((finitePolygonalChain O v h0 P n).join (P n)).vertices w
      ((finitePolygonalChain O v h0 P n).join (P n)).pieces k=_
    rw [PolygonalChain.intersection_join_left,ih,Finset.sum_range_succ]

theorem finitePolygonalChain_intersection_right (O : Set Plane) (v : ℕ → Plane) (h0 : v 0 ∈ O)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) (w : ℕ → Plane) (k n : ℕ) :
    polygonIntersection w (finitePolygonalChain O v h0 P n).vertices k (finitePolygonalChain O v h0 P n).pieces=
      ∑ i ∈ Finset.range n, polygonIntersection w (P i).vertices k (P i).pieces := by
  rw [polygonIntersection_swap,finitePolygonalChain_intersection_left]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact (polygonIntersection_swap _ _ _ _).symm

theorem finitePolygonalChain_transverse_left {O T : Set Plane} (v : ℕ → Plane) (h0 : v 0 ∈ O)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) {a b : Plane} (Q : PolygonalChain T a b)
    (n : ℕ) (h : ∀ i, i<n → (P i).Transverse Q) : (finitePolygonalChain O v h0 P n).Transverse Q := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    exact (finitePolygonalChain O v h0 P n).transverse_join_left (P n) Q
      (ih (fun i hi => h i (by omega))) (h n (by omega))

theorem finitePolygonalChain_transverse_right {O T : Set Plane} (v : ℕ → Plane) (h0 : v 0 ∈ O)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) {a b : Plane} (Q : PolygonalChain T a b)
    (n : ℕ) (h : ∀ i, i<n → Q.Transverse (P i)) : Q.Transverse (finitePolygonalChain O v h0 P n) :=
  (finitePolygonalChain O v h0 P n).transverse_swap Q
    (finitePolygonalChain_transverse_left v h0 P Q n (fun i hi => Q.transverse_swap (P i) (h i hi)))

theorem finitePolygonalChain_intersection_double {O T : Set Plane}
    (v w : ℕ → Plane) (hv : v 0 ∈ O) (hw : w 0 ∈ T)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) (Q : ∀ j, PolygonalChain T (w j) (w (j+1)))
    (n k : ℕ) :
    polygonIntersection (finitePolygonalChain O v hv P n).vertices (finitePolygonalChain T w hw Q k).vertices
      (finitePolygonalChain O v hv P n).pieces (finitePolygonalChain T w hw Q k).pieces =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range k, polygonIntersection (P i).vertices (Q j).vertices (P i).pieces (Q j).pieces := by
  rw [finitePolygonalChain_intersection_left]
  apply Finset.sum_congr rfl
  intro i hi
  exact finitePolygonalChain_intersection_right _ _ _ _ _ _ _

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_GlobalCycleIntersection
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

theorem exists_closed_cycle_intersection_radius_oai (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε| < δ →
      ∀ (d f : ℕ → (completeBipartite m n).Dart)
        (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
        (N K : ℕ), d N=d 0 → f K=f 0 →
        (∀ i, i < N → bipartiteDartEdge (d (i+1)) ≠ bipartiteDartEdge (d i)) →
        (∀ j, j < K → bipartiteDartEdge (f (j+1)) ≠ bipartiteDartEdge (f j)) →
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        (bipartiteDartSign (d i)*bipartiteDartSign (f j)*
          V.signedIntersection (bipartiteDartEdge (d i)) (bipartiteDartEdge (f j))+
            C.passageIntersection d f hd hf i j ε)=0 := by
  obtain ⟨δ,hδ,hh⟩ := C.exists_cycle_block_radius hnorm hstraight htrans
  refine ⟨δ,hδ,?_⟩
  intro ε hε hs d f hd hf N K hN hK hdi hfj
  let P := V.dartCycleChain d hd N hN
  let Q := C.shiftedCycleChain f hf K hK ε
  have hblocks (i j : ℕ) (hi : i < N) (hj : j < K) :=
    hh ε hε hs d f hd hf i j (hdi i hi) (hfj j hj)
  have hT : P.Transverse Q := by
    change (finitePolygonalChain Set.univ (V.dartCycleVertex d) (Set.mem_univ _) (V.dartCycleBlock d hd) N).Transverse
      (finitePolygonalChain Set.univ (C.shiftedCycleVertex f ε) (Set.mem_univ _) (C.shiftedCycleBlock f hf ε) K)
    apply finitePolygonalChain_transverse_left
    intro i hi
    apply finitePolygonalChain_transverse_right
    intro j hj
    exact (hblocks i j hi hj).1
  have hzero := P.closed_intersection_zero Q hT
  have hsplit : polygonIntersection P.vertices Q.vertices P.pieces Q.pieces=
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        polygonIntersection (V.dartCycleBlock d hd i).vertices (C.shiftedCycleBlock f hf ε j).vertices
          (V.dartCycleBlock d hd i).pieces (C.shiftedCycleBlock f hf ε j).pieces :=
    finitePolygonalChain_intersection_double _ _ _ _ _ _ _ _
  rw [hsplit] at hzero
  calc
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        polygonIntersection (V.dartCycleBlock d hd i).vertices (C.shiftedCycleBlock f hf ε j).vertices
          (V.dartCycleBlock d hd i).pieces (C.shiftedCycleBlock f hf ε j).pieces := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact (hblocks i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)).2.symm
    _ = 0 := hzero

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

theorem solution : type_of% @OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_closed_cycle_intersection_radius_oai := @OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_closed_cycle_intersection_radius_oai
