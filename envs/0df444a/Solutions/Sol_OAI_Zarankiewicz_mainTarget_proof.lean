-- Prove2me | solution 1 for OAI.Zarankiewicz.mainTarget_proof
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T13:20:54.995754+00:00
-- url     : https://prove2.me/submissions/4bb5df00-e8a1-445d-803d-fc334d55998a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr002
import Definitions.Def_OAIB3Zr003
import Theorems.Thm_OAI_Zarankiewicz_TruncatedSpokeCoordinates_odd_normalized_crossing_lower_bound
import Theorems.Thm_OAI_Zarankiewicz_polygonal_no_adjacent_locally_transverse

section
-- module Solutions.OAIB3_Zar.Crossing_FloorArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem axisPairs_even (r : ℕ) : axisPairs (2*r) = r*(r-1) := by
  unfold axisPairs
  have h₁ : 2*r/2 = r := by omega
  have h₂ : (2*r-1)/2 = r-1 := by omega
  rw [h₁,h₂]

theorem axisPairs_odd (r : ℕ) : axisPairs (2*r+1) = r*r := by
  unfold axisPairs
  have h₁ : (2*r+1)/2 = r := by omega
  have h₂ : (2*r+1-1)/2 = r := by omega
  rw [h₁,h₂]

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AffineIntervalRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem intervalSegment_interpolate (a b u v t : unitInterval) :
    intervalSegment (intervalSegment a b u) (intervalSegment a b v) t=
      intervalSegment a b (intervalSegment u v t) := by
  apply Subtype.ext
  dsimp [intervalSegment]
  ring

theorem segmentPoint_interpolate (a b : Plane) (u v t : ℝ) :
    segmentPoint (segmentPoint a b u) (segmentPoint a b v) t=
      segmentPoint a b ((1-t)*u+t*v) := by
  ext <;> dsimp [segmentPoint] <;> ring

theorem path_affine_restrict {a b : Plane} (γ : Path a b) (l r : unitInterval) (hlr : l < r)
    (haff : ∀ t : unitInterval, γ (intervalSegment l r t)=segmentPoint (γ l) (γ r) t.val)
    (u v : unitInterval) (hu : l ≤ u ∧ u ≤ r) (hv : l ≤ v ∧ v ≤ r) (t : unitInterval) :
    γ (intervalSegment u v t)=segmentPoint (γ u) (γ v) t.val := by
  obtain ⟨u',rfl⟩ := intervalSegment_surjective_interval l r hlr u hu
  obtain ⟨v',rfl⟩ := intervalSegment_surjective_interval l r hlr v hv
  rw [intervalSegment_interpolate,haff,haff,haff,segmentPoint_interpolate]
  rfl

end Zarankiewicz

end

end OAI
end

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
-- module Solutions.OAIB3_Zar.Crossing_GenericPolynomialBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem exists_box_avoiding_polynomials {σ κ : Type*} [Fintype κ]
    (P : κ → MvPolynomial σ ℝ) (hP : ∀ k, P k ≠ 0)
    (lo hi : σ → ℝ) (hinterval : ∀ i, lo i < hi i) :
    ∃ x : σ → ℝ, (∀ i, x i ∈ Set.Ioo (lo i) (hi i)) ∧ ∀ k, MvPolynomial.eval x (P k) ≠ 0 := by
  classical
  let Q := ∏ k, P k
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hP k)
  have hex : ∃ x : σ → ℝ, (∀ i, x i ∈ Set.Ioo (lo i) (hi i)) ∧ MvPolynomial.eval x Q ≠ 0 := by
    by_contra hh
    apply hQ
    apply MvPolynomial.funext_set (fun i => Set.Ioo (lo i) (hi i)) (fun i => Set.Ioo_infinite (hinterval i))
    intro x hx
    rw [map_zero]
    by_contra hz
    exact hh ⟨x,fun i => hx i (Set.mem_univ i),hz⟩
  obtain ⟨x,hx,hval⟩ := hex
  refine ⟨x,hx,?_⟩
  have he : (∏ k, MvPolynomial.eval x (P k)) ≠ 0 := by simpa only [Q,map_prod] using hval
  exact fun k => (Finset.prod_ne_zero_iff.mp he) k (Finset.mem_univ k)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AxisConcurrency
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open MvPolynomial
variable {m n : ℕ}

theorem axisConcurrencyPolynomial_eval (e f g : BipartiteEdge m n) (x : BipartiteVertex m n → ℝ) :
    eval x (axisConcurrencyPolynomial e f g)=
      axisConcurrency (x (Sum.inl e.1)) (x (Sum.inr e.2)) (x (Sum.inl f.1)) (x (Sum.inr f.2))
        (x (Sum.inl g.1)) (x (Sum.inr g.2)) := by
  simp [axisConcurrencyPolynomial,axisConcurrency]

theorem axisConcurrencyPolynomial_ne_zero (e f g : BipartiteEdge m n)
    (hef : e.1 ≠ f.1) (hgf : g.1 ≠ f.1) (hfe : f.2 ≠ e.2) (hge : g.2 ≠ e.2) :
    axisConcurrencyPolynomial e f g ≠ 0 := by
  let x : BipartiteVertex m n → ℝ
    | .inl i => if i=f.1 then 0 else 1
    | .inr p => if p=e.2 then 0 else 1
  intro h
  have hh := congrArg (eval x) h
  rw [axisConcurrencyPolynomial_eval] at hh
  norm_num [x,axisConcurrency,hef,hgf,hfe,hge] at hh

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AxisGenericPositions
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem exists_axis_generic_positions (lo hi : BipartiteVertex m n → ℝ)
    (hinterval : ∀ j, lo j < hi j) :
    ∃ x : BipartiteVertex m n → ℝ, (∀ j, x j ∈ Set.Ioo (lo j) (hi j)) ∧
      ∀ e f g : BipartiteEdge m n, AxisIndependentTriple e f g →
        axisConcurrency (x (Sum.inl e.1)) (x (Sum.inr e.2)) (x (Sum.inl f.1)) (x (Sum.inr f.2))
          (x (Sum.inl g.1)) (x (Sum.inr g.2)) ≠ 0 := by
  classical
  let P : (BipartiteEdge m n × BipartiteEdge m n × BipartiteEdge m n) → MvPolynomial (BipartiteVertex m n) ℝ :=
    fun t => if AxisIndependentTriple t.1 t.2.1 t.2.2 then axisConcurrencyPolynomial t.1 t.2.1 t.2.2 else 1
  have hP : ∀ t, P t ≠ 0 := by
    intro t
    dsimp only [P]
    split_ifs with h
    · exact axisConcurrencyPolynomial_ne_zero _ _ _ h.1 (Ne.symm h.2.2.1)
        (Ne.symm h.2.2.2.1) (Ne.symm h.2.2.2.2.1)
    · exact one_ne_zero
  obtain ⟨x,hx,havoid⟩ := exists_box_avoiding_polynomials P hP lo hi hinterval
  refine ⟨x,hx,?_⟩
  intro e f g htriple
  have hh := havoid (e,f,g)
  simpa only [P,ite_eq_left htriple,axisConcurrencyPolynomial_eval] using hh

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CrossingIncidence
attribute [-instance] _root_.OAI.Zarankiewicz.admissibleToFiniteIntersectionDrawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical
variable {m n : ℕ}

theorem crossing_incident_iff (D : AdmissibleDrawing m n) (x : Plane)
    (e f : BipartiteEdge m n) (hef : e ≠ f)
    (he : x ∈ edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ edgeInterior D.toContinuousDrawing f) (g : BipartiteEdge m n) :
    x ∈ edgeInterior D.toContinuousDrawing g ↔ g = e ∨ g = f := by
  constructor
  · intro hg
    by_contra hh
    have hge : e ≠ g := by tauto
    have hgf : f ≠ g := by tauto
    have hmem : x ∈ edgeInterior D.toContinuousDrawing e ∩ edgeInterior D.toContinuousDrawing f ∩
        edgeInterior D.toContinuousDrawing g := ⟨⟨he,hf⟩,hg⟩
    rw [D.no_triples e f g hef hge hgf] at hmem
    exact hmem
  · rintro (rfl | rfl) <;> assumption

theorem pairCrossings_self (D : AdmissibleDrawing m n) (e : BipartiteEdge m n) :
    pairCrossings D e e = ∅ := by
  simp [pairCrossings]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_BalancedAxisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem axisInterval_nonempty (r : ℕ) (i : Fin r) : axisIntervalLo r i < axisIntervalHi r i := by
  unfold axisIntervalLo axisIntervalHi
  split_ifs <;> linarith

theorem axisInterval_sign (r : ℕ) (i : Fin r) (x : ℝ)
    (hx : x ∈ Set.Ioo (axisIntervalLo r i) (axisIntervalHi r i)) :
    (0 < x ↔ i.val < r/2) ∧ (x < 0 ↔ r/2 ≤ i.val) := by
  have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  by_cases h : i.val < r/2
  · simp only [axisIntervalLo,axisIntervalHi,ite_eq_left h,Set.mem_Ioo] at hx
    have hp : 0 < x := by linarith [hx.1]
    simp [hp,h,not_lt_of_ge hp.le,Nat.not_le.mpr h]
  · simp only [axisIntervalLo,axisIntervalHi,ite_eq_right h,Set.mem_Ioo] at hx
    have hn : x < 0 := by linarith [hx.2]
    simp [hn,h,not_lt_of_ge hn.le,Nat.le_of_not_gt h]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_BalancedAxisDrawing
attribute [-instance] _root_.OAI.Zarankiewicz.admissibleToFiniteIntersectionDrawing _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem nonempty_balancedAxisRealization (m n : ℕ) : Nonempty (BalancedAxisRealization m n) := by
  let lo : BipartiteVertex m n → ℝ
    | .inl i => axisIntervalLo m i
    | .inr p => axisIntervalLo n p
  let hi : BipartiteVertex m n → ℝ
    | .inl i => axisIntervalHi m i
    | .inr p => axisIntervalHi n p
  have hinterval : ∀ j, lo j < hi j := by
    rintro (i|p)
    · exact axisInterval_nonempty m i
    · exact axisInterval_nonempty n p
  obtain ⟨x,hx,hgeneric⟩ := exists_axis_generic_positions lo hi hinterval
  exact ⟨⟨fun i => x (Sum.inl i),fun p => x (Sum.inr p),fun i => hx (Sum.inl i),
    fun p => hx (Sum.inr p),hgeneric⟩⟩

namespace BalancedAxisRealization
variable {m n : ℕ} (R : BalancedAxisRealization m n)

theorem vertical_abs_strictMono : StrictMono (fun i => |R.vertical i|) := axisInterval_abs_strictMono m _ R.vertical_interval
theorem horizontal_abs_strictMono : StrictMono (fun p => |R.horizontal p|) := axisInterval_abs_strictMono n _ R.horizontal_interval

theorem drawing_edgeInterior (e : BipartiteEdge m n) :
    edgeInterior R.drawing.toContinuousDrawing e=openSegmentTrace (0,R.vertical e.1) (R.horizontal e.2,0) :=
  axisContinuousDrawing_interior R.vertical R.horizontal R.vertical_injective R.horizontal_injective
    R.vertical_ne_zero R.horizontal_ne_zero e

end BalancedAxisRealization

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_BalancedRayPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz
open scoped Finset

theorem mem_balancedRayPairs (r : ℕ) (i k : Fin r) :
    (i,k) ∈ balancedRayPairs r ↔ i < k ∧ (i.val < r/2 ↔ k.val < r/2) := by
  simp only [balancedRayPairs,positiveRayIndices,negativeRayIndices,Finset.mem_union,
    Finset.mem_filter,Finset.mem_product,Finset.mem_univ,true_and]
  tauto

theorem positiveRayIndices_card (r : ℕ) : (positiveRayIndices r).card=r/2 := by
  cases r with
  | zero => simp [positiveRayIndices]
  | succ r =>
    let c : Fin (r+1) := ⟨(r+1)/2,by omega⟩
    have he : positiveRayIndices (r+1)=Finset.Iio c := by
      ext i
      simp only [positiveRayIndices,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio]
      rfl
    rw [he,Fin.card_Iio]

theorem negativeRayIndices_card (r : ℕ) : (negativeRayIndices r).card=r-r/2 := by
  have hh := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin r => i.val < r/2)
  change (positiveRayIndices r).card+(negativeRayIndices r).card=Finset.univ.card at hh
  rw [positiveRayIndices_card,Finset.card_univ,Fintype.card_fin] at hh
  omega

theorem twice_choose_two (s : ℕ) : 2*s.choose 2=s*(s-1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.choose_succ_succ,Nat.choose_one_right,Nat.add_sub_cancel]
    have hh : s*(s-1)+2*s=(s+1)*s := by
      cases s with
      | zero => simp
      | succ s => simp only [Nat.add_sub_cancel]; ring
    nlinarith

theorem balanced_choose_two (r : ℕ) : (r/2).choose 2+(r-r/2).choose 2=axisPairs r := by
  have hr : r=2*(r/2) ∨ r=2*(r/2)+1 := by omega
  rcases hr with hr | hr
  · generalize r/2=s at hr
    subst r
    rw [show 2*s-s=s by omega,axisPairs_even]
    have hh := twice_choose_two s
    omega
  · generalize r/2=s at hr
    subst r
    rw [show 2*s+1-s=s+1 by omega,axisPairs_odd,
      Nat.choose_succ_succ,Nat.choose_one_right]
    have hh := twice_choose_two s
    cases s with
    | zero => simp
    | succ s => simp only [Nat.add_sub_cancel] at hh; nlinarith

theorem balancedRayPairs_card (r : ℕ) : (balancedRayPairs r).card=axisPairs r := by
  have hd : Disjoint
      ((positiveRayIndices r ×ˢ positiveRayIndices r).filter (fun p => p.1 < p.2))
      ((negativeRayIndices r ×ˢ negativeRayIndices r).filter (fun p => p.1 < p.2)) := by
    apply Finset.disjoint_left.mpr
    rintro ⟨i,k⟩ hp hn
    simp only [Finset.mem_filter,Finset.mem_product,positiveRayIndices,negativeRayIndices,
      Finset.mem_univ,true_and] at hp hn
    exact hn.1.1 hp.1.1
  rw [balancedRayPairs,Finset.card_union_of_disjoint hd,Finset.card_product_filter_lt,
    Finset.card_product_filter_lt,positiveRayIndices_card,negativeRayIndices_card,balanced_choose_two]

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AxisCrossingOrder
attribute [-instance] _root_.OAI.Zarankiewicz.admissibleToFiniteIntersectionDrawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem positive_scaled_eq_sign (a b t u : ℝ) (ht : 0 < t) (hu : 0 < u) (he : t*a=u*b) :
    (0 < a ↔ 0 < b) := by
  have hh : (0 < t*a ↔ 0 < a) := mul_pos_iff_of_pos_left ht
  have hh' : (0 < u*b ↔ 0 < b) := mul_pos_iff_of_pos_left hu
  rw [he] at hh
  exact hh.symm.trans hh'

theorem axis_meeting_abs_order (a b c d t u : ℝ)
    (ha : 0 < |a|) (hd : 0 < |d|) (hac : |a| < |c|)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (he : axisSegmentPoint a b t=axisSegmentPoint c d u) : |d| < |b| := by
  have hx := congrArg (fun z : Plane => |z.1|) he
  have hy := congrArg (fun z : Plane => |z.2|) he
  simp only [axisSegmentPoint_coordinates,abs_mul,abs_of_pos ht.1,abs_of_pos hu.1,
    abs_of_pos (sub_pos.mpr ht.2),abs_of_pos (sub_pos.mpr hu.2)] at hx hy
  have htu : t < u := by
    by_contra hnot
    have hgap := mul_pos (sub_pos.mpr hac) (sub_pos.mpr hu.2)
    have hdiff := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot)) ha.le
    nlinarith
  have hgap := mul_pos (sub_pos.mpr htu) hd
  have htb : t*(|b|-|d|) > 0 := by nlinarith [hx]
  exact sub_pos.mp ((mul_pos_iff_of_pos_left ht.1).mp htb)

namespace BalancedAxisRealization
variable {m n : ℕ} (R : BalancedAxisRealization m n)

theorem meeting_same_rays (i k : Fin m) (p q : Fin n) (x : Plane)
    (hx : x ∈ edgeInterior R.drawing.toContinuousDrawing (i,p))
    (hy : x ∈ edgeInterior R.drawing.toContinuousDrawing (k,q)) :
    (i.val < m/2 ↔ k.val < m/2) ∧ (p.val < n/2 ↔ q.val < n/2) := by
  rw [R.drawing_edgeInterior] at hx hy
  obtain ⟨t,ht,he⟩ := hx
  obtain ⟨u,hu,hf⟩ := hy
  have hmeet : axisSegmentPoint (R.vertical i) (R.horizontal p) t=
      axisSegmentPoint (R.vertical k) (R.horizontal q) u := he.trans hf.symm
  have hcoordx := congrArg Prod.fst hmeet
  have hcoordy := congrArg Prod.snd hmeet
  simp only [axisSegmentPoint_coordinates] at hcoordx hcoordy
  have hposx := positive_scaled_eq_sign _ _ _ _ ht.1 hu.1 hcoordx
  have hposy := positive_scaled_eq_sign _ _ _ _ (sub_pos.mpr ht.2) (sub_pos.mpr hu.2) hcoordy
  exact ⟨(axisInterval_sign m i _ (R.vertical_interval i)).1.symm.trans
      (hposy.trans (axisInterval_sign m k _ (R.vertical_interval k)).1),
    (axisInterval_sign n p _ (R.horizontal_interval p)).1.symm.trans
      (hposx.trans (axisInterval_sign n q _ (R.horizontal_interval q)).1)⟩

theorem meeting_reverse_horizontal_order (i k : Fin m) (p q : Fin n) (hik : i < k) (x : Plane)
    (hx : x ∈ edgeInterior R.drawing.toContinuousDrawing (i,p))
    (hy : x ∈ edgeInterior R.drawing.toContinuousDrawing (k,q)) : q < p := by
  rw [R.drawing_edgeInterior] at hx hy
  obtain ⟨t,ht,he⟩ := hx
  obtain ⟨u,hu,hf⟩ := hy
  have hmeet : axisSegmentPoint (R.vertical i) (R.horizontal p) t=
      axisSegmentPoint (R.vertical k) (R.horizontal q) u := he.trans hf.symm
  have hh := axis_meeting_abs_order _ _ _ _ t u (abs_pos.mpr (R.vertical_ne_zero i))
    (abs_pos.mpr (R.horizontal_ne_zero q)) (R.vertical_abs_strictMono hik) ht hu hmeet
  by_contra hnot
  have hle := R.horizontal_abs_strictMono.monotone (le_of_not_gt hnot)
  exact not_lt_of_ge hle hh

theorem meeting_balanced_pairs (i k : Fin m) (p q : Fin n) (hik : i < k) (x : Plane)
    (hx : x ∈ edgeInterior R.drawing.toContinuousDrawing (i,p))
    (hy : x ∈ edgeInterior R.drawing.toContinuousDrawing (k,q)) :
    (i,k) ∈ balancedRayPairs m ∧ (q,p) ∈ balancedRayPairs n := by
  obtain ⟨hvert,hhor⟩ := R.meeting_same_rays i k p q x hx hy
  exact ⟨(mem_balancedRayPairs m i k).mpr ⟨hik,hvert⟩,
    (mem_balancedRayPairs n q p).mpr ⟨R.meeting_reverse_horizontal_order i k p q hik x hx hy,hhor.symm⟩⟩

end BalancedAxisRealization
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingDeletion
attribute [-instance] _root_.OAI.Zarankiewicz.admissibleToFiniteIntersectionDrawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical
variable {m n : ℕ}

theorem crossing_survives_deletion_iff (D : AdmissibleDrawing m (n+1))
    (v : Fin (n+1)) (x : Plane) (e f : BipartiteEdge m (n+1)) (hef : e ≠ f)
    (he : x ∈ edgeInterior D.toContinuousDrawing e) (hf : x ∈ edgeInterior D.toContinuousDrawing f) :
    x ∈ crossingPoints (deleteRightVertex D v).toContinuousDrawing ↔ e.2 ≠ v ∧ f.2 ≠ v := by
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    let emb := (Fin.succAboveOrderEmb v).toEmbedding
    have hab' : restrictEdge emb a ≠ restrictEdge emb b := (restrictEdge emb).injective.ne hab
    have hae : e = restrictEdge emb a ∨ e = restrictEdge emb b :=
      (crossing_incident_iff D x (restrictEdge emb a) (restrictEdge emb b) hab' ha hb e).mp he
    have haf : f = restrictEdge emb a ∨ f = restrictEdge emb b :=
      (crossing_incident_iff D x (restrictEdge emb a) (restrictEdge emb b) hab' ha hb f).mp hf
    constructor
    · rcases hae with rfl | rfl <;> exact Fin.succAbove_ne v _
    · rcases haf with rfl | rfl <;> exact Fin.succAbove_ne v _
  · rintro ⟨hev,hfv⟩
    obtain ⟨a,ha⟩ := Fin.exists_succAbove_eq hev
    obtain ⟨b,hb⟩ := Fin.exists_succAbove_eq hfv
    let emb := (Fin.succAboveOrderEmb v).toEmbedding
    have hea : restrictEdge emb (e.1,a) = e := Prod.ext rfl ha
    have hfb : restrictEdge emb (f.1,b) = f := Prod.ext rfl hb
    refine ⟨(e.1,a),(f.1,b),?_,?_,?_⟩
    · intro hab
      apply hef
      rw [← hea, ← hfb, hab]
    · change x ∈ edgeInterior D.toContinuousDrawing (restrictEdge emb (e.1,a))
      rwa [hea]
    · change x ∈ edgeInterior D.toContinuousDrawing (restrictEdge emb (f.1,b))
      rwa [hfb]

theorem crossing_columns_ne (D : AdmissibleDrawing m n) (hnorm : NoAdjacentCrossings D)
    (x : Plane) (e f : BipartiteEdge m n) (hef : e ≠ f)
    (he : x ∈ edgeInterior D.toContinuousDrawing e) (hf : x ∈ edgeInterior D.toContinuousDrawing f) :
    e.2 ≠ f.2 := by
  intro hcol
  have hh : x ∈ edgeInterior D.toContinuousDrawing e ∩ edgeInterior D.toContinuousDrawing f := ⟨he,hf⟩
  rw [hnorm e f hef (Or.inr hcol)] at hh
  exact hh

theorem two_excluded_indices (a b : Fin (n+1)) (hab : a ≠ b) :
    (∑ v : Fin (n+1), if a ≠ v ∧ b ≠ v then (1 : ℕ) else 0) = (n+1)-2 := by
  have he : (Finset.univ.filter (fun v : Fin (n+1) => a ≠ v ∧ b ≠ v)) =
      (Finset.univ.erase a).erase b := by
    ext v
    simp [ne_comm, and_comm]
  rw [← Finset.card_filter, he, Finset.card_erase_of_mem (by simp [hab.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
  omega

theorem crossing_deletion_multiplicity (D : AdmissibleDrawing m (n+1))
    (hnorm : NoAdjacentCrossings D) (x : Plane) (hx : x ∈ crossingPoints D.toContinuousDrawing) :
    (∑ v : Fin (n+1), if x ∈ crossingPoints (deleteRightVertex D v).toContinuousDrawing
      then (1 : ℕ) else 0) = (n+1)-2 := by
  obtain ⟨e,f,hef,he,hf⟩ := hx
  simp_rw [crossing_survives_deletion_iff D _ x e f hef he hf]
  exact two_excluded_indices e.2 f.2 (crossing_columns_ne D hnorm x e f hef he hf)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DeletionCount
attribute [-instance] _root_.OAI.Zarankiewicz.admissibleToFiniteIntersectionDrawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical
variable {m n : ℕ}

theorem delete_crossing_finset (D : AdmissibleDrawing m (n+1)) (v : Fin (n+1)) :
    (deleteRightVertex D v).crossings_finite.toFinset =
      D.crossings_finite.toFinset.filter
        (fun x => x ∈ crossingPoints (deleteRightVertex D v).toContinuousDrawing) := by
  ext x
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
  exact ⟨fun h => ⟨restrict_crossingPoints_subset D.toContinuousDrawing _ h,h⟩, And.right⟩

theorem sum_delete_crossingCount (D : AdmissibleDrawing m (n+1))
    (hnorm : NoAdjacentCrossings D) :
    (∑ v : Fin (n+1), crossingCount (deleteRightVertex D v)) = ((n+1)-2)*crossingCount D := by
  simp only [crossingCount, delete_crossing_finset, Finset.card_filter]
  rw [Finset.sum_comm]
  have he : ∀ x ∈ D.crossings_finite.toFinset,
      (∑ v : Fin (n+1), if x ∈ crossingPoints (deleteRightVertex D v).toContinuousDrawing
        then (1 : ℕ) else 0) = (n+1)-2 := by
    intro x hx
    exact crossing_deletion_multiplicity D hnorm x (by simpa using hx)
  rw [Finset.sum_congr rfl he]
  simp [Nat.mul_comm]

theorem even_deletion_floor (s : ℕ) :
    (2*s)*axisPairs (2*s-1) = (2*s-2)*axisPairs (2*s) := by
  cases s with
  | zero => simp
  | succ s =>
    have h₁ : 2*(s+1)-1 = 2*s+1 := by omega
    have h₂ : 2*(s+1)-2 = 2*s := by omega
    rw [h₁, h₂, axisPairs_odd, axisPairs_even, Nat.add_sub_cancel]
    ring

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
-- module Solutions.OAIB3_Zar.Crossing_RoundDiskClearance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical Topology

theorem dist_le_of_mem_closedRoundDisk (z x : Plane) (r : ℝ) (hr : 0 ≤ r)
    (hx : x ∈ closedRoundDisk z r) : dist x z ≤ r := by
  change (x.1-z.1)^2+(x.2-z.2)^2 ≤ r^2 at hx
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_le_iff,abs_le,abs_le]
  have h₁ := sq_nonneg (x.1-z.1)
  have h₂ := sq_nonneg (x.2-z.2)
  constructor <;> constructor <;> nlinarith

theorem exists_round_disk_clearance {ι : Type*} [Fintype ι]
    (z : ι → Plane) (K : ι → Set Plane) (hK : ∀ i, IsCompact (K i))
    (hz : ∀ i, z i ∉ K i) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, Disjoint (closedRoundDisk (z i) r) (K i) := by
  have hex (i : ι) : ∃ ε : ℝ, 0 < ε ∧ Metric.ball (z i) ε ⊆ (K i)ᶜ :=
    Metric.mem_nhds_iff.mp ((hK i).isClosed.isOpen_compl.mem_nhds (hz i))
  choose radius hpos hclear using hex
  obtain ⟨r,hr,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun i _ => hpos i)
  refine ⟨r,hr,?_⟩
  intro i
  apply Set.disjoint_left.mpr
  intro x hx hmem
  have hd := dist_le_of_mem_closedRoundDisk (z i) x r hr.le hx
  exact hclear i (hd.trans_lt (hbound i (Finset.mem_univ _))) hmem

theorem exists_disjoint_round_disks {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → Plane) (hz : Function.Injective z) :
    ∃ r : ℝ, 0 < r ∧ ∀ i j, i ≠ j → Disjoint (closedRoundDisk (z i) r) (closedRoundDisk (z j) r) := by
  obtain ⟨δ,hδ,hgap⟩ := finite_positive_lower_bound
    (Finset.univ.filter (fun ij : ι × ι => ij.1 ≠ ij.2)) (fun ij => dist (z ij.1) (z ij.2)) (by
      intro ij hij
      exact dist_pos.mpr (hz.ne (Finset.mem_filter.mp hij).2))
  refine ⟨δ/3,by positivity,?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h₁ := dist_le_of_mem_closedRoundDisk (z i) x (δ/3) (by positivity) hx
  have h₂ := dist_le_of_mem_closedRoundDisk (z j) x (δ/3) (by positivity) hy
  have htri := dist_triangle (z i) x (z j)
  rw [dist_comm (z i) x] at htri
  have hg := hgap (i,j) (by simpa using hij)
  linarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_MarkedCurveDisks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem closedRoundDisk_mono (z : Plane) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    closedRoundDisk z r ⊆ closedRoundDisk z s := by
  intro x hx
  change squaredLength (x-z) ≤ r^2 at hx
  change squaredLength (x-z) ≤ s^2
  nlinarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SortedMarkedParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_sorted_unitInterval_finset (S : Finset unitInterval)
    (h0 : (0 : unitInterval) ∈ S) (h1 : (1 : unitInterval) ∈ S) :
    ∃ k : ℕ, 0 < k ∧ ∃ t : Fin (k+1) → unitInterval,
      StrictMono t ∧ t 0=0 ∧ t (Fin.last k)=1 ∧ Set.range t=(S : Set unitInterval) := by
  have hc : 1 < S.card := Finset.one_lt_card.mpr ⟨0,h0,1,h1,zero_ne_one⟩
  let k := S.card-1
  have hk : 0 < k := by dsimp [k]; omega
  have hcard : S.card=k+1 := by dsimp [k]; omega
  let e := S.orderEmbOfFin hcard
  have hrange : Set.range e=(S : Set unitInterval) := Finset.range_orderEmbOfFin S hcard
  obtain ⟨i,hi⟩ : ∃ i, e i=0 := by
    have hm : (0 : unitInterval) ∈ Set.range e := hrange.symm ▸ h0
    exact hm
  obtain ⟨j,hj⟩ : ∃ j, e j=1 := by
    have hm : (1 : unitInterval) ∈ Set.range e := hrange.symm ▸ h1
    exact hm
  have he0 : e 0=0 := by
    apply le_antisymm
    · exact (e.monotone (Fin.zero_le i)).trans_eq hi
    · exact (e 0).property.1
  have he1 : e (Fin.last k)=1 := by
    apply le_antisymm
    · exact (e (Fin.last k)).property.2
    · exact hj.symm.trans_le (e.monotone (Fin.le_last j))
  exact ⟨k,hk,e,e.strictMono,he0,he1,hrange⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_IntervalSegmentStrict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem intervalSegment_strict_between (a b t : unitInterval) (hab : a < b)
    (ht : t ∈ Set.Ioo (0 : unitInterval) 1) :
    a < intervalSegment a b t ∧ intervalSegment a b t < b := by
  have hab' : a.val < b.val := hab
  have ht0 : 0 < t.val := ht.1
  have ht1 : t.val < 1 := ht.2
  have h₀ := mul_pos ht0 (sub_pos.mpr hab')
  have h₁ := mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hab')
  change a.val < (1-t.val)*a.val+t.val*b.val ∧ (1-t.val)*a.val+t.val*b.val < b.val
  constructor <;> nlinarith

end Zarankiewicz

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

theorem circlePoint_injective : Function.Injective circlePoint := by
  intro a b hab
  have hh := congrArg (fun z : Plane => z.2/(1+z.1)) hab
  simpa only [circlePoint_parameter] using hh

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
-- module Solutions.OAIB3_Zar.Crossing_PolygonalChainExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_minimum_polygonalChain {O : Set Plane} {a b : Plane}
    (h : Nonempty (PolygonalChain O a b)) :
    ∃ P : PolygonalChain O a b, ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces := by
  classical
  obtain ⟨P⟩ := h
  have hex : ∃ n : ℕ, ∃ Q : PolygonalChain O a b, Q.pieces=n := ⟨P.pieces,P,rfl⟩
  obtain ⟨Q,hQ⟩ := Nat.find_spec hex
  refine ⟨Q,?_⟩
  intro R
  rw [hQ]
  exact Nat.find_min' hex ⟨R,rfl⟩

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

theorem adjacent_segments_meet_only_at_bend (a b c : Plane)
    (h : det2 (b-a) (c-b) ≠ 0) {x : Plane}
    (hx : x ∈ segment ℝ a b) (hy : x ∈ segment ℝ b c) : x=b := by
  rw [← Path.range_segment] at hx hy
  obtain ⟨s,hs⟩ := hx
  obtain ⟨t,ht⟩ := hy
  have hs' : segmentPoint a b s.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs
  have ht' : segmentPoint b c t.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  have he := segment_intersection_parameters_unique a b b c h s.val t.val 1 0
    (hs'.trans ht'.symm) (by simp)
  rw [he.1,segmentPoint_one] at hs'
  exact hs'.symm

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

theorem minimum_adjacent_intersection (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) {x : Plane}
    (hx : x ∈ segment ℝ (P.vertices i) (P.vertices (i+1)))
    (hy : x ∈ segment ℝ (P.vertices (i+1)) (P.vertices (i+2))) : x=P.vertices (i+1) := by
  exact adjacent_segments_meet_only_at_bend _ _ _ (P.minimum_bend_det_ne_zero hmin i hi) hx hy

end PolygonalChain
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalArcInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem minimum_path_injective (P : PolygonalChain O a b) (hab : a ≠ b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces) : Function.Injective P.path := by
  have hp : 0 < P.pieces := by
    by_contra h
    have hz : P.pieces=0 := by omega
    exact hab (P.first.symm.trans (hz ▸ P.last))
  change Function.Injective (polygonalArcPath P.vertices P.pieces)
  apply polygonalArcPath_injective P.vertices P.pieces hp
  · intro i hi
    exact P.minimum_vertices_ne hmin i (i+1) (by omega) (by omega)
  · intro i j hij hj x hx hy
    by_cases he : j=i+1
    · subst j
      exact ⟨rfl,P.minimum_adjacent_intersection hmin i (by omega) hx hy⟩
    · exact False.elim ((Set.disjoint_left.mp (P.minimum_nonadjacent_disjoint hmin i j (by omega) hj)) hx hy)

end PolygonalChain

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OrderedAffineSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem strictMono_no_between_successors {k : ℕ} (t : Fin (k+1) → unitInterval)
    (ht : StrictMono t) (i : Fin k) (j : Fin (k+1)) :
    ¬ (t i.castSucc < t j ∧ t j < t i.succ) := by
  intro h
  have hlo : i.castSucc < j := by
    by_contra hn
    exact h.1.not_ge (ht.monotone (le_of_not_gt hn))
  have hhi : j < i.succ := by
    by_contra hn
    exact h.2.not_ge (ht.monotone (le_of_not_gt hn))
  change i.val < j.val at hlo
  change j.val < i.val+1 at hhi
  omega

theorem HasFiniteAffineCover.nonempty_polygonalParametrization {a b : Plane} {γ : Path a b}
    (hγ : HasFiniteAffineCover γ) : Nonempty (PolygonalParametrization γ) := by
  classical
  obtain ⟨S,hSlt,hScov,hSaff⟩ := hγ
  let T : Finset unitInterval := insert 0 (insert 1 (S.image Prod.fst ∪ S.image Prod.snd))
  obtain ⟨k,hk,t,ht,h0,h1,hR⟩ := exists_sorted_unitInterval_finset T (by simp [T]) (by simp [T])
  have hleft (ab : unitInterval × unitInterval) (hab : ab ∈ S) : ab.1 ∈ Set.range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩)))
  have hright (ab : unitInterval × unitInterval) (hab : ab ∈ S) : ab.2 ∈ Set.range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩)))
  refine ⟨{pieces:=k,knot:=t,increasing:=ht,first:=h0,last:=h1,affine:=?_}⟩
  intro i u
  let mid : unitInterval := ⟨1/2,by norm_num⟩
  let z := intervalSegment (t i.castSucc) (t i.succ) mid
  have hz : t i.castSucc < z ∧ z < t i.succ :=
    intervalSegment_strict_between _ _ mid (ht (by change i.val < i.val+1; omega)) (by
      constructor <;> change (_ : ℝ) < _ <;> norm_num [mid])
  obtain ⟨ab,hab,ha,hb⟩ := hScov z
  have hlo : ab.1 ≤ t i.castSucc := by
    by_contra hn
    obtain ⟨j,hj⟩ := hleft ab hab
    exact strictMono_no_between_successors t ht i j
      ⟨by rw [hj]; exact lt_of_not_ge hn,by rw [hj]; exact ha.trans_lt hz.2⟩
  have hhi : t i.succ ≤ ab.2 := by
    by_contra hn
    obtain ⟨j,hj⟩ := hright ab hab
    exact strictMono_no_between_successors t ht i j
      ⟨by rw [hj]; exact hz.1.trans_le hb,by rw [hj]; exact lt_of_not_ge hn⟩
  have hle : t i.castSucc ≤ t i.succ := ht.monotone (by change i.val ≤ i.val+1; omega)
  exact path_affine_restrict γ ab.1 ab.2 (hSlt ab hab) (hSaff ab hab)
    (t i.castSucc) (t i.succ) ⟨hlo,hle.trans hhi⟩ ⟨hlo.trans hle,hhi⟩ u

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ReducedPolygonalPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_reduced_polygonalChain {a b : Plane} (γ : Path a b)
    (hinj : Function.Injective γ) (hpoly : HasFiniteAffineCover γ) :
    ∃ P : PolygonalChain (Set.range γ) a b,
      Set.range P.path=Set.range γ ∧ Function.Injective P.path ∧ 0 < P.pieces ∧
      (∀ i, i < P.pieces → P.vertices (i+1)-P.vertices i ≠ 0) ∧
      (∀ i, i+2 ≤ P.pieces →
        det2 (P.vertices (i+1)-P.vertices i) (P.vertices (i+2)-P.vertices (i+1)) ≠ 0) ∧
      (∀ Q : PolygonalChain (Set.range γ) a b, P.pieces ≤ Q.pieces) := by
  have hab : a ≠ b := by
    intro h
    exact zero_ne_one (hinj (γ.source.trans (h.trans γ.target.symm)))
  obtain ⟨Q⟩ := hpoly.nonempty_polygonalParametrization
  obtain ⟨P,hmin⟩ := exists_minimum_polygonalChain ⟨Q.containedChain⟩
  exact ⟨P,path_range_eq_of_subset γ P.path hinj P.path_range_subset,
    P.minimum_path_injective hab hmin,P.pieces_pos_of_ne hab,
    P.minimum_piece_ne_zero hmin,P.minimum_bend_det_ne_zero hmin,hmin⟩

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
-- module Solutions.OAIB3_Zar.Crossing_VertexPieceClearance
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem exists_vertex_piece_clearance (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces) :
    ∃ r : ℝ, 0 < r ∧
      (∀ j k, j ≠ k → Disjoint (closedRoundDisk (D.vertex j) r) (closedRoundDisk (D.vertex k) r)) ∧
      (∀ j e (i : Fin (P e).pieces),
        ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=(P e).pieces)) →
        Disjoint (closedRoundDisk (D.vertex j) r)
          (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1)))) := by
  classical
  let Bad := Σ j : BipartiteVertex m n, Σ e : BipartiteEdge m n,
    {i : Fin (P e).pieces // ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨
      (j=Sum.inr e.2 ∧ i.val+1=(P e).pieces))}
  let K : Bad → Set Plane := fun t =>
    segment ℝ ((P t.2.1).vertices t.2.2.val.val) ((P t.2.1).vertices (t.2.2.val.val+1))
  have hK (t : Bad) : IsCompact (K t) := by
    dsimp [K]
    rw [← Path.range_segment]
    exact isCompact_range (Path.segment _ _).continuous
  have hnot (t : Bad) : D.vertex t.1 ∉ K t := by
    intro hx
    exact t.2.2.property (drawing_chain_piece_vertex D t.2.1 (P t.2.1)
      (hmin t.2.1) t.2.2.val.val t.2.2.val.isLt t.1 hx)
  obtain ⟨ρ,hρ,hclear⟩ := exists_round_disk_clearance (fun t : Bad => D.vertex t.1) K hK hnot
  obtain ⟨σ,hσ,hdis⟩ := exists_disjoint_round_disks D.vertex D.vertex_injective
  refine ⟨min ρ σ,lt_min hρ hσ,?_,?_⟩
  · intro j k hjk
    exact (hdis j k hjk).mono
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_right _ _))
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_right _ _))
  · intro j e i hi
    exact (hclear ⟨j,e,⟨i,hi⟩⟩).mono_left
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_left _ _))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_VertexSpokeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_small_squared_radius {ι : Type*} [Fintype ι] (ρ : ℝ) (hρ : 0 < ρ)
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ ∀ i, r^2 < L i := by
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ (fun i => min 1 (L i))
    (fun i _ => lt_min (by norm_num) (hL i))
  refine ⟨min ρ δ,lt_min hρ hδ,min_le_left _ _,?_⟩
  intro i
  have hh := (min_le_right ρ δ).trans_lt (hbound i (Finset.mem_univ _))
  have h1 := hh.trans_le (min_le_left 1 (L i))
  have hlen := hh.trans_le (min_le_right 1 (L i))
  have hpos := lt_min hρ hδ
  have hm := mul_pos hpos (sub_pos.mpr h1)
  nlinarith

theorem exists_vertex_spoke_bound {m n : ℕ} (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ ∀ e,
      r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)) := by
  let L : BipartiteEdge m n → ℝ := fun e =>
    min (squaredLength ((P e).vertices 1-(P e).vertices 0))
      (squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
  have hL (e : BipartiteEdge m n) : 0 < L e := by
    have hp := drawing_chain_pieces_pos D e (P e)
    have hlast := (P e).minimum_piece_ne_zero (hmin e) ((P e).pieces-1) (by omega)
    rw [show (P e).pieces-1+1=(P e).pieces by omega] at hlast
    exact lt_min (squaredLength_pos _ ((P e).minimum_piece_ne_zero (hmin e) 0 hp))
      (squaredLength_pos _ hlast)
  obtain ⟨r,hr,hrρ,hbound⟩ := exists_small_squared_radius ρ hρ L hL
  exact ⟨r,hr,hrρ,fun e => ⟨(hbound e).trans_le (min_le_left _ _),
    (hbound e).trans_le (min_le_right _ _)⟩⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ShortVertexRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_short_vertex_radius {m n : ℕ} (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ ∀ e,
      4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)) := by
  obtain ⟨s,hs,hsρ,hbound⟩ := exists_vertex_spoke_bound D P hmin ρ hρ
  refine ⟨s/2,by positivity,by linarith,?_⟩
  intro e
  obtain ⟨hfirst,hlast⟩ := hbound e
  constructor <;> nlinarith

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

theorem drawingSpokePort_injective (D : AdmissibleDrawing m n) (hnorm : NoAdjacentCrossings D)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (j : BipartiteVertex m n) : Function.Injective (drawingSpokePort D.toContinuousDrawing P r j) := by
  intro e f heq
  by_contra hne
  have hef : e.val ≠ f.val := fun h => hne (Subtype.ext h)
  have hp := drawingSpokePort_interior D.toContinuousDrawing P hmin r hr hshort j e
  have hq := drawingSpokePort_interior D.toContinuousDrawing P hmin r hr hshort j f
  rw [← heq] at hq
  have hh : drawingSpokePort D.toContinuousDrawing P r j e ∈
      edgeInterior D.toContinuousDrawing e.val ∩ edgeInterior D.toContinuousDrawing f.val := ⟨hp,hq⟩
  rw [hnorm e.val f.val hef (incident_edges_adjacent j e f)] at hh
  exact hh

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

theorem nonempty_vertexTruncation (D : ContinuousDrawing m n)
    (hpoly : ∀ e, HasFiniteAffineCover (D.edge e)) : Nonempty (VertexTruncation D) := by
  classical
  have hex (e : BipartiteEdge m n) := exists_reduced_polygonalChain (D.edge e) (D.edge_injective e) (hpoly e)
  choose P htrace hinj hpos hdir hbend hmin using hex
  obtain ⟨ρ,hρ,hdis,hclear⟩ := exists_vertex_piece_clearance D P hmin
  obtain ⟨r,hr,hrρ,hshort⟩ := exists_short_vertex_radius D P hmin ρ hρ
  refine ⟨⟨P,hmin,r,hr,hshort,?_,?_⟩⟩
  · intro j k hjk
    exact (hdis j k hjk).mono (closedRoundDisk_mono _ hr.le hrρ) (closedRoundDisk_mono _ hr.le hrρ)
  · intro j e i hi
    exact (hclear j e i hi).mono_left (closedRoundDisk_mono _ hr.le hrρ)

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
-- module Solutions.OAIB3_Zar.Crossing_SimilarityCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem similarityPoint_coordinates (o u x : Plane) (hu : u ≠ 0) :
    similarityPoint o u (similarityCoordinates o u x)=x := by
  have hL := ne_of_gt (squaredLength_pos u hu)
  change u.1^2+u.2^2 ≠ 0 at hL
  apply Prod.ext <;>
    dsimp [similarityPoint,similarityCoordinates,dot2,det2,rotateQuarter,squaredLength] <;>
    field_simp [hL] <;> ring

theorem similarityCoordinates_length (o u x : Plane) (hu : u ≠ 0) :
    squaredLength (similarityCoordinates o u x)=squaredLength (x-o)/squaredLength u := by
  have hL := ne_of_gt (squaredLength_pos u hu)
  change u.1^2+u.2^2 ≠ 0 at hL
  dsimp [similarityCoordinates,dot2,det2,squaredLength]
  field_simp [hL]
  ring

theorem similarityPoint_cut (o u : Plane) : similarityPoint o u (-1,0)=o-u := by
  apply Prod.ext <;> dsimp [similarityPoint,rotateQuarter] <;> ring

theorem circle_similarity_parameter (o u x : Plane) (hu : u ≠ 0)
    (hx : squaredLength (x-o)=squaredLength u) (hcut : x ≠ o-u) :
    ∃ t : ℝ, similarityPoint o u (circlePoint t)=x := by
  let c := similarityCoordinates o u x
  have hL := ne_of_gt (squaredLength_pos u hu)
  have hc : c.1^2+c.2^2=1 := by
    change squaredLength (similarityCoordinates o u x)=1
    rw [similarityCoordinates_length o u x hu,hx,div_self hL]
  have hcx : c.1 ≠ -1 := by
    intro hh
    have hc2 : c.2=0 := by rw [hh] at hc; nlinarith [sq_nonneg c.2]
    have he : c=(-1,0) := Prod.ext hh hc2
    apply hcut
    calc
      x = similarityPoint o u c := (similarityPoint_coordinates o u x hu).symm
      _ = o-u := by rw [he,similarityPoint_cut]
  refine ⟨c.2/(1+c.1),?_⟩
  rw [circlePoint_surjective_away_cut c hc hcx]
  exact similarityPoint_coordinates o u x hu

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FiniteCircleCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_circle_cut_vector {ι : Type*} [Fintype ι] (o : Plane)
    (r : ℝ) (hr : 0 < r) (point : ι → Plane) :
    ∃ u : Plane, u ≠ 0 ∧ squaredLength u=r^2 ∧ ∀ i, point i ≠ o-u := by
  let f : ℝ → Plane := fun t => o+r • circlePoint t
  have hf : Function.Injective f := by
    intro t s h
    have hh := congrArg (fun z : Plane => r⁻¹ • (z-o)) h
    dsimp [f] at hh
    simp only [add_sub_cancel_left,smul_smul,inv_mul_cancel₀ (ne_of_gt hr),one_smul] at hh
    exact circlePoint_injective hh
  have hbad : (f ⁻¹' Set.range point).Finite := Set.Finite.preimage hf.injOn (Set.finite_range point)
  obtain ⟨t,ht⟩ := hbad.exists_notMem
  let u := (-r) • circlePoint t
  have hlen : squaredLength u=r^2 := by
    dsimp [u]
    rw [squaredLength_smul]
    have hunit : squaredLength (circlePoint t)=1 := circlePoint_on_unit_circle t
    rw [hunit,mul_one,neg_sq]
  have hu : u ≠ 0 := by
    intro h
    rw [h] at hlen
    have hz : squaredLength (0 : Plane)=0 := by simp [squaredLength]
    rw [hz] at hlen
    nlinarith
  refine ⟨u,hu,hlen,?_⟩
  intro i he
  apply ht
  refine ⟨i,?_⟩
  simpa only [u,f,neg_smul,sub_neg_eq_add] using he

theorem exists_finite_circle_coordinates {ι : Type*} [Fintype ι]
    (o : Plane) (r : ℝ) (hr : 0 < r) (point : ι → Plane)
    (hinj : Function.Injective point) (hcircle : ∀ i, squaredLength (point i-o)=r^2) :
    ∃ u : Plane, u ≠ 0 ∧ squaredLength u=r^2 ∧
      ∃ node : ι → ℝ, Function.Injective node ∧ ∀ i, similarityPoint o u (circlePoint (node i))=point i := by
  obtain ⟨u,hu,hlen,hcut⟩ := exists_circle_cut_vector o r hr point
  have hex (i : ι) := circle_similarity_parameter o u (point i) hu ((hcircle i).trans hlen.symm) (hcut i)
  choose node hnode using hex
  refine ⟨u,hu,hlen,node,?_,hnode⟩
  intro i j hij
  apply hinj
  rw [← hnode i,← hnode j,hij]

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

theorem spokePort_circle (j : BipartiteVertex m n) (e : IncidentEdges j) :
    squaredLength (V.spokePort j e-D.vertex j)=V.radius^2 :=
  drawingSpokePort_circle D V.chain V.minimal V.radius j e

theorem spokePort_injective {A : AdmissibleDrawing m n}
    (V : VertexTruncation A.toContinuousDrawing) (hnorm : NoAdjacentCrossings A)
    (j : BipartiteVertex m n) : Function.Injective (V.spokePort j) :=
  drawingSpokePort_injective A hnorm V.chain V.minimal V.radius V.radius_pos V.weak_short j

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

theorem nonempty_truncatedSpokeCoordinates {A : AdmissibleDrawing m n}
    (V : VertexTruncation A.toContinuousDrawing) (hnorm : NoAdjacentCrossings A) :
    Nonempty (TruncatedSpokeCoordinates V) := by
  have hex (j : BipartiteVertex m n) := exists_finite_circle_coordinates
    (A.vertex j) V.radius V.radius_pos (V.spokePort j)
    (V.spokePort_injective hnorm j) (V.spokePort_circle j)
  choose u hu hlen node hnode hpoint using hex
  exact ⟨⟨u,hu,hlen,node,hnode,hpoint⟩⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OddCrossingLowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem odd_crossing_lower_bound (m s : ℕ) (D : AdmissibleDrawing m (2*s+1)) :
    axisPairs m*axisPairs (2*s+1) ≤ crossingCount D := by
  by_cases hm : 0 < m
  · by_cases hs : 0 < s
    · obtain ⟨A,hcount,hpoly,hnorm,hstraight,htrans⟩ := polygonal_no_adjacent_locally_transverse D
      obtain ⟨V⟩ := nonempty_vertexTruncation A.toContinuousDrawing hpoly
      obtain ⟨C⟩ := nonempty_truncatedSpokeCoordinates V hnorm
      rw [axisPairs_odd]
      exact (C.odd_normalized_crossing_lower_bound hnorm hstraight htrans s hs rfl hm).trans hcount
    · have he : s=0 := Nat.eq_zero_of_not_pos hs
      subst s
      simp [axisPairs]
  · have he : m=0 := Nat.eq_zero_of_not_pos hm
    subst m
    simp [axisPairs]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_EvenCrossingLowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem even_successor_crossing_lower_bound (m s : ℕ) (D : AdmissibleDrawing m ((2*s+1)+1)) :
    axisPairs m*axisPairs ((2*s+1)+1) ≤ crossingCount D := by
  by_cases hs : 0 < s
  · obtain ⟨A,hcount,hpoly,hnorm,hstraight,htrans⟩ := polygonal_no_adjacent_locally_transverse D
    have hsum : (∑ v : Fin ((2*s+1)+1), axisPairs m*axisPairs (2*s+1)) ≤
        ∑ v : Fin ((2*s+1)+1), crossingCount (deleteRightVertex A v) := by
      apply Finset.sum_le_sum
      intro v hv
      exact odd_crossing_lower_bound m s (deleteRightVertex A v)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
    rw [sum_delete_crossingCount A hnorm] at hsum
    have hN : (2*s+1)+1=2*(s+1) := by omega
    have hprev : 2*s+1=2*(s+1)-1 := by omega
    have hfloor : ((2*s+1)+1)*axisPairs (2*s+1)=
        (((2*s+1)+1)-2)*axisPairs ((2*s+1)+1) := by
      rw [hN,hprev]
      exact even_deletion_floor (s+1)
    have hmul : (((2*s+1)+1)-2)*(axisPairs m*axisPairs ((2*s+1)+1)) ≤
        (((2*s+1)+1)-2)*crossingCount A := by
      calc
        _ = axisPairs m*((((2*s+1)+1)-2)*axisPairs ((2*s+1)+1)) := by ring
        _ = axisPairs m*(((2*s+1)+1)*axisPairs (2*s+1)) := by rw [← hfloor]
        _ = ((2*s+1)+1)*(axisPairs m*axisPairs (2*s+1)) := by ring
        _ ≤ _ := hsum
    exact (Nat.le_of_mul_le_mul_left hmul (by omega)).trans hcount
  · have he : s=0 := Nat.eq_zero_of_not_pos hs
    subst s
    simp [axisPairs]

theorem crossing_lower_bound (m n : ℕ) (D : AdmissibleDrawing m n) :
    axisPairs m*axisPairs n ≤ crossingCount D := by
  rcases Nat.even_or_odd n with h | h
  · obtain ⟨s,hs⟩ := h
    cases s with
    | zero =>
      have hn : n=0 := by omega
      cases hn
      simp [axisPairs]
    | succ s =>
      have he : n=(2*s+1)+1 := by omega
      cases he
      exact even_successor_crossing_lower_bound m s D
  · obtain ⟨s,hs⟩ := h
    have hn : n=2*s+1 := by omega
    cases hn
    exact odd_crossing_lower_bound m s D

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_BalancedAxisCrossingCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.BalancedAxisRealization
open scoped BigOperators Finset
variable {m n : ℕ} (R : BalancedAxisRealization m n)

theorem pairCrossings_card_le_one (e f : BipartiteEdge m n) : (pairCrossings R.drawing e f).card ≤ 1 := by
  classical
  by_cases hef : e=f
  · subst f
    simp [pairCrossings_self]
  · apply Finset.card_le_one.mpr
    intro x hx y hy
    have hsub := axisContinuousDrawing_pair_subsingleton R.vertical R.horizontal R.vertical_injective
      R.horizontal_injective R.vertical_ne_zero R.horizontal_ne_zero e f hef
    exact hsub (Finset.mem_filter.mp hx).2.2 (Finset.mem_filter.mp hy).2.2

theorem crossings_covered_by_candidates :
    R.drawing.crossings_finite.toFinset ⊆ R.crossingCandidates.biUnion R.candidateCrossings := by
  classical
  intro x hx
  have hcross : x ∈ crossingPoints R.drawing.toContinuousDrawing := by simpa using hx
  obtain ⟨e,f,hef,he,hf⟩ := hcross
  have hind := axisContinuousDrawing_meeting_independent R.vertical R.horizontal R.vertical_injective
    R.horizontal_injective R.vertical_ne_zero R.horizontal_ne_zero e f hef x he hf
  rcases lt_or_gt_of_ne hind.1 with hlt | hgt
  · have hc := R.meeting_balanced_pairs e.1 f.1 e.2 f.2 hlt x he hf
    apply Finset.mem_biUnion.mpr
    refine ⟨((e.1,f.1),(f.2,e.2)),Finset.mem_product.mpr hc,?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨hx,hef,he,hf⟩
  · have hc := R.meeting_balanced_pairs f.1 e.1 f.2 e.2 hgt x hf he
    apply Finset.mem_biUnion.mpr
    refine ⟨((f.1,e.1),(e.2,f.2)),Finset.mem_product.mpr hc,?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨hx,Ne.symm hef,hf,he⟩

theorem crossingCount_le : crossingCount R.drawing ≤ axisPairs m*axisPairs n := by
  classical
  calc
    crossingCount R.drawing ≤ (R.crossingCandidates.biUnion R.candidateCrossings).card :=
      Finset.card_le_card R.crossings_covered_by_candidates
    _ ≤ ∑ v ∈ R.crossingCandidates, (R.candidateCrossings v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ R.crossingCandidates, 1 := by
      apply Finset.sum_le_sum
      intro v hv
      exact R.pairCrossings_card_le_one _ _
    _ = R.crossingCandidates.card := by simp
    _ = axisPairs m*axisPairs n := by
      rw [crossingCandidates,Finset.card_product,balancedRayPairs_card,balancedRayPairs_card]

theorem crossingCount_eq : crossingCount R.drawing=axisPairs m*axisPairs n :=
  Nat.le_antisymm R.crossingCount_le (crossing_lower_bound m n R.drawing)

end Zarankiewicz.BalancedAxisRealization

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem mainTarget_proof_oai : MainTarget := by
  intro m n hm hn
  obtain ⟨R⟩ := nonempty_balancedAxisRealization m n
  exact ⟨⟨R.drawing,R.crossingCount_eq⟩,crossing_lower_bound m n⟩

end Zarankiewicz

end

end OAI
end

theorem solution : type_of% @OAI.Zarankiewicz.mainTarget_proof_oai := @OAI.Zarankiewicz.mainTarget_proof_oai
