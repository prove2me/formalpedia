-- Prove2me | solution 1 for OAI.Zarankiewicz.nonempty_polygonalExterior
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T13:21:39.025824+00:00
-- url     : https://prove2.me/submissions/465df081-132a-4167-a770-a318a1f835ba

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr002

section
-- module Solutions.OAIB3_Zar.Crossing_RadialExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem squaredLength_segment_translated (a b z : Plane) (t : ℝ) :
    squaredLength (segmentPoint a b t-z)=
      squaredLength (a-z)+2*t*dot2 (a-z) (b-a)+t^2*squaredLength (b-a) := by
  dsimp [squaredLength,dot2,segmentPoint]
  ring

theorem exterior_segment_of_dot (z a b : Plane) (r : ℝ)
    (ha : r^2 < squaredLength (a-z)) (hd : 0 ≤ dot2 (a-z) (b-a)) :
    segment ℝ a b ⊆ {x | r^2 < squaredLength (x-z)} := by
  intro x hx
  rw [← Path.range_segment] at hx
  obtain ⟨t,rfl⟩ := hx
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  change r^2 < squaredLength (segmentPoint a b t.val-z)
  rw [squaredLength_segment_translated]
  have h₁ : 0 ≤ 2*t.val*dot2 (a-z) (b-a) := mul_nonneg (mul_nonneg (by norm_num) t.property.1) hd
  have h₂ : 0 ≤ t.val^2*squaredLength (b-a) := by dsimp [squaredLength]; positivity
  linarith

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

theorem radial_tip_dot (z x : Plane) (α : ℝ) :
    dot2 (x-z) ((x+α • (x-z))-x)=α*squaredLength (x-z) := by
  dsimp [dot2,squaredLength]
  ring

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_BoundaryCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem exists_radial_tip_collar (z x : Plane) (r : ℝ) (hr : 0 < r)
    (hx : squaredLength (x-z)=r^2) (U : Set Plane) (hU : IsOpen U) (hxu : x ∈ U) :
    ∃ α ρ : ℝ, 0 < α ∧ 0 < ρ ∧
      segment ℝ x (x+α • (x-z)) ⊆ U ∩ insert x {y | r^2 < squaredLength (y-z)} ∧
      (∀ y, dist y x < ρ → r^2 < squaredLength (y-z) →
        segment ℝ (x+α • (x-z)) y ⊆ U ∩ {p | r^2 < squaredLength (p-z)}) := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU x hxu
  have hmove : Continuous (fun α : ℝ => x+α • (x-z)) := by fun_prop
  have hevent : ∀ᶠ α : ℝ in 𝓝 0, x+α • (x-z) ∈ Metric.ball x ε :=
    hmove.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds x hε)
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp hevent
  let α := δ/2
  have hα : 0 < α := by dsimp [α]; positivity
  have htip : x+α • (x-z) ∈ Metric.ball x ε := hd (by
    rw [Real.dist_eq,sub_zero,abs_of_pos hα]
    dsimp [α]
    linarith)
  have hdpos : 0 < dot2 (x-z) ((x+α • (x-z))-x) := by
    rw [radial_tip_dot,hx]
    exact mul_pos hα (sq_pos_of_pos hr)
  have hdot : Continuous (fun y : Plane => dot2 (y-z) ((x+α • (x-z))-y)) := by
    unfold dot2
    fun_prop
  have hev : ∀ᶠ y : Plane in 𝓝 x, 0 < dot2 (y-z) ((x+α • (x-z))-y) :=
    continuousAt_const.eventually_lt hdot.continuousAt hdpos
  obtain ⟨σ,hσ,hσdot⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨α,min ε σ,hα,lt_min hε hσ,?_,?_⟩
  · apply Set.subset_inter
    · exact ((convex_ball x ε).segment_subset (Metric.mem_ball_self hε) htip).trans hball
    · exact radial_spur_exterior z x r α hx hr hα
  · intro y hy hout
    apply Set.subset_inter
    · exact ((convex_ball x ε).segment_subset htip (hy.trans_le (min_le_left _ _))).trans hball
    · rw [segment_symm]
      exact exterior_segment_of_dot z y (x+α • (x-z)) r hout
        (hσdot (hy.trans_le (min_le_right _ _))).le

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
-- module Solutions.OAIB3_Zar.Crossing_CompactCorridors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem finite_compact_corridors {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K O : ι → Set Plane) (hK : ∀ i, IsCompact (K i))
    (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (hO : ∀ i, IsOpen (O i)) (hKO : ∀ i, K i ⊆ O i) :
    ∃ U : ι → Set Plane, (∀ i, IsOpen (U i)) ∧ (∀ i, K i ⊆ U i) ∧
      (∀ i, U i ⊆ O i) ∧ (∀ i j, i ≠ j → Disjoint (U i) (U j)) := by
  have hex (i j : ι) : ∃ A B : Set Plane, IsOpen A ∧ IsOpen B ∧ K i ⊆ A ∧ K j ⊆ B ∧
      (i ≠ j → Disjoint A B) := by
    by_cases he : i=j
    · exact ⟨Set.univ,Set.univ,isOpen_univ,isOpen_univ,Set.subset_univ _,Set.subset_univ _,fun hn => False.elim (hn he)⟩
    · obtain ⟨A,B,hA,hB,hi,hj,hab⟩ := normal_separation (hK i).isClosed (hK j).isClosed (hd i j he)
      exact ⟨A,B,hA,hB,hi,hj,fun _ => hab⟩
  choose A B hA hB hKA hKB hAB using hex
  let U : ι → Set Plane := fun i => O i ∩ ⋂ j, A i j ∩ B j i
  refine ⟨U,?_,?_,?_,?_⟩
  · intro i
    exact (hO i).inter (isOpen_iInter_of_finite (fun j => (hA i j).inter (hB j i)))
  · intro i x hx
    exact ⟨hKO i hx,Set.mem_iInter.mpr (fun j => ⟨hKA i j hx,hKB j i hx⟩)⟩
  · intro i x hx
    exact hx.1
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (hAB i j hij)
      (Set.mem_iInter.mp hx.2 j).1 (Set.mem_iInter.mp hy.2 i).2

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingMarks
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem drawingMarks_finite (D : FiniteIntersectionDrawing m n) : (drawingMarks D).Finite :=
  (Set.finite_range D.vertex).union D.crossings_finite

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FiniteDiskCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem isOpen_disk_exterior (z : Plane) (r : ℝ) :
    IsOpen {x | r^2 < squaredLength (x-z)} := by
  apply isOpen_lt continuous_const
  unfold squaredLength
  fun_prop

theorem isOpen_outsideDisks {ι : Type*} [Finite ι] (z : ι → Plane) (r : ℝ) :
    IsOpen (outsideDisks z r) := by
  have he : outsideDisks z r=⋂ i, {x | r^2 < squaredLength (x-z i)} := by
    ext x
    simp [outsideDisks]
  rw [he]
  exact isOpen_iInter_of_finite (fun i => isOpen_disk_exterior (z i) r)

theorem exists_finite_disk_collar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → Plane) (r : ℝ) (hr : 0 < r)
    (hd : ∀ i j, i ≠ j → Disjoint (closedRoundDisk (z i) r) (closedRoundDisk (z j) r))
    (k : ι) (x : Plane) (hx : squaredLength (x-z k)=r^2)
    (U : Set Plane) (hU : IsOpen U) (hxu : x ∈ U) :
    ∃ α ρ : ℝ, 0 < α ∧ 0 < ρ ∧
      segment ℝ x (x+α • (x-z k)) ⊆ U ∩ insert x (outsideDisks z r) ∧
      (∀ y, dist y x < ρ → y ∈ outsideDisks z r →
        segment ℝ (x+α • (x-z k)) y ⊆ U ∩ outsideDisks z r) := by
  let V : Set Plane := U ∩ ⋂ j : {j : ι // j ≠ k}, {y | r^2 < squaredLength (y-z j.val)}
  have hV : IsOpen V := hU.inter (isOpen_iInter_of_finite (fun j => isOpen_disk_exterior (z j.val) r))
  have hxV : x ∈ V := by
    refine ⟨hxu,Set.mem_iInter.mpr (fun j => ?_)⟩
    change r^2 < squaredLength (x-z j.val)
    apply lt_of_not_ge
    intro hh
    exact Set.disjoint_left.mp (hd k j.val (Ne.symm j.property)) (show x ∈ closedRoundDisk (z k) r from hx.le) hh
  obtain ⟨α,ρ,hα,hρ,hspur,hnear⟩ := exists_radial_tip_collar (z k) x r hr hx V hV hxV
  have hout : V ∩ {p | r^2 < squaredLength (p-z k)} ⊆ U ∩ outsideDisks z r := by
    intro p hp
    refine ⟨hp.1.1,fun j => ?_⟩
    by_cases he : j=k
    · simpa [he] using hp.2
    · exact Set.mem_iInter.mp hp.1.2 ⟨j,he⟩
  refine ⟨α,ρ,hα,hρ,?_,?_⟩
  · intro p hp
    obtain ⟨hpV,hpx | hpout⟩ := hspur hp
    · exact ⟨hpV.1,Or.inl hpx⟩
    · exact ⟨hpV.1,Or.inr (hout ⟨hpV,hpout⟩).2⟩
  · intro y hy hyout
    exact (hnear y hy (hyout k)).trans hout

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PathEndpointNeighborhoods
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem path_near_endpoints {a b : Plane} (γ : Path a b) (ρ σ : ℝ)
    (hρ : 0 < ρ) (hσ : 0 < σ) :
    ∃ u v : unitInterval, 0 < u ∧ u < v ∧ v < 1 ∧
      dist (γ u) a < ρ ∧ dist (γ v) b < σ := by
  have he0 : ∀ᶠ t : ℝ in 𝓝 0, γ.extend t ∈ Metric.ball a ρ :=
    γ.continuous_extend.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds a hρ)
  have he1 : ∀ᶠ t : ℝ in 𝓝 1, γ.extend t ∈ Metric.ball b σ :=
    γ.continuous_extend.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds b hσ)
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp he0
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp he1
  let p := min (δ/2) (1/4)
  let q := min (ε/2) (1/4)
  have hp : 0 < p := lt_min (by positivity) (by norm_num)
  have hq : 0 < q := lt_min (by positivity) (by norm_num)
  have hp4 : p ≤ 1/4 := min_le_right _ _
  have hq4 : q ≤ 1/4 := min_le_right _ _
  have hpd : p < δ := (min_le_left _ _).trans_lt (by linarith)
  have hqe : q < ε := (min_le_left _ _).trans_lt (by linarith)
  let u : unitInterval := ⟨p,hp.le,by linarith⟩
  let v : unitInterval := ⟨1-q,by linarith,by linarith⟩
  have hu : γ.extend p ∈ Metric.ball a ρ := hd (by simpa [Real.dist_eq,abs_of_pos hp] using hpd)
  have hv : γ.extend (1-q) ∈ Metric.ball b σ := he (by
    simpa [Real.dist_eq,abs_of_pos hq] using hqe)
  rw [show γ.extend p=γ u from γ.extend_extends' u] at hu
  rw [show γ.extend (1-q)=γ v from γ.extend_extends' v] at hv
  exact ⟨u,v,hp,(by change p < 1-q; linarith),(by change 1-q < 1; linarith),hu,hv⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalReach
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem segmentReach_mem {O : Set Plane} {a b : Plane} (ha : a ∈ O) (h : SegmentReach O a b) : b ∈ O := by
  induction h with
  | refl => exact ha
  | @tail b c hab hbc ih => exact hbc (right_mem_segment ℝ b c)

theorem isOpen_segmentReach (O : Set Plane) (hO : IsOpen O) (a : Plane) (ha : a ∈ O) :
    IsOpen {b | SegmentReach O a b} := by
  apply Metric.isOpen_iff.mpr
  intro b hb
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds (segmentReach_mem ha hb))
  refine ⟨ε,hε,?_⟩
  intro c hc
  apply Relation.ReflTransGen.tail hb
  exact ((convex_ball b ε).segment_subset (Metric.mem_ball_self hε) hc).trans hball

theorem isOpen_non_segmentReach (O : Set Plane) (hO : IsOpen O) (a : Plane) :
    IsOpen (O \ {b | SegmentReach O a b}) := by
  apply Metric.isOpen_iff.mpr
  intro b hb
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hb.1)
  refine ⟨ε,hε,?_⟩
  intro c hc
  refine ⟨hball hc,?_⟩
  intro hreach
  apply hb.2
  apply Relation.ReflTransGen.tail hreach
  exact ((convex_ball b ε).segment_subset hc (Metric.mem_ball_self hε)).trans hball

theorem segmentReach_of_path {a b : Plane} (γ : Path a b) (O : Set Plane)
    (hO : IsOpen O) (hγ : ∀ t, γ t ∈ O) : SegmentReach O a b := by
  have ha : a ∈ O := by simpa using hγ 0
  let A : Set unitInterval := {t | SegmentReach O a (γ t)}
  have hopen : IsOpen A := (isOpen_segmentReach O hO a ha).preimage γ.continuous
  have hcomp : IsOpen Aᶜ := by
    have heq : Aᶜ = γ ⁻¹' (O \ {x | SegmentReach O a x}) := by
      ext t
      simp only [A,Set.mem_compl_iff,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_sdiff,hγ t,true_and]
    rw [heq]
    exact (isOpen_non_segmentReach O hO a).preimage γ.continuous
  have hall : A=Set.univ := (show IsClopen A from ⟨by simpa using hcomp.isClosed_compl,hopen⟩).eq_univ ⟨0,by
    change SegmentReach O a (γ 0)
    rw [γ.source]
    exact Relation.ReflTransGen.refl⟩
  have hb : (1 : unitInterval) ∈ A := by rw [hall]; trivial
  change SegmentReach O a (γ 1) at hb
  rwa [γ.target] at hb

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem nonempty_polygonalChain_of_reach {O : Set Plane} {a b : Plane}
    (ha : a ∈ O) (h : SegmentReach O a b) : Nonempty (PolygonalChain O a b) := by
  induction h with
  | refl => exact ⟨PolygonalChain.point O a ha⟩
  | @tail b c hab hbc ih =>
    obtain ⟨P⟩ := ih
    exact ⟨P.append c hbc⟩

theorem nonempty_polygonalChain_of_path {a b : Plane} (γ : Path a b) (O : Set Plane)
    (hO : IsOpen O) (hγ : ∀ t, γ t ∈ O) : Nonempty (PolygonalChain O a b) := by
  exact nonempty_polygonalChain_of_reach (by simpa using hγ 0) (segmentReach_of_path γ O hO hγ)

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
-- module Solutions.OAIB3_Zar.Crossing_SimultaneousPolygonalReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_simple_polygonalChain {O : Set Plane} {a b : Plane} (hab : a ≠ b)
    (h : Nonempty (PolygonalChain O a b)) :
    ∃ P : PolygonalChain O a b, Function.Injective P.path ∧ Set.range P.path ⊆ O := by
  obtain ⟨P,hmin⟩ := exists_minimum_polygonalChain h
  exact ⟨P,P.minimum_path_injective hab hmin,P.path_range_subset⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalBoundaryReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem simple_path_interior_of_range_insert {a b : Plane} (γ : Path a b)
    (hinj : Function.Injective γ) (O : Set Plane)
    (hrange : Set.range γ ⊆ insert a (insert b O))
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) : γ t ∈ O := by
  rcases hrange ⟨t,rfl⟩ with ha | hb | ho
  · have he := hinj (ha.trans γ.source.symm)
    exact False.elim (ht.1.ne he.symm)
  · have he := hinj (hb.trans γ.target.symm)
    exact False.elim (ht.2.ne he)
  · exact ho

theorem polygonal_replacement_with_spurs (O : Set Plane) (hO : IsOpen O)
    (a a' b' b : Plane) (hab : a ≠ b) (γ : Path a' b')
    (hγ : ∀ t, γ t ∈ O)
    (ha : segment ℝ a a' ⊆ insert a (insert b O))
    (hb : segment ℝ b' b ⊆ insert a (insert b O)) :
    ∃ P : PolygonalChain (insert a (insert b O)) a b,
      Function.Injective P.path ∧
      (∀ t : unitInterval, t ∈ Set.Ioo (0 : unitInterval) 1 → P.path t ∈ O) := by
  obtain ⟨Q⟩ := nonempty_polygonalChain_of_path γ O hO hγ
  let S := insert a (insert b O)
  let Q' : PolygonalChain S a' b' := Q.widen (fun _ hx => Or.inr (Or.inr hx))
  let L : PolygonalChain S a a' := PolygonalChain.single S a a' (Or.inl rfl) ha
  let R : PolygonalChain S b' b := PolygonalChain.single S b' b
    (Or.inr (Or.inr (by simpa using hγ 1))) hb
  obtain ⟨P,hP,hR⟩ := exists_simple_polygonalChain hab ⟨(L.join Q').join R⟩
  exact ⟨P,hP,fun t ht => simple_path_interior_of_range_insert P.path hP O hR t ht⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ExteriorArcReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exterior_arc_polygonal_replacement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → Plane) (r : ℝ) (hr : 0 < r)
    (hd : ∀ i j, i ≠ j → Disjoint (closedRoundDisk (z i) r) (closedRoundDisk (z j) r))
    (k l : ι) (a b : Plane) (hab : a ≠ b)
    (ha : squaredLength (a-z k)=r^2) (hb : squaredLength (b-z l)=r^2)
    (γ : Path a b) (U : Set Plane) (hU : IsOpen U) (hγU : ∀ t, γ t ∈ U)
    (hγout : ∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → γ t ∈ outsideDisks z r) :
    ∃ P : PolygonalChain U a b, Function.Injective P.path ∧
      (∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → P.path t ∈ outsideDisks z r) := by
  obtain ⟨α,ρ,hα,hρ,hspurA,hnearA⟩ := exists_finite_disk_collar z r hr hd k a ha U hU
    (by simpa using hγU 0)
  obtain ⟨β,σ,hβ,hσ,hspurB,hnearB⟩ := exists_finite_disk_collar z r hr hd l b hb U hU
    (by simpa using hγU 1)
  obtain ⟨u,v,hu0,huv,hv1,hu,hv⟩ := path_near_endpoints γ ρ σ hρ hσ
  let a' := a+α • (a-z k)
  let b' := b+β • (b-z l)
  let O := U ∩ outsideDisks z r
  have hO : IsOpen O := hU.inter (isOpen_outsideDisks z r)
  have hleft : segment ℝ a' (γ u) ⊆ O := hnearA (γ u) hu (hγout u ⟨hu0,huv.trans hv1⟩)
  have hright : segment ℝ (γ v) b' ⊆ O := by
    rw [segment_symm]
    exact hnearB (γ v) hv (hγout v ⟨hu0.trans huv,hv1⟩)
  have hmiddle : Set.range (pathSubarc γ u v) ⊆ O := by
    rw [pathSubarc_range γ u v huv]
    rintro x ⟨t,ht,rfl⟩
    exact ⟨hγU t,hγout t ⟨hu0.trans_le ht.1,ht.2.trans_lt hv1⟩⟩
  let η : Path a' b' := (Path.segment a' (γ u)).trans
    ((pathSubarc γ u v).trans (Path.segment (γ v) b'))
  have hη : Set.range η ⊆ O := by
    dsimp [η]
    rw [Path.trans_range,Path.trans_range,Path.range_segment,Path.range_segment]
    exact Set.union_subset hleft (Set.union_subset hmiddle hright)
  have hA : segment ℝ a a' ⊆ insert a (insert b O) := by
    intro x hx
    obtain ⟨hxU,hxa | hxout⟩ := hspurA hx
    · exact Or.inl hxa
    · exact Or.inr (Or.inr ⟨hxU,hxout⟩)
  have hB : segment ℝ b' b ⊆ insert a (insert b O) := by
    rw [segment_symm]
    intro x hx
    obtain ⟨hxU,hxb | hxout⟩ := hspurB hx
    · exact Or.inr (Or.inl hxb)
    · exact Or.inr (Or.inr ⟨hxU,hxout⟩)
  obtain ⟨Q,hQ,hQout⟩ := polygonal_replacement_with_spurs O hO a a' b' b hab η
    (fun t => hη ⟨t,rfl⟩) hA hB
  have hSU : insert a (insert b O) ⊆ U := by
    intro x hx
    rcases hx with rfl | rfl | hx
    · simpa using hγU 0
    · simpa using hγU 1
    · exact hx.1
  exact ⟨Q.widen hSU,hQ,fun t ht => (hQout t ht).2⟩

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
-- module Solutions.OAIB3_Zar.Crossing_OrderedPassages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem ordered_passage_leave_strictMono {a b : Plane} (γ : Path a b) {k : ℕ}
    (τ : Fin (k+1) → unitInterval) (r : ℝ) (P : ∀ i, DiskPassage γ (γ (τ i)) r (τ i))
    (hsep : ∀ i j, i < j → (P i).leave < (P j).enter) :
    StrictMono (fun i => (P i).leave) := by
  intro i j hij
  exact (hsep i j hij).trans (P j).enter_lt_leave

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RetainedDrawingArcs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem retained_parameter_outside (C : DrawingPassages D) (i : C.ArcIndex) (t : unitInterval)
    (ht : t ∈ Set.Ioo (C.passage i.1 i.2.castSucc).leave (C.passage i.1 i.2.succ).enter) :
    D.edge i.1 t ∈ outsideDisks (fun x : DrawingMark D => x.val) C.radius := by
  intro x
  apply lt_of_not_ge
  intro hh
  obtain ⟨u,hu⟩ := C.visited_mark_on_edge i.1 x t hh
  have hmu : u ∈ Set.range (C.node i.1) := by
    rw [C.node_range]
    change D.edge i.1 u ∈ drawingMarks D
    rw [hu]
    exact x.property
  obtain ⟨j,hj⟩ := hmu
  have hc : D.edge i.1 (C.node i.1 j)=x.val := (congrArg (D.edge i.1) hj).trans hu
  have hv := (C.passage i.1 j).all_visits t (by rw [hc]; exact hh)
  by_cases hji : j ≤ i.2.castSucc
  · have hm := (ordered_passage_leave_strictMono (D.edge i.1) (C.node i.1) C.radius
      (C.passage i.1) (C.separated i.1)).monotone hji
    exact ht.1.not_ge (hv.2.trans hm)
  · have hij : i.2.succ ≤ j := by
      change i.2.val+1 ≤ j.val
      have hn : ¬ j.val ≤ i.2.val := hji
      omega
    have hm := (ordered_passage_enter_strictMono (D.edge i.1) (C.node i.1) C.radius
      (C.passage i.1) (C.separated i.1)).monotone hij
    exact ht.2.not_ge (hm.trans hv.1)

theorem arc_interior_outside (C : DrawingPassages D) (i : C.ArcIndex) (t : unitInterval)
    (ht : t ∈ Set.Ioo (0 : unitInterval) 1) :
    C.arc i t ∈ outsideDisks (fun x : DrawingMark D => x.val) C.radius := by
  exact C.retained_parameter_outside i _ (intervalSegment_strict_between _ _ t (C.arc_gap i) ht)

end Zarankiewicz.DrawingPassages

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SimultaneousExteriorArcs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem finite_exterior_arc_replacements {E M : Type*}
    [Fintype E] [DecidableEq E] [Fintype M] [DecidableEq M]
    (z : M → Plane) (r : ℝ) (hr : 0 < r)
    (hd : ∀ i j, i ≠ j → Disjoint (closedRoundDisk (z i) r) (closedRoundDisk (z j) r))
    (k l : E → M) (a b : E → Plane) (hab : ∀ e, a e ≠ b e)
    (ha : ∀ e, squaredLength (a e-z (k e))=r^2)
    (hb : ∀ e, squaredLength (b e-z (l e))=r^2)
    (γ : ∀ e, Path (a e) (b e))
    (hdisjoint : ∀ e f, e ≠ f → Disjoint (Set.range (γ e)) (Set.range (γ f)))
    (hγ : ∀ e t, t ∈ Set.Ioo (0 : unitInterval) 1 → γ e t ∈ outsideDisks z r) :
    ∃ U : E → Set Plane, ∃ P : ∀ e, PolygonalChain (U e) (a e) (b e),
      (∀ e, IsOpen (U e)) ∧ (∀ e, Function.Injective (P e).path) ∧
      (∀ e t, t ∈ Set.Ioo (0 : unitInterval) 1 → (P e).path t ∈ outsideDisks z r) ∧
      (∀ e f, e ≠ f → Disjoint (Set.range (P e).path) (Set.range (P f).path)) := by
  obtain ⟨U,hU,hKU,_,hUU⟩ := finite_compact_corridors (fun e => Set.range (γ e))
    (fun _ => Set.univ) (fun e => isCompact_range (γ e).continuous) hdisjoint
    (fun _ => isOpen_univ) (fun _ => Set.subset_univ _)
  have hex (e : E) : ∃ P : PolygonalChain (U e) (a e) (b e), Function.Injective P.path ∧
      (∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → P.path t ∈ outsideDisks z r) :=
    exterior_arc_polygonal_replacement z r hr hd (k e) (l e) (a e) (b e) (hab e)
      (ha e) (hb e) (γ e) (U e) (hU e) (fun t => hKU e ⟨t,rfl⟩) (hγ e)
  choose P hP hR using hex
  exact ⟨U,P,hU,hP,hR,fun e f hef =>
    (hUU e f hef).mono (P e).path_range_subset (P f).path_range_subset⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem nonempty_polygonalExterior_oai (C : DrawingPassages D) : Nonempty (PolygonalExterior C) := by
  classical
  let : Fintype (DrawingMark D) := (drawingMarks_finite D).fintype
  obtain ⟨U,P,hU,hP,hout,hdisjoint⟩ := finite_exterior_arc_replacements
    (fun x : DrawingMark D => x.val) C.radius C.radius_pos C.disks_disjoint
    C.arcStartMark C.arcEndMark C.arcStart C.arcEnd C.arc_endpoints_ne
    C.arc_start_on_circle C.arc_end_on_circle C.arc C.arcs_pairwise_disjoint C.arc_interior_outside
  exact ⟨{
    chain := fun i => (P i).widen (Set.subset_univ _)
    injective := hP
    outside := hout
    disjoint := hdisjoint }⟩

end Zarankiewicz

end

end OAI
end

theorem solution : type_of% @OAI.Zarankiewicz.nonempty_polygonalExterior_oai := @OAI.Zarankiewicz.nonempty_polygonalExterior_oai
