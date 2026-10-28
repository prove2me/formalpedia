-- Prove2me | solution 1 for OAI.Zarankiewicz.TruncatedSpokeCoordinates.odd_normalized_crossing_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T13:23:52.382307+00:00
-- url     : https://prove2.me/submissions/190c45ae-0b4a-46bf-815b-90ed35a63774

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr003
import Definitions.Def_OAIB3Zr004
import Theorems.Thm_OAI_Zarankiewicz_TruncatedSpokeCoordinates_additive_detector_relation
import Theorems.Thm_OAI_Zarankiewicz_TruncatedSpokeCoordinates_diagonal_detector_isUnit

section
-- module Solutions.OAIB3_Zar.Crossing_AdaptedFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module Submodule
open scoped BigOperators
variable {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

theorem exists_adapted_family (E : ℕ → Submodule ℝ W) (hE : Monotone E) (hzero : E 0 = ⊥)
    (h : ℕ) :
    ∃ (v : Fin (finrank ℝ (E h)) → W) (d : Fin (finrank ℝ (E h)) → ℕ),
      LinearIndependent ℝ v ∧ span ℝ (Set.range v) = E h ∧
      (∀ i, d i < h ∧ v i ∈ E (d i+1)) ∧
      (∑ i, d i) = ∑ e ∈ Finset.range h, e * (finrank ℝ (E (e+1)) - finrank ℝ (E e)) := by
  classical
  induction h with
  | zero =>
    have hd : finrank ℝ (E 0) = 0 := by simp [hzero]
    rw [hd]
    refine ⟨Fin.elim0, Fin.elim0, linearIndependent_empty_type, ?_, ?_, ?_⟩
    · simp [hzero]
    · intro i
      exact Fin.elim0 i
    · simp
  | succ h ih =>
    obtain ⟨v, d, hli, hspan, hmem, hsum⟩ := ih
    obtain ⟨C, hdisj, hsup⟩ := IsModularLattice.exists_disjoint_and_sup_eq (hE (Nat.le_succ h))
    have hCle : C ≤ E (h+1) := by rw [← hsup]; exact le_sup_right
    have hdim : finrank ℝ (E h) + finrank ℝ C = finrank ℝ (E (h+1)) := by
      have hh := Submodule.finrank_sup_add_finrank_inf_eq (E h) C
      rw [hsup, hdisj.eq_bot, finrank_bot, add_zero] at hh
      exact hh.symm
    have hCdim : finrank ℝ C = finrank ℝ (E (h+1)) - finrank ℝ (E h) := by omega
    let b := finBasis ℝ C
    let w : Fin (finrank ℝ C) → W := fun i => C.subtype (b i)
    have hwli : LinearIndependent ℝ w := b.linearIndependent.map' C.subtype (Submodule.ker_subtype C)
    have hwspan : span ℝ (Set.range w) = C := by
      change span ℝ (Set.range (C.subtype ∘ b)) = C
      rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
    let v' := Sum.elim v w
    let d' := Sum.elim d (fun _ : Fin (finrank ℝ C) => h)
    have hv' : LinearIndependent ℝ v' :=
      hli.sum_type hwli (by rwa [hspan, hwspan])
    let e : Fin (finrank ℝ (E (h+1))) ≃
        (Fin (finrank ℝ (E h)) ⊕ Fin (finrank ℝ C)) :=
      Fintype.equivOfCardEq (by simp [hdim])
    refine ⟨v' ∘ e, d' ∘ e, hv'.comp e e.injective, ?_, ?_, ?_⟩
    · rw [Set.range_comp, e.surjective.range_eq, Set.image_univ]
      change span ℝ (Set.range (Sum.elim v w)) = E (h+1)
      rw [Set.Sum.elim_range, span_union, hspan, hwspan, hsup]
    · intro i
      change d' (e i) < h+1 ∧ v' (e i) ∈ E (d' (e i)+1)
      cases he : e i with
      | inl j =>
        change d j < h+1 ∧ v j ∈ E (d j+1)
        exact ⟨(hmem j).1.trans (Nat.lt_succ_self h), (hmem j).2⟩
      | inr j =>
        change h < h+1 ∧ w j ∈ E (h+1)
        exact ⟨Nat.lt_succ_self h, hCle (b j).property⟩
    · change (∑ i, d' (e i)) = _
      rw [e.sum_comp, Fintype.sum_sum_type, Finset.sum_range_succ]
      change (∑ i, d i) + (∑ _ : Fin (finrank ℝ C), h) = _
      rw [hsum]
      simp [hCdim, Nat.mul_comm]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FloorArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem square_quarter_even (r : ℕ) : (2*r)*(2*r)/4 = r*r := by
  rw [show (2*r)*(2*r) = r*r*4 by ring, Nat.mul_div_left _ (by decide : 0<4)]

theorem square_quarter_odd (r : ℕ) : (2*r+1)*(2*r+1)/4 = r*r+r := by
  rw [show (2*r+1)*(2*r+1) = 1+(r*r+r)*4 by ring,
    Nat.add_mul_div_right _ _ (by decide : 0<4)]
  omega

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

theorem diagonal_floor_identity (m : ℕ) :
    2*axisPairs m + m + 2*(m*m/4) = m*m := by
  have hm : m = 2*(m/2) ∨ m = 2*(m/2)+1 := by omega
  rcases hm with hm | hm
  · generalize m/2 = r at hm
    subst m
    rw [axisPairs_even, square_quarter_even]
    cases r with
    | zero => simp
    | succ r => simp only [Nat.add_sub_cancel]; ring
  · generalize m/2 = r at hm
    subst m
    rw [axisPairs_odd, square_quarter_odd]
    ring

end Zarankiewicz

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

theorem crossing_two_edges (D : AdmissibleDrawing m n) (x : Plane)
    (hx : x ∈ crossingPoints D.toContinuousDrawing) :
    ∃ e f : BipartiteEdge m n, e ≠ f ∧
      ∀ g, x ∈ edgeInterior D.toContinuousDrawing g ↔ g = e ∨ g = f := by
  obtain ⟨e,f,hef,he,hf⟩ := hx
  exact ⟨e,f,hef,crossing_incident_iff D x e f hef he hf⟩

theorem pairCrossings_self (D : AdmissibleDrawing m n) (e : BipartiteEdge m n) :
    pairCrossings D e e = ∅ := by
  simp [pairCrossings]

theorem crossing_ordered_incidence (D : AdmissibleDrawing m n) (x : Plane)
    (hx : x ∈ crossingPoints D.toContinuousDrawing) :
    (∑ e : BipartiteEdge m n, ∑ f : BipartiteEdge m n,
      if e ≠ f ∧ x ∈ edgeInterior D.toContinuousDrawing e ∧
        x ∈ edgeInterior D.toContinuousDrawing f then (1 : ℕ) else 0) = 2 := by
  classical
  obtain ⟨e,f,hef,hinc⟩ := crossing_two_edges D x hx
  simp_rw [hinc]
  have hp : ∀ a b : BipartiteEdge m n,
      (a ≠ b ∧ (a = e ∨ a = f) ∧ (b = e ∨ b = f)) ↔
        ((a = e ∧ b = f) ∨ (a = f ∧ b = e)) := by
    intro a b
    constructor
    · rintro ⟨hab, rfl | rfl, rfl | rfl⟩ <;> tauto
    · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> tauto
  simp_rw [hp]
  have hi : ∀ a b : BipartiteEdge m n,
      (if (a = e ∧ b = f) ∨ (a = f ∧ b = e) then (1 : ℕ) else 0) =
        (if a = e ∧ b = f then 1 else 0) + (if a = f ∧ b = e then 1 else 0) := by
    intro a b
    split_ifs <;> simp_all
  simp_rw [hi, Finset.sum_add_distrib]
  simp [ite_and]

theorem sum_pairCrossings_card (D : AdmissibleDrawing m n) :
    (∑ e : BipartiteEdge m n, ∑ f : BipartiteEdge m n, (pairCrossings D e f).card) =
      2 * crossingCount D := by
  classical
  simp only [pairCrossings, Finset.card_filter]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext f; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have he : ∀ x ∈ D.crossings_finite.toFinset,
      (∑ f : BipartiteEdge m n, ∑ e : BipartiteEdge m n,
        if e ≠ f ∧ x ∈ edgeInterior D.toContinuousDrawing e ∧
          x ∈ edgeInterior D.toContinuousDrawing f then (1 : ℕ) else 0) = 2 := by
    intro x hx
    rw [Finset.sum_comm]
    exact crossing_ordered_incidence D x (by simpa using hx)
  simp_rw [Finset.sum_congr rfl he]
  simp [crossingCount, Nat.mul_comm]

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

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RowCrossingCount
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

theorem pairCrossings_eq_empty_of_adjacent (D : AdmissibleDrawing m n)
    (hnorm : NoAdjacentCrossings D) (e f : BipartiteEdge m n)
    (hadj : e.1 = f.1 ∨ e.2 = f.2) : pairCrossings D e f = ∅ := by
  by_cases hef : e = f
  · subst f
    exact pairCrossings_self D e
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hmem := (Finset.mem_filter.mp hx).2
    have hi : x ∈ edgeInterior D.toContinuousDrawing e ∩ edgeInterior D.toContinuousDrawing f :=
      ⟨hmem.2.1,hmem.2.2⟩
    rw [hnorm e f hef hadj] at hi
    exact hi

theorem rowCrossingCount_self (D : AdmissibleDrawing m n) (hnorm : NoAdjacentCrossings D)
    (i : Fin m) : rowCrossingCount D i i = 0 := by
  unfold rowCrossingCount
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro q hq
  rw [pairCrossings_eq_empty_of_adjacent D hnorm (i,p) (i,q) (Or.inl rfl), Finset.card_empty]

theorem sum_rowCrossingCount (D : AdmissibleDrawing m n) :
    (∑ i : Fin m, ∑ k : Fin m, rowCrossingCount D i k) = 2*crossingCount D := by
  have h := sum_pairCrossings_card D
  change (∑ e : Fin m × Fin n, ∑ f : Fin m × Fin n, (pairCrossings D e f).card) = _ at h
  simp only [Fintype.sum_prod_type] at h
  calc
    _ = ∑ i : Fin m, ∑ p : Fin n, ∑ k : Fin m, ∑ q : Fin n,
        (pairCrossings D (i,p) (k,q)).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := h

theorem sum_offDiagonal_rowCrossingCount (D : AdmissibleDrawing m n)
    (hnorm : NoAdjacentCrossings D) :
    (∑ i : Fin m, ∑ k ∈ Finset.univ.erase i, rowCrossingCount D i k) = 2*crossingCount D := by
  rw [← sum_rowCrossingCount D]
  apply Finset.sum_congr rfl
  intro i hi
  have he := Finset.sum_erase_add Finset.univ (rowCrossingCount D i) (Finset.mem_univ i)
  simpa only [rowCrossingCount_self D hnorm, add_zero] using he

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

end VertexTruncation
end Zarankiewicz

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

theorem signedIntersection_self (e : BipartiteEdge m n) : V.signedIntersection e e=0 := by
  simp [signedIntersection]

theorem signedIntersection_zero_of_pairCrossings_empty {A : AdmissibleDrawing m n}
    (V : VertexTruncation A.toContinuousDrawing) (e f : BipartiteEdge m n)
    (hempty : pairCrossings A e f=∅) : V.signedIntersection e f=0 := by
  classical
  by_cases hef : e=f
  · subst f
    exact V.signedIntersection_self e
  · rw [signedIntersection,ite_eq_right hef]
    unfold polygonIntersection
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hnot : ¬ SegmentsCrossProperly (V.vertices e i) (V.vertices e (i+1))
        (V.vertices f j) (V.vertices f (j+1)) := by
      rintro ⟨_,s,hs,t,ht,he⟩
      let x := segmentPoint (V.vertices e i) (V.vertices e (i+1)) s
      have hxe : x ∈ edgeInterior A.toContinuousDrawing e := by
        apply V.range_subset_edgeInterior e
        apply V.piece_subset_range e i (Finset.mem_range.mp hi)
        rw [← Path.range_segment]
        exact ⟨⟨s,⟨hs.1.le,hs.2.le⟩⟩,by simp only [Path.segment_apply,AffineMap.lineMap_apply_module,x,segmentPoint]⟩
      have hxf : x ∈ edgeInterior A.toContinuousDrawing f := by
        apply V.range_subset_edgeInterior f
        apply V.piece_subset_range f j (Finset.mem_range.mp hj)
        rw [← Path.range_segment]
        refine ⟨⟨t,⟨ht.1.le,ht.2.le⟩⟩,?_⟩
        simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,x,segmentPoint] using he.symm
      have hx : x ∈ pairCrossings A e f := by
        apply Finset.mem_filter.mpr
        exact ⟨by simpa using (show x ∈ crossingPoints A.toContinuousDrawing from ⟨e,f,hef,hxe,hxf⟩),hef,hxe,hxf⟩
      rw [hempty] at hx
      exact Finset.notMem_empty x hx
    simp [segmentCrossingSign,hnot]

theorem pairCrossings_pos_of_signedIntersection_ne_zero {A : AdmissibleDrawing m n}
    (V : VertexTruncation A.toContinuousDrawing) (e f : BipartiteEdge m n)
    (h : V.signedIntersection e f ≠ 0) : 0 < (pairCrossings A e f).card := by
  by_contra hh
  have hz : (pairCrossings A e f).card=0 := by omega
  exact h (V.signedIntersection_zero_of_pairCrossings_empty e f (Finset.card_eq_zero.mp hz))

end Zarankiewicz.VertexTruncation

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

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_MatrixRankBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module
open scoped BigOperators
variable {κ ρ : Type*} [Fintype κ] [Fintype ρ] [DecidableEq ρ]

theorem matrix_rank_add_le
    {κ ρ : Type*} [Fintype κ] [Fintype ρ] [DecidableEq ρ]
    (A B : Matrix κ ρ ℝ) : (A+B).rank ≤ A.rank+B.rank := by
  change finrank ℝ (LinearMap.range (A+B).mulVecLin) ≤ _
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem matrix_rank_smul_le
    {κ ρ : Type*} [Fintype κ] [Fintype ρ] [DecidableEq ρ]
    (c : ℝ) (A : Matrix κ ρ ℝ) : (c • A).rank ≤ A.rank := by
  by_cases hc : c = 0
  · simp [hc, Matrix.rank_zero]
  · rw [Matrix.rank_smul_of_mem_nonZeroDivisors A (mem_nonZeroDivisors_of_ne_zero hc)]

theorem matrix_rank_sum_le {α : Type*} (S : Finset α) (A : α → Matrix κ ρ ℝ) :
    (∑ a ∈ S, A a).rank ≤ ∑ a ∈ S, (A a).rank := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | @insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact (matrix_rank_add_le _ _).trans (Nat.add_le_add_left ih _)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolynomialKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

variable {ι : Type*}

variable (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)

theorem constrainedCoefficients_injective (k : ℕ) :
    Function.Injective (constrainedCoefficients U node Z k) := by
  intro p q he
  apply Subtype.ext
  apply PolynomialModule.ext
  apply Finsupp.ext
  intro n
  by_cases hn : n < k
  · exact congrFun he ⟨n, hn⟩
  · rw [p.property.1 n (by omega), q.property.1 n (by omega)]

instance constrained_finiteDimensional [FiniteDimensional ℝ W] (k : ℕ) :
    FiniteDimensional ℝ (constrained U node Z k) :=
  FiniteDimensional.of_injective (constrainedCoefficients U node Z k)
    (constrainedCoefficients_injective U node Z k)

theorem finrank_eval_range [FiniteDimensional ℝ W] (h : ℕ) (t : ℝ)
    (ht : ∀ i, node i ≠ t) :
    Module.finrank ℝ (LinearMap.range (constrainedEval U node Z (h+1) t)) =
      rankIncrement U node Z h := by
  have he := (evalKernelEquiv U node Z h t ht).finrank_eq
  have hr := (constrainedEval U node Z (h+1) t).finrank_range_add_finrank_ker
  unfold rankIncrement
  omega

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_Interpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
open scoped BigOperators
variable {W : Type*} [AddCommGroup W] [Module ℝ W]
variable {ι : Type*}

variable [Fintype ι]
variable (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)

theorem finrank_constrained_zero
    {W : Type*} [AddCommGroup W] [Module ℝ W] {ι : Type*} [Fintype ι]
    (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)
    : Module.finrank ℝ (constrained U node Z 0) = 0 := by
  have hz : constrained U node Z 0 = ⊥ := by
    apply le_antisymm _ bot_le
    intro p hp
    exact (Submodule.mem_bot ℝ).mpr ((bounded_zero_iff p).mp hp.1)
  rw [hz]
  simp

theorem constrained_finrank_mono
    {W : Type*} [AddCommGroup W] [Module ℝ W] {ι : Type*} [Fintype ι]
    (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)
    [FiniteDimensional ℝ W] :
    Monotone (fun k => Module.finrank ℝ (constrained U node Z k)) := by
  intro k l hkl
  exact Submodule.finrank_mono (fun p hp => ⟨bounded_mono hp.1 hkl, hp.2⟩)

theorem sum_rankIncrement [FiniteDimensional ℝ W] (m : ℕ) :
    ∑ h ∈ Finset.range m, rankIncrement U node Z h =
      Module.finrank ℝ (constrained U node Z m) := by
  unfold rankIncrement
  rw [Finset.sum_range_tsub (constrained_finrank_mono U node Z), finrank_constrained_zero,
    Nat.sub_zero]

theorem interpolation_identity [FiniteDimensional ℝ W] (hn : Function.Injective node) :
    ∑ h ∈ Finset.range (Fintype.card ι), rankIncrement U node Z h =
      ∑ i, Module.finrank ℝ ↥(U i ⊓ Z) := by
  rw [sum_rankIncrement, (nodeEvaluationEquiv U node Z hn).finrank_eq,
    Module.finrank_pi_fintype]

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

theorem detectorAtom_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (node : ι → ℝ) (p : ι) : detectorAtom s node p p = 0 := by
  simp [detectorAtom, detectorWeight]

theorem rankDetector_diagonal (s : ℕ) (node : ι → ℝ) (d : ι → ℝ) :
    rankDetector s node (Matrix.diagonal d) = 0 := by
  change (∑ p, ∑ q, Matrix.diagonal d p q • detectorAtom s node p q) = 0
  simp [Matrix.diagonal_apply, detectorAtom_self]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DetectorRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem detectorAtom_rank_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (node : ι → ℝ) (p q : ι) :
    (detectorAtom s node p q).rank ≤ 1 :=
  (matrix_rank_smul_le _ _).trans (Matrix.rank_vecMulVec_le _ _)

theorem rankDetector_support_bound (s : ℕ) (node : ι → ℝ) (H : Matrix ι ι ℝ) :
    (rankDetector s node H).rank ≤
      (Finset.univ.filter (fun pq : ι × ι => pq.1 ≠ pq.2 ∧ H pq.1 pq.2 ≠ 0)).card := by
  let S := Finset.univ.filter (fun pq : ι × ι => pq.1 ≠ pq.2 ∧ H pq.1 pq.2 ≠ 0)
  have he : rankDetector s node H = ∑ pq ∈ S, H pq.1 pq.2 • detectorAtom s node pq.1 pq.2 := by
    change (∑ p, ∑ q, H p q • detectorAtom s node p q) = _
    rw [← Fintype.sum_prod_type (fun pq : ι × ι => H pq.1 pq.2 • detectorAtom s node pq.1 pq.2)]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro pq hpq hnot
    have hnot' : ¬(pq.1 ≠ pq.2 ∧ H pq.1 pq.2 ≠ 0) := by simpa [S] using hnot
    by_cases heq : pq.1 = pq.2
    · simp [heq, detectorAtom_self]
    · have hz : H pq.1 pq.2 = 0 := by tauto
      rw [hz, zero_smul]
  rw [he]
  calc
    _ ≤ ∑ pq ∈ S, (H pq.1 pq.2 • detectorAtom s node pq.1 pq.2).rank := matrix_rank_sum_le S _
    _ ≤ ∑ _pq ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro pq hpq
      exact (matrix_rank_smul_le _ _).trans (detectorAtom_rank_le_one s node pq.1 pq.2)
    _ = _ := by simp [S]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DetectorCrossingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
open scoped BigOperators
variable {m n : ℕ} {D : AdmissibleDrawing m n} (V : VertexTruncation D.toContinuousDrawing)

theorem detector_rank_le_rowCrossingCount (s : ℕ) (node : Fin n → ℝ) (i k : Fin m) :
    (rankDetector s node (V.intersectionBlock i k)).rank ≤ rowCrossingCount D i k := by
  classical
  apply (rankDetector_support_bound s node (V.intersectionBlock i k)).trans
  rw [Finset.card_filter,Fintype.sum_prod_type]
  unfold rowCrossingCount
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  by_cases hh : p ≠ q ∧ V.intersectionBlock i k p q ≠ 0
  · rw [ite_eq_left hh]
    exact V.pairCrossings_pos_of_signedIntersection_ne_zero (i,p) (k,q) hh.2
  · rw [ite_eq_right hh]
    exact Nat.zero_le _

theorem ordered_detector_rank_le_twice_crossings (hnorm : NoAdjacentCrossings D)
    (s : ℕ) (node : Fin n → ℝ) :
    (∑ i : Fin m, ∑ k ∈ Finset.univ.erase i, (rankDetector s node (V.intersectionBlock i k)).rank) ≤
      2*crossingCount D := by
  rw [← sum_offDiagonal_rowCrossingCount D hnorm]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro k hk
  exact V.detector_rank_le_rowCrossingCount s node i k

end Zarankiewicz.VertexTruncation

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CycleMatrixBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem flagPairing_left_block (i k : Fin m) (p q : Fin n) :
    C.flagPairing (dartSourceFlag (forwardBipartiteDart (i,p)))
      (dartSourceFlag (forwardBipartiteDart (k,q)))=if i=k then C.leftHalfOrder i p q else 0 := by
  by_cases h : i=k
  · subst k
    change (if h : (Sum.inl i : BipartiteVertex m n)=Sum.inl i then
      orderSign (C.node (Sum.inl i) (V.leftIncident (i,p)))
        (C.node (Sum.inl i) (incidentCast h (V.leftIncident (i,q))))/2 else 0)=_
    rw [dite_eq_left rfl,incidentCast_refl,ite_eq_left rfl]
    rfl
  · have hn : (Sum.inl k : BipartiteVertex m n) ≠ Sum.inl i := fun he => h (Sum.inl.inj he).symm
    simp only [flagPairing,dartSourceFlag,forwardBipartiteDart,ite_eq_right h]
    exact dite_eq_right hn

theorem flagPairing_right_block (i k : Fin m) (p q : Fin n) :
    C.flagPairing (dartTargetFlag (forwardBipartiteDart (i,p)))
      (dartTargetFlag (forwardBipartiteDart (k,q)))=if p=q then C.rightHalfOrder p i k else 0 := by
  by_cases h : p=q
  · subst q
    change (if h : (Sum.inr p : BipartiteVertex m n)=Sum.inr p then
      orderSign (C.node (Sum.inr p) (V.rightIncident (i,p)))
        (C.node (Sum.inr p) (incidentCast h (V.rightIncident (k,p))))/2 else 0)=_
    rw [dite_eq_left rfl,incidentCast_refl,ite_eq_left rfl]
    rfl
  · have hn : (Sum.inr q : BipartiteVertex m n) ≠ Sum.inr p := fun he => h (Sum.inr.inj he).symm
    simp only [flagPairing,dartTargetFlag,forwardBipartiteDart,ite_eq_right h]
    exact dite_eq_right hn

theorem cycleIntersectionMatrix_entry (i k : Fin m) (p q : Fin n) :
    C.cycleIntersectionMatrix (i,p) (k,q)=V.signedIntersection (i,p) (k,q)+
      (if i=k then C.leftHalfOrder i p q else 0)+(if p=q then C.rightHalfOrder p i k else 0) := by
  rw [cycleIntersectionMatrix,edgeEndpointPairing,C.flagPairing_left_block,C.flagPairing_right_block]
  ring

theorem cycleIntersectionMatrix_offDiagonal_block (i k : Fin m) (hik : i ≠ k) :
    edgeBlock C.cycleIntersectionMatrix i k=V.intersectionBlock i k+
      Matrix.diagonal (fun p => C.rightHalfOrder p i k) := by
  ext p q
  rw [edgeBlock,C.cycleIntersectionMatrix_entry,ite_eq_right hik]
  simp only [Matrix.add_apply,VertexTruncation.intersectionBlock,Matrix.diagonal_apply,add_zero]

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DegreeCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz
open scoped BigOperators

theorem triangular_degree_sum (ell : ℕ → ℕ) (m : ℕ) :
    (∑ h ∈ Finset.range m, ∑ e ∈ Finset.range (h+1), e * ell e) =
      ∑ e ∈ Finset.range m, e * (m-e) * ell e := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel_left, mul_one]
    have hc : ∀ e ∈ Finset.range m,
        e * (m+1-e) * ell e = e * (m-e) * ell e + e * ell e := by
      intro e he
      have ht : m+1-e = (m-e)+1 := by have := Finset.mem_range.mp he; omega
      rw [ht]
      ring
    simp_rw [Finset.sum_congr rfl hc, Finset.sum_add_distrib]
    omega

theorem parabola_le_floor (m e : ℕ) (he : e ≤ m) : e * (m-e) ≤ m*m/4 := by
  have hm : ((m-e : ℕ) : ℤ) + (e : ℤ) = (m : ℤ) := by
    exact_mod_cast Nat.sub_add_cancel he
  have hz : (4 : ℤ) * (e : ℤ) * ((m-e : ℕ) : ℤ) ≤ (m : ℤ) * (m : ℤ) := by
    nlinarith [sq_nonneg ((e : ℤ) - ((m-e : ℕ) : ℤ))]
  have hn : 4 * e * (m-e) ≤ m*m := by exact_mod_cast hz
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  nlinarith

theorem total_degree_cost_le (ell : ℕ → ℕ) (m N : ℕ)
    (hell : ∑ e ∈ Finset.range m, ell e ≤ N) :
    (∑ h ∈ Finset.range m, ∑ e ∈ Finset.range (h+1), e * ell e) ≤ (m*m/4) * N := by
  rw [triangular_degree_sum]
  calc
    (∑ e ∈ Finset.range m, e * (m-e) * ell e) ≤
        ∑ e ∈ Finset.range m, (m*m/4) * ell e := by
      apply Finset.sum_le_sum
      intro e he
      exact Nat.mul_le_mul_right (ell e) (parabola_le_floor m e (Nat.le_of_lt (Finset.mem_range.mp he)))
    _ = (m*m/4) * ∑ e ∈ Finset.range m, ell e := (Finset.mul_sum ..).symm
    _ ≤ (m*m/4) * N := Nat.mul_le_mul_left _ hell

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolynomialMinors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem natDegree_det_le_column_sum (M : Matrix κ κ ℝ[X]) (e : κ → ℕ)
    (he : ∀ i j, (M i j).natDegree ≤ e j) :
    M.det.natDegree ≤ ∑ j, e j := by
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ hσ
  apply (natDegree_smul_le _ _).trans
  exact (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun j _ => he (σ j) j)

theorem pow_card_dvd_det_of_columns_vanish (M : Matrix κ κ ℝ[X]) (t : ℝ)
    (S : Finset κ) (hv : ∀ j ∈ S, ∀ i, (M i j).eval t = 0) :
    (X - C t)^S.card ∣ M.det := by
  let v : κ → ℝ[X] := fun j => if j ∈ S then X-C t else 1
  let A : Matrix κ κ ℝ[X] := fun i j => if j ∈ S then M i j /ₘ (X-C t) else M i j
  have hM : M = Matrix.of (fun i j => v j * A i j) := by
    funext i j
    by_cases hj : j ∈ S
    · simp only [Matrix.of_apply, v, A, hj, ite_true]
      exact (mul_divByMonic_eq_iff_isRoot.mpr (hv j hj i)).symm
    · simp [v, A, hj]
  have hprod : ∏ j, v j = (X-C t)^S.card := by
    simp [v]
  rw [hM, Matrix.det_mul_row, hprod]
  exact dvd_mul_right _ _

theorem prod_pow_roots_dvd {ι : Type*} [Fintype ι] (node : ι → ℝ)
    (hn : Function.Injective node) (q : ι → ℕ) (p : ℝ[X])
    (hq : ∀ i, (X-C (node i))^(q i) ∣ p) :
    (∏ i, (X-C (node i))^(q i)) ∣ p := by
  apply Fintype.prod_dvd_of_coprime _ hq
  intro i j hij
  exact (pairwise_coprime_X_sub_C hn hij).pow

theorem sum_multiplicities_le_natDegree {ι : Type*} [Fintype ι] (node : ι → ℝ)
    (hn : Function.Injective node) (q : ι → ℕ) (p : ℝ[X]) (hp : p ≠ 0)
    (hq : ∀ i, (X-C (node i))^(q i) ∣ p) :
    ∑ i, q i ≤ p.natDegree := by
  have hd := natDegree_le_of_dvd (prod_pow_roots_dvd node hn q p hq) hp
  rw [natDegree_prod_of_monic] at hd
  · simpa only [natDegree_pow, natDegree_X_sub_C, mul_one] using hd
  · intro i hi
    exact (monic_X_sub_C (node i)).pow (q i)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RankSpecialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators
variable {μ ν : Type*} [Fintype μ] [Fintype ν]

theorem exists_row_minor [DecidableEq ν] (A : Matrix μ ν ℝ) (hA : LinearIndependent ℝ A.col) :
    ∃ r : ν → μ, Function.Injective r ∧ (A.submatrix r id).det ≠ 0 := by
  classical
  obtain ⟨ι, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ A.row
  let : Fintype ι := Fintype.ofInjective a ha
  have hcard : Fintype.card ι = Fintype.card ν := by
    rw [← finrank_span_eq_card hli, hspan, ← A.rank_eq_finrank_span_row,
      A.rank_eq_finrank_span_cols, finrank_span_eq_card hA]
  let e : ν ≃ ι := Fintype.equivOfCardEq hcard.symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  have hrows : LinearIndependent ℝ (A.submatrix (a ∘ e) id).row := hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

theorem exists_rank_minor (A : Matrix μ ν ℝ) :
    ∃ (r : Fin A.rank → μ) (c : Fin A.rank → ν),
      Function.Injective r ∧ Function.Injective c ∧ (A.submatrix r c).det ≠ 0 := by
  classical
  obtain ⟨ι, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ A.col
  let : Fintype ι := Fintype.ofInjective a ha
  have hcard : Fintype.card ι = A.rank := by
    rw [← finrank_span_eq_card hli, hspan, A.rank_eq_finrank_span_cols]
  let e : Fin A.rank ≃ ι := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let c : Fin A.rank → ν := a ∘ e
  have hc : LinearIndependent ℝ (A.submatrix id c).col := hli.comp e e.injective
  obtain ⟨r, hr, hd⟩ := exists_row_minor (A.submatrix id c) hc
  refine ⟨r, c, hr, ha.comp e.injective, ?_⟩
  simpa [Matrix.submatrix_submatrix] using hd

theorem polynomial_rank_specialization (M : Matrix μ ν ℝ[X]) (nodes : Finset ℝ)
    (b : ℕ) (hb : ∀ t ∉ nodes, (M.map (Polynomial.eval t)).rank ≤ b) (t₀ : ℝ) :
    (M.map (Polynomial.eval t₀)).rank ≤ b := by
  classical
  let A := M.map (Polynomial.eval t₀)
  by_contra h
  have hlt : b < A.rank := Nat.lt_of_not_ge h
  obtain ⟨r, c, hr, hc, hd⟩ := exists_rank_minor A
  let P : ℝ[X] := (M.submatrix r c).det
  have evalP (t : ℝ) : P.eval t = ((M.map (Polynomial.eval t)).submatrix r c).det := by
    exact (evalRingHom t).map_det (M.submatrix r c)
  have hP : P ≠ 0 := by
    intro hzero
    apply hd
    change ((M.map (Polynomial.eval t₀)).submatrix r c).det = 0
    rw [← evalP, hzero, eval_zero]
  obtain ⟨t, ht⟩ := (nodes ∪ P.roots.toFinset).exists_notMem
  have htN : t ∉ nodes := fun htn => ht (Finset.mem_union_left _ htn)
  have htP : P.eval t ≠ 0 := by
    intro hz
    exact ht (Finset.mem_union_right _ (by simpa [mem_roots hP] using hz))
  have hm : (((M.map (Polynomial.eval t)).submatrix r c)).rank = A.rank := by
    simpa using Matrix.rank_of_det_ne_zero (show
      ((M.map (Polynomial.eval t)).submatrix r c).det ≠ 0 by rwa [← evalP])
  have hle := Matrix.rank_submatrix_le (M.map (Polynomial.eval t)) r c
  rw [hm] at hle
  exact (not_le_of_gt hlt) (hle.trans (hb t htN))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolynomialCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
open scoped BigOperators
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

theorem scalarPolynomial_coeff (f : W →ₗ[ℝ] ℝ) (p : PolynomialModule ℝ W) (n : ℕ) :
    (scalarPolynomial f p).coeff n = f (p.coeff n) := rfl

theorem scalarPolynomial_eval (f : W →ₗ[ℝ] ℝ) (p : PolynomialModule ℝ W) (t : ℝ) :
    (scalarPolynomial f p).eval t = f (eval t p) := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | single n w =>
    simp [scalarPolynomial, PolynomialModule.map_single, Polynomial.eval_monomial,
      _root_.map_smul, smul_eq_mul, mul_comm]

theorem scalarPolynomial_natDegree_le (f : W →ₗ[ℝ] ℝ) (p : PolynomialModule ℝ W)
    (h : ℕ) (hp : Bounded (h+1) p) : (scalarPolynomial f p).natDegree ≤ h := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [scalarPolynomial_coeff, hp n (by omega), map_zero]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem polynomialColumnMatrix_eval
    {W : Type*} [AddCommGroup W] [Module ℝ W] {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℝ W) (p : κ → PolynomialModule ℝ W)
    (t : ℝ) (i : ι) (j : κ) :
    (polynomialColumnMatrix b p i j).eval t = b.repr (eval t (p j)) i :=
  scalarPolynomial_eval (b.coord i) (p j) t

theorem exists_polynomial_minor (b : Module.Basis ι ℝ W) (p : κ → PolynomialModule ℝ W)
    (d : κ → ℕ) (hp : ∀ j, Bounded (d j+1) (p j)) (t : ℝ)
    (hli : LinearIndependent ℝ (fun j => eval t (p j))) :
    ∃ r : κ → ι, Function.Injective r ∧
      let Δ := ((polynomialColumnMatrix b p).submatrix r id).det
      Δ.eval t ≠ 0 ∧ Δ.natDegree ≤ ∑ j, d j := by
  classical
  let A := (polynomialColumnMatrix b p).map (Polynomial.eval t)
  have hA : LinearIndependent ℝ A.col := by
    have hh := hli.map' b.equivFun.toLinearMap (LinearMap.ker_eq_bot.mpr b.equivFun.injective)
    have hcols : A.col = b.equivFun ∘ (fun j => eval t (p j)) := by
      funext j i
      exact polynomialColumnMatrix_eval b p t i j
    rw [hcols]
    exact hh
  obtain ⟨r, hr, hd⟩ := exists_row_minor A hA
  refine ⟨r, hr, ?_, ?_⟩
  · have he := (Polynomial.evalRingHom t).map_det ((polynomialColumnMatrix b p).submatrix r id)
    exact he.trans_ne hd
  · apply natDegree_det_le_column_sum
    intro i j
    exact scalarPolynomial_natDegree_le (b.coord (r i)) (p j) (d j) (hp j)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolynomialFiltration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule Module Submodule
open scoped BigOperators
variable {W ι : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
variable (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)

theorem evaluationFiltration_mono
    {W ι : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)
    (t : ℝ) : Monotone (evaluationFiltration U node Z t) := by
  intro k l hkl z hz
  obtain ⟨p, hp⟩ := hz
  exact ⟨⟨p.val, bounded_mono p.property.1 hkl, p.property.2⟩, hp⟩

theorem evaluationFiltration_zero
    {W ι : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)
    (t : ℝ) : evaluationFiltration U node Z t 0 = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨p, hp⟩ := hz
  have hp0 : p.val = 0 := (bounded_zero_iff p.val).mp p.property.1
  change eval t p.val = z at hp
  rw [hp0, map_zero] at hp
  exact (Submodule.mem_bot ℝ).mpr hp.symm

theorem sum_columnIncrement (t : ℝ) (m : ℕ) :
    ∑ e ∈ Finset.range m, columnIncrement U node Z t e =
      finrank ℝ (evaluationFiltration U node Z t m) := by
  unfold columnIncrement
  rw [Finset.sum_range_tsub (fun k l hkl => Submodule.finrank_mono
    (evaluationFiltration_mono U node Z t hkl)), evaluationFiltration_zero,
    finrank_bot, Nat.sub_zero]

theorem exists_adapted_polynomials (t : ℝ) (h : ℕ) :
    ∃ (p : Fin (finrank ℝ (evaluationFiltration U node Z t (h+1))) → PolynomialModule ℝ Z)
      (d : Fin (finrank ℝ (evaluationFiltration U node Z t (h+1))) → ℕ),
      (∀ j, p j ∈ constrained U node Z (d j+1) ∧ d j ≤ h) ∧
      LinearIndependent ℝ (fun j => eval t (p j)) ∧
      span ℝ (Set.range (fun j => eval t (p j))) = evaluationFiltration U node Z t (h+1) ∧
      (∑ j, d j) = ∑ e ∈ Finset.range (h+1), e * columnIncrement U node Z t e := by
  obtain ⟨v, d, hli, hspan, hmem, hsum⟩ := exists_adapted_family
    (evaluationFiltration U node Z t) (evaluationFiltration_mono U node Z t)
    (evaluationFiltration_zero U node Z t) (h+1)
  have hex : ∀ i, ∃ p : constrained U node Z (d i+1),
      constrainedEval U node Z (d i+1) t p = v i := fun i => (hmem i).2
  choose p hp using hex
  have hpv : (fun i => eval t (p i).val) = v := funext hp
  refine ⟨fun i => (p i).val, d, ?_, ?_, ?_, hsum⟩
  · intro i
    exact ⟨(p i).property, Nat.le_of_lt_succ (hmem i).1⟩
  · rw [hpv]
    exact hli
  · rw [hpv]
    exact hspan

theorem exists_adapted_minor {κ : Type*} [Fintype κ] (b : Basis κ ℝ Z)
    (t : ℝ) (_ht : ∀ i, node i ≠ t) (h : ℕ) :
    ∃ (p : Fin (finrank ℝ (evaluationFiltration U node Z t (h+1))) → PolynomialModule ℝ Z)
      (d : Fin (finrank ℝ (evaluationFiltration U node Z t (h+1))) → ℕ)
      (r : Fin (finrank ℝ (evaluationFiltration U node Z t (h+1))) → κ),
      (∀ j, p j ∈ constrained U node Z (d j+1) ∧ d j ≤ h) ∧ Function.Injective r ∧
      let Δ := ((polynomialColumnMatrix b p).submatrix r id).det
      Δ.eval t ≠ 0 ∧
      Δ.natDegree ≤ ∑ e ∈ Finset.range (h+1), e * columnIncrement U node Z t e := by
  obtain ⟨p, d, hp, hli, hspan, hsum⟩ := exists_adapted_polynomials U node Z t h
  obtain ⟨r, hr, hd, hdeg⟩ := exists_polynomial_minor b p d (fun j => (hp j).1.1) t hli
  exact ⟨p, d, r, hp, hr, hd, hsum ▸ hdeg⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_EvaluationAmbient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule Module Submodule
variable {W ι : Type*} [AddCommGroup W] [Module ℝ W]
variable (U : ι → Submodule ℝ W) (node : ι → ℝ)

theorem constrainedInclusion_eval {Z₁ Z₂ : Submodule ℝ W} (hZ : Z₁ ≤ Z₂) (k : ℕ)
    (t : ℝ) (p : constrained U node Z₁ k) :
    Z₂.subtype (eval t (constrainedInclusion U node hZ k p).val) = Z₁.subtype (eval t p.val) := by
  change Z₂.subtype (eval t (PolynomialModule.map ℝ (Submodule.inclusion hZ) p.val)) = _
  rw [show eval t (PolynomialModule.map ℝ (Submodule.inclusion hZ) p.val) =
    Submodule.inclusion hZ (eval t p.val) by
      simpa using PolynomialModule.eval_map ℝ (Submodule.inclusion hZ) p.val t]
  rfl

theorem finrank_ambientEvalRange (Z : Submodule ℝ W) (k : ℕ) (t : ℝ) :
    finrank ℝ (ambientEvalRange U node Z k t) = finrank ℝ (evaluationFiltration U node Z t k) := by
  unfold ambientEvalRange ambientEval evaluationFiltration
  rw [LinearMap.range_comp]
  exact Submodule.finrank_map_subtype_eq Z _

theorem finrank_ambientEvalRange_off_node [FiniteDimensional ℝ W]
    (Z : Submodule ℝ W) (h : ℕ) (t : ℝ) (ht : ∀ i, node i ≠ t) :
    finrank ℝ (ambientEvalRange U node Z (h+1) t) = rankIncrement U node Z h := by
  rw [finrank_ambientEvalRange]
  exact finrank_eval_range U node Z h t ht

theorem ambientEvalRange_mono_coeff {Z₁ Z₂ : Submodule ℝ W} (hZ : Z₁ ≤ Z₂) (k : ℕ) (t : ℝ) :
    ambientEvalRange U node Z₁ k t ≤ ambientEvalRange U node Z₂ k t := by
  intro z hz
  obtain ⟨p, hp⟩ := hz
  refine ⟨constrainedInclusion U node hZ k p, ?_⟩
  exact (constrainedInclusion_eval U node hZ k t p).trans hp

theorem ambientEvalRange_le_coeff (Z : Submodule ℝ W) (k : ℕ) (t : ℝ) :
    ambientEvalRange U node Z k t ≤ Z := by
  intro z hz
  obtain ⟨p, rfl⟩ := hz
  exact (eval t p.val).property

theorem ambientEvalRange_at_node_le (Z : Submodule ℝ W) (k : ℕ) (i : ι) :
    ambientEvalRange U node Z k (node i) ≤ U i := by
  intro z hz
  obtain ⟨p, rfl⟩ := hz
  exact p.property.2 i

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_MatrixGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module Submodule
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem matrix_graph_finrank_add_rank (d : ℕ) (X Y : Matrix (Fin d) (Fin d) ℝ) :
    finrank ℝ ↥(X.mulVecLin.graph ⊓ Y.mulVecLin.graph) + (X-Y).rank = d := by
  have hdiff : X.mulVecLin - Y.mulVecLin = (X-Y).mulVecLin :=
    (map_sub (Matrix.mulVecBilin ℝ ℝ) X Y).symm
  have he := (graphKernelEquiv X.mulVecLin Y.mulVecLin).finrank_eq
  rw [hdiff] at he
  have hr := (X-Y).mulVecLin.finrank_range_add_finrank_ker
  change (X-Y).rank + finrank ℝ (LinearMap.ker (X-Y).mulVecLin) = finrank ℝ (Fin d → ℝ) at hr
  rw [he, Module.finrank_pi, Fintype.card_fin] at hr
  omega

theorem matrix_graph_disjoint (d : ℕ) (X Y : Matrix (Fin d) (Fin d) ℝ) (h : IsUnit (X-Y)) :
    Disjoint X.mulVecLin.graph Y.mulVecLin.graph := by
  apply disjoint_iff.mpr
  apply Submodule.finrank_eq_zero.mp
  have hh := matrix_graph_finrank_add_rank d X Y
  have hr := Matrix.rank_of_isUnit (X-Y) h
  simp only [Fintype.card_fin] at hr
  omega

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolynomialLinearMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule Module
variable {V W ι κ : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
variable [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem polynomialLinearMatrix_eval (bV : Basis κ ℝ V) (bW : Basis ι ℝ W)
    (F : V →ₗ[ℝ] PolynomialModule ℝ W) (t : ℝ) :
    (polynomialLinearMatrix bV bW F).map (Polynomial.eval t) =
      LinearMap.toMatrix bV bW ((eval t).comp F) := by
  funext i j
  rw [LinearMap.toMatrix_apply]
  exact polynomialColumnMatrix_eval bW (fun j => F (bV j)) t i j

theorem polynomialLinearMatrix_rank (bV : Basis κ ℝ V) (bW : Basis ι ℝ W)
    (F : V →ₗ[ℝ] PolynomialModule ℝ W) (t : ℝ) :
    ((polynomialLinearMatrix bV bW F).map (Polynomial.eval t)).rank =
      finrank ℝ (LinearMap.range ((eval t).comp F)) := by
  rw [polynomialLinearMatrix_eval, Matrix.rank_eq_finrank_range_toLin _ bW bV,
    Matrix.toLin_toMatrix]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SubspaceProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module Submodule
variable {W W' : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
variable [AddCommGroup W'] [Module ℝ W']

theorem finrank_map_add_le (f : W →ₗ[ℝ] W') (E T : Submodule ℝ W)
    (hTE : T ≤ E) (hTk : T ≤ LinearMap.ker f) :
    finrank ℝ (E.map f) + finrank ℝ T ≤ finrank ℝ E := by
  let g := f.comp E.subtype
  have hk : T.comap E.subtype ≤ LinearMap.ker g := fun x hx => hTk hx
  have hd := Submodule.finrank_mono hk
  rw [(Submodule.comapSubtypeEquivOfLe hTE).finrank_eq] at hd
  have hr := g.finrank_range_add_finrank_ker
  have he : LinearMap.range g = E.map f := by
    dsimp only [g]
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [he] at hr
  omega

theorem finrank_map_of_disjoint
    {W W' : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [AddCommGroup W'] [Module ℝ W']
    (f : W →ₗ[ℝ] W') (E : Submodule ℝ W)
    (hE : Disjoint E (LinearMap.ker f)) : finrank ℝ (E.map f) = finrank ℝ E := by
  let g := f.comp E.subtype
  have hg : Function.Injective g := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    have hm : x.val ∈ E ⊓ LinearMap.ker f := ⟨x.property, hx⟩
    rw [hE.eq_bot] at hm
    exact (Submodule.mem_bot ℝ).mpr (Subtype.ext ((Submodule.mem_bot ℝ).mp hm))
  have hr := LinearMap.finrank_range_of_inj hg
  change finrank ℝ (LinearMap.range (f.comp E.subtype)) = finrank ℝ E at hr
  rw [LinearMap.range_comp, Submodule.range_subtype] at hr
  exact hr

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_NodeRankLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule Module Submodule
variable {W ι : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
variable (U : ι → Submodule ℝ W) (node : ι → ℝ)

theorem off_node_projected_rank (V : Submodule ℝ W) (h : ℕ) (t : ℝ)
    (ht : ∀ i, node i ≠ t) :
    finrank ℝ ((ambientEvalRange U node ⊤ (h+1) t).map V.mkQ) + rankIncrement U node V h ≤
      rankIncrement U node ⊤ h := by
  have hh := finrank_map_add_le V.mkQ
    (ambientEvalRange U node ⊤ (h+1) t) (ambientEvalRange U node V (h+1) t)
    (ambientEvalRange_mono_coeff U node le_top (h+1) t)
    (by rw [Submodule.ker_mkQ]; exact ambientEvalRange_le_coeff U node V (h+1) t)
  rwa [finrank_ambientEvalRange_off_node U node V h t ht,
    finrank_ambientEvalRange_off_node U node ⊤ h t ht] at hh

theorem node_rank_loss [Fintype ι] (V : Submodule ℝ W) (j : ι)
    (hUV : Disjoint (U j) V) (h : ℕ) (tstar : ℝ) (htstar : ∀ i, node i ≠ tstar) :
    finrank ℝ (ambientEvalRange U node ⊤ (h+1) (node j)) + rankIncrement U node V h ≤
      rankIncrement U node ⊤ h := by
  classical
  let bP := finBasis ℝ (constrained U node ⊤ (h+1))
  let bQ := finBasis ℝ (W ⧸ V)
  let f : (⊤ : Submodule ℝ W) →ₗ[ℝ] (W ⧸ V) := V.mkQ.comp (⊤ : Submodule ℝ W).subtype
  let F : constrained U node ⊤ (h+1) →ₗ[ℝ] PolynomialModule ℝ (W ⧸ V) :=
    (PolynomialModule.map ℝ f).comp (constrained U node ⊤ (h+1)).subtype
  let M := polynomialLinearMatrix bP bQ F
  have heval (t : ℝ) : (eval t).comp F = V.mkQ.comp (ambientEval U node ⊤ (h+1) t) := by
    apply LinearMap.ext
    intro p
    change eval t (PolynomialModule.map ℝ f p.val) = f (eval t p.val)
    simpa using PolynomialModule.eval_map ℝ f p.val t
  have hrank (t : ℝ) : (M.map (Polynomial.eval t)).rank =
      finrank ℝ ((ambientEvalRange U node ⊤ (h+1) t).map V.mkQ) := by
    rw [polynomialLinearMatrix_rank, heval, LinearMap.range_comp]
    rfl
  let nodes := Finset.univ.image node
  have hoff (t : ℝ) (ht : t ∉ nodes) : (M.map (Polynomial.eval t)).rank ≤
      rankIncrement U node ⊤ h - rankIncrement U node V h := by
    rw [hrank]
    apply Nat.le_sub_of_add_le
    apply off_node_projected_rank U node V h t
    intro i hi
    exact ht (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
  have hnode := polynomial_rank_specialization M nodes
    (rankIncrement U node ⊤ h - rankIncrement U node V h) hoff (node j)
  rw [hrank] at hnode
  have hdisj : Disjoint (ambientEvalRange U node ⊤ (h+1) (node j)) (LinearMap.ker V.mkQ) := by
    rw [Submodule.ker_mkQ]
    exact hUV.mono_left (ambientEvalRange_at_node_le U node ⊤ (h+1) j)
  rw [finrank_map_of_disjoint V.mkQ _ hdisj] at hnode
  have hmono := Submodule.finrank_mono
    (ambientEvalRange_mono_coeff U node (show V ≤ ⊤ from le_top) (h+1) tstar)
  rw [finrank_ambientEvalRange_off_node U node V h tstar htstar,
    finrank_ambientEvalRange_off_node U node ⊤ h tstar htstar] at hmono
  omega

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RankMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem rank_deficiency_pow_dvd_det (M : Matrix κ κ ℝ[X]) (t : ℝ) :
    (X-C t)^(Fintype.card κ - ((evalRingHom t).mapMatrix M).rank) ∣ M.det := by
  classical
  let E : Matrix κ κ ℝ := (evalRingHom t).mapMatrix M
  obtain ⟨V, U, e, hV, hU, he⟩ := Matrix.exists_rank_normal_form E
  let T : Matrix κ κ ℝ[X] := C.mapMatrix V * M * C.mapMatrix U
  let emb : Fin (Fintype.card κ-E.rank) ↪ κ :=
    ⟨fun i => e.symm (Sum.inr i), fun i j h => Sum.inr_injective (e.symm.injective h)⟩
  let S : Finset κ := Finset.univ.map emb
  have hS : S.card = Fintype.card κ-E.rank := by simp [S]
  have evalC (A : Matrix κ κ ℝ) : (evalRingHom t).mapMatrix (C.mapMatrix A) = A := by
    funext i j
    exact eval_C
  have hT : (evalRingHom t).mapMatrix T = V * E * U := by
    simp only [T, map_mul, evalC]
    rfl
  have hz : ∀ j ∈ S, ∀ i, (T i j).eval t = 0 := by
    intro j hj i
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hj
    change ((evalRingHom t).mapMatrix T) i (emb a) = 0
    rw [hT, he]
    change (Matrix.fromBlocks 1 0 0 0) (e i) (e (e.symm (Sum.inr a))) = 0
    rw [Equiv.apply_symm_apply]
    cases e i <;> rfl
  have hd := pow_card_dvd_det_of_columns_vanish T t S hz
  rw [hS] at hd
  have hdet : T.det = C V.det * M.det * C U.det := by
    dsimp only [T]
    rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det]
  rw [hdet] at hd
  have hu : IsUnit (C U.det : ℝ[X]) := isUnit_C.mpr ((Matrix.isUnit_iff_isUnit_det U).mp hU)
  have hv : IsUnit (C V.det : ℝ[X]) := isUnit_C.mpr ((Matrix.isUnit_iff_isUnit_det V).mp hV)
  exact hv.dvd_mul_left.mp (hu.dvd_mul_right.mp hd)

theorem pow_dvd_det_of_rank_le (M : Matrix κ κ ℝ[X]) (t : ℝ) (q : ℕ)
    (hq : q + ((evalRingHom t).mapMatrix M).rank ≤ Fintype.card κ) :
    (X-C t)^q ∣ M.det := by
  apply dvd_trans _ (rank_deficiency_pow_dvd_det M t)
  exact pow_dvd_pow _ (by omega)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_StageDegreeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule Module Submodule
open scoped BigOperators
variable {W ι : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

theorem polynomial_columns_rank_le {κ ρ : Type*} [Fintype κ] [Fintype ρ] [DecidableEq ρ]
    (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)
    (b : Basis κ ℝ Z) (p : ρ → PolynomialModule ℝ Z) (k : ℕ)
    (hp : ∀ j, p j ∈ constrained U node Z k) (t : ℝ) :
    ((polynomialColumnMatrix b p).map (Polynomial.eval t)).rank ≤
      finrank ℝ (evaluationFiltration U node Z t k) := by
  let A := (polynomialColumnMatrix b p).map (Polynomial.eval t)
  have hcol : A.col = b.equivFun ∘ (fun j => eval t (p j)) := by
    funext j i
    exact polynomialColumnMatrix_eval b p t i j
  have hspan : span ℝ (Set.range (fun j => eval t (p j))) ≤ evaluationFiltration U node Z t k := by
    apply span_le.mpr
    rintro z ⟨j, rfl⟩
    exact ⟨⟨p j, hp j⟩, rfl⟩
  change A.rank ≤ _
  rw [Matrix.rank_eq_finrank_span_cols, hcol, Set.range_comp]
  calc
    _ ≤ finrank ℝ ((evaluationFiltration U node Z t k).map b.equivFun.toLinearMap) := by
      apply Submodule.finrank_mono
      apply span_le.mpr
      rintro z ⟨v, ⟨j, rfl⟩, rfl⟩
      exact ⟨eval t (p j), ⟨⟨p j, hp j⟩, rfl⟩, rfl⟩
    _ = _ := b.equivFun.finrank_map_eq _

theorem stage_degree_bound [Fintype ι] (U V : ι → Submodule ℝ W) (node : ι → ℝ)
    (hn : Function.Injective node) (hUV : ∀ i, Disjoint (U i) (V i))
    (tstar : ℝ) (htstar : ∀ i, node i ≠ tstar) (h : ℕ) :
    (∑ j, rankIncrement U node (V j) h) ≤
      ∑ e ∈ Finset.range (h+1), e * columnIncrement U node ⊤ tstar e := by
  let b := finBasis ℝ (⊤ : Submodule ℝ W)
  obtain ⟨p, d, r, hp, hr, hdt, hdeg⟩ := exists_adapted_minor U node ⊤ b tstar htstar h
  let M := (polynomialColumnMatrix b p).submatrix r id
  have hM : M.det ≠ 0 := by
    intro hz
    apply hdt
    change M.det.eval tstar = 0
    rw [hz, Polynomial.eval_zero]
  have hcard : Fintype.card (Fin (finrank ℝ (evaluationFiltration U node ⊤ tstar (h+1)))) =
      rankIncrement U node ⊤ h := by
    rw [Fintype.card_fin]
    exact finrank_eval_range U node ⊤ h tstar htstar
  have hp' : ∀ j, p j ∈ constrained U node ⊤ (h+1) := by
    intro j
    exact ⟨bounded_mono (hp j).1.1 (Nat.add_le_add_right (hp j).2 1), (hp j).1.2⟩
  have hfactor : ∀ j, (Polynomial.X-Polynomial.C (node j))^(rankIncrement U node (V j) h) ∣ M.det := by
    intro j
    have hnode := node_rank_loss U node (V j) j (hUV j) h tstar htstar
    rw [finrank_ambientEvalRange] at hnode
    have hcols := polynomial_columns_rank_le U node ⊤ b p (h+1) hp' (node j)
    have hminor := Matrix.rank_submatrix_le
      ((polynomialColumnMatrix b p).map (Polynomial.eval (node j))) r id
    have hbound : ((Polynomial.evalRingHom (node j)).mapMatrix M).rank ≤
        finrank ℝ (evaluationFiltration U node ⊤ (node j) (h+1)) :=
      hminor.trans hcols
    apply pow_dvd_det_of_rank_le
    rw [hcard]
    omega
  exact (sum_multiplicities_le_natDegree node hn (fun j => rankIncrement U node (V j) h)
    M.det hM hfactor).trans hdeg

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SubspaceIntersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module Submodule
open scoped BigOperators
variable {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

theorem subspace_intersection_bound (m : ℕ) (U V : Fin m → Submodule ℝ W)
    (hUV : ∀ i, Disjoint (U i) (V i)) :
    (∑ i, ∑ j, finrank ℝ ↥(U i ⊓ V j)) ≤ (m*m/4) * finrank ℝ W := by
  let node : Fin m → ℝ := fun i => (i.val : ℝ)
  have hn : Function.Injective node := by
    intro i j hij
    apply Fin.ext
    dsimp only [node] at hij
    exact_mod_cast hij
  have ht : ∀ i, node i ≠ (-1 : ℝ) := by
    intro i
    have hnonneg : (0 : ℝ) ≤ node i := Nat.cast_nonneg i.val
    linarith
  let ell := columnIncrement U node ⊤ (-1)
  have hsum : (∑ i, ∑ j, finrank ℝ ↥(U i ⊓ V j)) =
      ∑ h ∈ Finset.range m, ∑ j, rankIncrement U node (V j) h := by
    rw [Finset.sum_comm]
    calc
      (∑ j, ∑ i, finrank ℝ ↥(U i ⊓ V j)) =
          ∑ j, ∑ h ∈ Finset.range m, rankIncrement U node (V j) h := by
        apply Finset.sum_congr rfl
        intro j hj
        simpa only [Fintype.card_fin] using (interpolation_identity U node (V j) hn).symm
      _ = _ := Finset.sum_comm
  have hell : (∑ e ∈ Finset.range m, ell e) ≤ finrank ℝ W := by
    change (∑ e ∈ Finset.range m, columnIncrement U node ⊤ (-1) e) ≤ _
    rw [sum_columnIncrement]
    have he := Submodule.finrank_le (evaluationFiltration U node ⊤ (-1) m)
    simpa using he
  rw [hsum]
  calc
    (∑ h ∈ Finset.range m, ∑ j, rankIncrement U node (V j) h) ≤
        ∑ h ∈ Finset.range m, ∑ e ∈ Finset.range (h+1), e * ell e := by
      apply Finset.sum_le_sum
      intro h hh
      exact stage_degree_bound U V node hn hUV (-1) ht h
    _ ≤ (m*m/4) * finrank ℝ W := total_degree_cost_le ell m (finrank ℝ W) hell

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_MatrixRankSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module Submodule
open scoped BigOperators

theorem matrix_rank_sum_bound (m d : ℕ)
    (X Y : Fin m → Matrix (Fin d) (Fin d) ℝ)
    (hdiag : ∀ i, IsUnit (X i-Y i)) :
    2 * axisPairs m * d ≤ offDiagonalRankSum m d X Y := by
  let U := fun i => (X i).mulVecLin.graph
  let V := fun i => (Y i).mulVecLin.graph
  have hUV : ∀ i, Disjoint (U i) (V i) := fun i => matrix_graph_disjoint d (X i) (Y i) (hdiag i)
  have hsub := subspace_intersection_bound m U V hUV
  have hdim : finrank ℝ ((Fin d → ℝ) × (Fin d → ℝ)) = 2*d := by
    simp [Module.finrank_prod, two_mul]
  rw [hdim] at hsub
  have htotal : (∑ i, ∑ j, finrank ℝ ↥(U i ⊓ V j)) +
      (∑ i, ∑ j, (X i-Y j).rank) = m*m*d := by
    dsimp only [U, V]
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, matrix_graph_finrank_add_rank]
    simp [Nat.mul_assoc]
  have hremove : offDiagonalRankSum m d X Y + m*d = ∑ i, ∑ j, (X i-Y j).rank := by
    have hdiagrank : ∀ i, (X i-Y i).rank = d := by
      intro i
      simpa using Matrix.rank_of_isUnit (X i-Y i) (hdiag i)
    unfold offDiagonalRankSum
    have hm : m*d = ∑ i : Fin m, d := by simp
    rw [hm, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [hdiagrank i] using
      Finset.sum_erase_add Finset.univ (fun j => (X i-Y j).rank) (Finset.mem_univ i)
  have hfloor := congrArg (fun a : ℕ => a*d) (diagonal_floor_identity m)
  nlinarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_IndexedMatrixRankSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem matrix_rank_sum_bound_indexed {κ : Type*} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (X Y : Fin m → Matrix κ κ ℝ) (hdiag : ∀ i, IsUnit (X i-Y i)) :
    2*axisPairs m*Fintype.card κ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, (X i-Y j).rank := by
  let e := Fintype.equivFin κ
  let R := Matrix.reindexRingEquiv ℝ e
  have hunit : ∀ i, IsUnit (R (X i)-R (Y i)) := by
    intro i
    rw [← map_sub]
    exact (hdiag i).map R.toMonoidHom
  have hrank (i j : Fin m) : (R (X i)-R (Y j)).rank=(X i-Y j).rank := by
    rw [← map_sub]
    exact Matrix.rank_reindex e e (X i-Y j)
  have h := matrix_rank_sum_bound m (Fintype.card κ) (fun i => R (X i)) (fun i => R (Y i)) hunit
  simpa only [offDiagonalRankSum,hrank] using h

theorem matrix_rank_sum_bound_product (m s : ℕ)
    (X Y : Fin m → Matrix (Fin s × Fin s) (Fin s × Fin s) ℝ)
    (hdiag : ∀ i, IsUnit (X i-Y i)) :
    2*axisPairs m*(s*s) ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, (X i-Y j).rank := by
  simpa only [Fintype.card_prod,Fintype.card_fin] using matrix_rank_sum_bound_indexed m X Y hdiag

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

theorem offDiagonal_detector (s : ℕ) (node : Fin n → ℝ) (i k : Fin m) (hik : i ≠ k) :
    rankDetector s node (edgeBlock C.cycleIntersectionMatrix i k)=
      rankDetector s node (V.intersectionBlock i k) := by
  rw [C.cycleIntersectionMatrix_offDiagonal_block i k hik,map_add,rankDetector_diagonal,add_zero]

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OddNormalizedLowerBound
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

theorem odd_normalized_crossing_lower_bound_oai (C : TruncatedSpokeCoordinates V) (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (s : ℕ) (hs : 0 < s) (hcard : n=2*s+1) (hm : 0 < m) :
    axisPairs m*(s*s) ≤ crossingCount D := by
  let node : Fin n → ℝ := fun p => p.val
  have hnode : Function.Injective node := by
    intro p q hpq
    apply Fin.ext
    change (p.val : ℝ)=(q.val : ℝ) at hpq
    exact_mod_cast hpq
  let i₀ : Fin m := ⟨0,hm⟩
  let H := fun i k : Fin m => rankDetector s node (edgeBlock C.cycleIntersectionMatrix i k)
  let X := fun i : Fin m => H i i₀
  let Y := fun k : Fin m => H i₀ i₀-H i₀ k
  have hH (i k : Fin m) : H i k=X i-Y k := by
    have hh := C.additive_detector_relation hnorm hstraight htrans s node hnode hcard i k i₀
    change H i k-H i i₀-H i₀ k+H i₀ i₀=0 at hh
    dsimp only [X,Y]
    calc
      H i k=(H i k-H i i₀-H i₀ k+H i₀ i₀)+(H i i₀-(H i₀ i₀-H i₀ k)) := by abel
      _ = _ := by rw [hh,zero_add]
  have hdiag : ∀ i, IsUnit (X i-Y i) := by
    intro i
    rw [← hH]
    exact C.diagonal_detector_isUnit hnorm s hs node hnode hcard i
  have hlower := matrix_rank_sum_bound_product m s X Y hdiag
  have hsum : (∑ i : Fin m, ∑ k ∈ Finset.univ.erase i, (X i-Y k).rank)=
      ∑ i : Fin m, ∑ k ∈ Finset.univ.erase i, (rankDetector s node (V.intersectionBlock i k)).rank := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    rw [← hH]
    exact congrArg Matrix.rank (C.offDiagonal_detector s node i k (Ne.symm (Finset.mem_erase.mp hk).1))
  rw [hsum] at hlower
  have hupper := V.ordered_detector_rank_le_twice_crossings hnorm s node
  have hh := hlower.trans hupper
  nlinarith

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

theorem solution : type_of% @OAI.Zarankiewicz.TruncatedSpokeCoordinates.odd_normalized_crossing_lower_bound_oai := @OAI.Zarankiewicz.TruncatedSpokeCoordinates.odd_normalized_crossing_lower_bound_oai
