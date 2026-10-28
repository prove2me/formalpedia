-- Prove2me | solution 1 for OAI.Zarankiewicz.TruncatedSpokeCoordinates.diagonal_detector_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T13:23:29.729881+00:00
-- url     : https://prove2.me/submissions/76483ec4-fce6-4faa-9f43-b608ac464ae7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr003
import Definitions.Def_OAIB3Zr004

section
-- module Solutions.OAIB3_Zar.Crossing_Bivariate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule

theorem flattenBi_apply (p : BiPoly) (a b : ℕ) : flattenBi p (a,b) = biCoeff p a b := rfl

theorem biCoeff_swap (p : BiPoly) (a b : ℕ) : biCoeff (swapBi p) a b = biCoeff p b a := by
  rw [← flattenBi_apply]
  change flattenBi (flattenBi.symm _) (a,b) = _
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.mapDomain_equiv_apply (flattenBi p) (a,b)

theorem bi_ext {p q : BiPoly} (h : ∀ a b, biCoeff p a b = biCoeff q a b) : p = q := by
  apply PolynomialModule.ext
  apply Finsupp.ext
  intro a
  apply PolynomialModule.ext
  apply Finsupp.ext
  exact h a

theorem swapBi_swapBi (p : BiPoly) : swapBi (swapBi p) = p := by
  apply bi_ext
  intro a b
  rw [biCoeff_swap, biCoeff_swap]

theorem swapBi_single (a b : ℕ) (c : ℝ) :
    swapBi (single ℝ a (single ℝ b c)) = single ℝ b (single ℝ a c) := by
  apply bi_ext
  intro i j
  rw [biCoeff_swap]
  simp [biCoeff, Finsupp.single_apply]
  split_ifs <;> simp_all

theorem biEval_swap (p : BiPoly) (u v : ℝ) : biEval u v (swapBi p) = biEval v u p := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single a q =>
    induction q using PolynomialModule.induction_linear with
    | zero => simp
    | add p q hp hq => simp only [single_add, map_add, hp, hq]
    | single b c =>
      rw [swapBi_single]
      simp [biEval, eval_single, smul_eq_mul]
      ring

theorem biBounded_swap {r s : ℕ} {p : BiPoly} (hp : BiBounded r s p) :
    BiBounded s r (swapBi p) := by
  constructor
  · intro a ha
    apply PolynomialModule.ext
    apply Finsupp.ext
    intro b
    change biCoeff (swapBi p) a b = 0
    rw [biCoeff_swap]
    exact hp.2 b a ha
  · intro a b hb
    change biCoeff (swapBi p) a b = 0
    rw [biCoeff_swap]
    simp [biCoeff, hp.1 b hb]

theorem coefficients_of_mulRoot {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Z : Submodule ℝ W) (t : ℝ) (k : ℕ) (q : PolynomialModule ℝ W)
    (hq : Bounded k q) (hc : ∀ n, (mulRoot t q).coeff n ∈ Z) :
    ∀ n, q.coeff n ∈ Z := by
  have aux : ∀ d n, k-n = d → q.coeff n ∈ Z := by
    intro d
    induction d with
    | zero =>
      intro n hn
      rw [hq n (by omega)]
      exact Z.zero_mem
    | succ d ih =>
      intro n hn
      have hh := Z.add_mem (hc (n+1)) (Z.smul_mem t (ih (n+1) (by omega)))
      simpa only [mulRoot_coeff_succ, sub_add_cancel] using hh
  intro n
  exact aux (k-n) n rfl

theorem bi_factor_row (r s : ℕ) (p : BiPoly) (hp : BiBounded (r+1) s p)
    (t : ℝ) (hz : eval t p = 0) :
    ∃ q : BiPoly, BiBounded r s q ∧ mulRoot t q = p := by
  obtain ⟨q, hq, he⟩ := exists_mulRoot_of_eval_zero t r p hp.1 hz
  refine ⟨q, ⟨hq, ?_⟩, he⟩
  apply coefficients_of_mulRoot (boundedSpace s) t r q hq
  intro n
  rw [he]
  exact hp.2 n

theorem biEval_mulRoot (t u v : ℝ) (p : BiPoly) :
    biEval u v (mulRoot t p) = (u-t) * biEval u v p := by
  change eval v (eval u (mulRoot t p)) = _
  rw [eval_mulRoot, _root_.map_smul]
  rfl

theorem bounded_eval_outer {r s : ℕ} {p : BiPoly} (hp : BiBounded r s p) (u : ℝ) :
    Bounded s (eval u p) := by
  change eval u p ∈ boundedSpace s
  change p.coeff.sum (fun a c => u^a • c) ∈ boundedSpace s
  apply Submodule.sum_mem
  intro a ha
  exact (boundedSpace s).smul_mem (u^a) (hp.2 a)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TwoTriangleIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz
open Finset

theorem triangleRelabel_injective_on (s : ℕ) :
    Set.InjOn (triangleRelabel s) (Set.Icc 1 (2*s-1)) := by
  intro p hp q hq he
  simp only [Set.mem_Icc] at hp hq
  unfold triangleRelabel at he
  split_ifs at he <;> omega

theorem triangleRelabel_range (s k : ℕ) (hk : k ∈ Icc 1 (2*s-1)) :
    triangleRelabel s k ∈ Icc 1 (2*s+1) ∧
      triangleRelabel s k ≠ s+1 ∧ triangleRelabel s k ≠ 1 := by
  simp only [mem_Icc] at hk ⊢
  unfold triangleRelabel
  split_ifs <;> omega

theorem relabel_twoTriangle (s : ℕ) (hs : 1 ≤ s) (p q : ℕ)
    (hpq : (p,q) ∈ twoTriangle (s-1)) :
    (triangleRelabel s q, triangleRelabel s p) ∈ twoTriangle s ∧
      triangleRelabel s q ≠ s+1 ∧ triangleRelabel s p ≠ 1 := by
  rw [mem_twoTriangle] at hpq ⊢
  unfold triangleRelabel
  split_ifs <;> omega

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TwoTriangleUnisolvence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
open Finset

theorem eq_zero_of_roots_injOn {W : Type*} [AddCommGroup W] [Module ℝ W]
    (node : ℕ → ℝ) (S : Finset ℕ) (hn : Set.InjOn node (S : Set ℕ))
    (p : PolynomialModule ℝ W) (hp : Bounded S.card p)
    (he : ∀ i ∈ S, eval (node i) p = 0) : p = 0 := by
  let x : S → ℝ := fun i => node i.val
  have hx : Function.Injective x := by
    intro i j hij
    exact Subtype.ext (hn i.property j.property hij)
  apply eq_zero_of_node_roots x hx Finset.univ p
  · simpa using hp
  · intro i hi
    exact he i.val i.property

theorem twoTriangle_unisolvent (s : ℕ) (node : ℕ → ℝ)
    (hn : Set.InjOn node (Set.Icc 1 (2*s+1))) (p : BiPoly)
    (hp : BiBounded s s p)
    (hv : ∀ a b, (a,b) ∈ twoTriangle s → biEval (node a) (node b) p = 0) : p = 0 := by
  induction s generalizing node p with
  | zero => exact (bounded_zero_iff p).mp hp.1
  | succ k ih =>
    have node_ne : ∀ a b, a ∈ Icc 1 (2*(k+1)+1) → b ∈ Icc 1 (2*(k+1)+1) →
        a ≠ b → node a ≠ node b := by
      intro a b ha hb hab he
      exact hab (hn (by simpa only [mem_Icc, Set.mem_Icc] using ha)
        (by simpa only [mem_Icc, Set.mem_Icc] using hb) he)

    have hrow : eval (node (k+2)) p = 0 := by
      apply eq_zero_of_roots_injOn node (Icc 1 (k+1))
      · intro a ha b hb he
        apply hn _ _ he <;> simp only [mem_coe, mem_Icc, Set.mem_Icc] at * <;> omega
      · simpa using bounded_eval_outer hp (node (k+2))
      · intro q hq
        apply hv (k+2) q
        rw [mem_twoTriangle]
        simp only [mem_Icc] at hq
        left
        omega
    obtain ⟨p₁, hp₁, he₁⟩ := bi_factor_row k (k+1) p hp (node (k+2)) hrow

    have hcol : eval (node 1) (swapBi p₁) = 0 := by
      apply eq_zero_of_roots_injOn node (Icc 2 (k+1))
      · intro a ha b hb he
        apply hn _ _ he <;> simp only [mem_coe, mem_Icc, Set.mem_Icc] at * <;> omega
      · simpa using bounded_eval_outer (biBounded_swap hp₁) (node 1)
      · intro a ha
        change biEval (node 1) (node a) (swapBi p₁) = 0
        rw [biEval_swap]
        have hpa : biEval (node a) (node 1) p = 0 := by
          apply hv
          rw [mem_twoTriangle]
          simp only [mem_Icc] at ha
          left
          omega
        rw [← he₁, biEval_mulRoot] at hpa
        apply (mul_eq_zero.mp hpa).resolve_left
        apply sub_ne_zero.mpr
        apply node_ne a (k+2) <;> simp only [mem_Icc] at * <;> omega
    obtain ⟨r, hr, her⟩ := bi_factor_row k k (swapBi p₁) (biBounded_swap hp₁) (node 1) hcol

    let y : ℕ → ℝ := fun i => node (triangleRelabel (k+1) i)
    have hyrange : ∀ a, a ∈ Icc 1 (2*k+1) →
        triangleRelabel (k+1) a ∈ Icc 1 (2*(k+1)+1) ∧
          triangleRelabel (k+1) a ≠ k+2 ∧ triangleRelabel (k+1) a ≠ 1 := by
      intro a ha
      simpa only [show k+1+1 = k+2 from rfl] using
        triangleRelabel_range (k+1) a (by simp only [mem_Icc] at *; omega)
    have hyn : Set.InjOn y (Set.Icc 1 (2*k+1)) := by
      intro a ha b hb he
      have ha' : a ∈ Icc 1 (2*k+1) := by simpa only [mem_Icc, Set.mem_Icc] using ha
      have hb' : b ∈ Icc 1 (2*k+1) := by simpa only [mem_Icc, Set.mem_Icc] using hb
      apply triangleRelabel_injective_on (k+1)
      · simp only [Set.mem_Icc] at *
        omega
      · simp only [Set.mem_Icc] at *
        omega
      · exact hn (by simpa only [Set.mem_Icc, mem_Icc] using (hyrange a ha').1)
          (by simpa only [Set.mem_Icc, mem_Icc] using (hyrange b hb').1) he
    have hrv : ∀ a b, (a,b) ∈ twoTriangle k → biEval (y a) (y b) r = 0 := by
      intro a b hab
      have ha : a ∈ Icc 1 (2*k+1) := by
        rw [mem_twoTriangle] at hab
        simp only [mem_Icc]
        omega
      have hb : b ∈ Icc 1 (2*k+1) := by
        rw [mem_twoTriangle] at hab
        simp only [mem_Icc]
        omega
      have hpattern := relabel_twoTriangle (k+1) (by omega) a b (by simpa using hab)
      have hval := hv (triangleRelabel (k+1) b) (triangleRelabel (k+1) a) hpattern.1
      rw [← he₁, biEval_mulRoot] at hval
      have hfirst : node (triangleRelabel (k+1) b) - node (k+2) ≠ 0 :=
        sub_ne_zero.mpr (node_ne _ _ (hyrange b hb).1 (by simp) (hyrange b hb).2.1)
      have hp₁val := (mul_eq_zero.mp hval).resolve_left hfirst
      have hswap : p₁ = swapBi (mulRoot (node 1) r) := by rw [her, swapBi_swapBi]
      rw [hswap, biEval_swap, biEval_mulRoot] at hp₁val
      apply (mul_eq_zero.mp hp₁val).resolve_left
      exact sub_ne_zero.mpr (node_ne _ _ (hyrange a ha).1 (by simp) (hyrange a ha).2.2)
    have hr0 := ih y hyn r hr hrv
    have hp₁0 : p₁ = 0 := by
      apply swapBi.injective
      rw [← her, hr0]
      simp [mulRoot]
    rw [← he₁, hp₁0]
    simp [mulRoot]

theorem twoTriangle_evaluation_injective (s : ℕ) (node : ℕ → ℝ)
    (hn : Set.InjOn node (Set.Icc 1 (2*s+1))) (p q : BiPoly)
    (hp : BiBounded s s p) (hq : BiBounded s s q)
    (he : ∀ a b, (a,b) ∈ twoTriangle s → biEval (node a) (node b) p = biEval (node a) (node b) q) :
    p = q := by
  apply sub_eq_zero.mp
  apply twoTriangle_unisolvent s node hn (p-q)
  · refine ⟨bounded_sub hp.1 hq.1, ?_⟩
    intro a
    exact bounded_sub (hp.2 a) (hq.2 a)
  · intro a b hab
    rw [map_sub, he a b hab, sub_self]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_BivariateCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule Module
open scoped BigOperators

theorem biCoeff_biOfCoeffs (s : ℕ) (c : BiExponent s → ℝ) (a b : Fin s) :
    biCoeff (biOfCoeffs s c) a.val b.val = c (a,b) := by
  simp [biCoeff, biOfCoeffs, coeff_sum, Finsupp.finsetSum_apply, Finsupp.single_apply, Fin.val_inj]

theorem biOfCoeffs_injective (s : ℕ) : Function.Injective (biOfCoeffs s) := by
  intro c d h
  funext ab
  have hh := congrArg (fun p => biCoeff p ab.1.val ab.2.val) h
  simpa only [biCoeff_biOfCoeffs] using hh

theorem biOfCoeffs_bounded (s : ℕ) (c : BiExponent s → ℝ) :
    BiBounded s s (biOfCoeffs s c) := by
  constructor
  · apply bounded_sum
    intro a ha
    exact bounded_single a.isLt _
  · intro n k hk
    simp only [biOfCoeffs, coeff_sum, Finsupp.finsetSum_apply, coeff_single,
      Finsupp.single_apply]
    apply Finset.sum_eq_zero
    intro a ha
    split_ifs with hna
    · simp only [coeff_sum, Finsupp.finsetSum_apply, coeff_single, Finsupp.single_apply]
      apply Finset.sum_eq_zero
      intro b hb
      rw [ite_eq_right (by omega)]
    · rfl

theorem biEval_biOfCoeffs (s : ℕ) (c : BiExponent s → ℝ) (u v : ℝ) :
    biEval u v (biOfCoeffs s c) = ∑ a : Fin s, ∑ b : Fin s,
      (u^a.val * v^b.val) * c (a,b) := by
  simp [biOfCoeffs, biEval, eval_single, smul_eq_mul, Finset.mul_sum, mul_assoc]

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

theorem pairCrossings_self (D : AdmissibleDrawing m n) (e : BipartiteEdge m n) :
    pairCrossings D e e = ∅ := by
  simp [pairCrossings]

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

theorem signedIntersection_adjacent_zero {A : AdmissibleDrawing m n}
    (V : VertexTruncation A.toContinuousDrawing) (hnorm : NoAdjacentCrossings A)
    (e f : BipartiteEdge m n) (hadj : e.1=f.1 ∨ e.2=f.2) : V.signedIntersection e f=0 :=
  V.signedIntersection_zero_of_pairCrossings_empty e f (pairCrossings_eq_empty_of_adjacent A hnorm e f hadj)

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

theorem matrix_rank_eq_zero_iff
    {κ ρ : Type*} [Fintype κ] [Fintype ρ] [DecidableEq ρ]
    (A : Matrix κ ρ ℝ) : A.rank = 0 ↔ A = 0 := by
  constructor
  · intro ha
    have hf : A.mulVecLin = 0 :=
      LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp ha)
    funext i j
    have hh := congrArg (fun f : (ρ → ℝ) →ₗ[ℝ] (κ → ℝ) => f (Pi.single j 1) i) hf
    simpa [Matrix.mulVec_single] using hh
  · rintro rfl
    exact Matrix.rank_zero

theorem matrix_rank_smul_le
    {κ ρ : Type*} [Fintype κ] [Fintype ρ] [DecidableEq ρ]
    (c : ℝ) (A : Matrix κ ρ ℝ) : (c • A).rank ≤ A.rank := by
  by_cases hc : c = 0
  · simp [hc, Matrix.rank_zero]
  · rw [Matrix.rank_smul_of_mem_nonZeroDivisors A (mem_nonZeroDivisors_of_ne_zero hc)]

end Zarankiewicz

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

theorem derivativeAtNode_ne_zero (node : ι → ℝ) (hn : Function.Injective node) (i : ι) :
    derivativeAtNode node i ≠ 0 := by
  rw [derivativeAtNode_eq_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro hij
  exact (Finset.mem_erase.mp hj).1 (hn hij).symm

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
-- module Solutions.OAIB3_Zar.Crossing_TwoTriangleBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module
open scoped BigOperators

theorem triangleMatrix_eval (s : ℕ) (node : ℕ → ℝ) (c : BiExponent s → ℝ)
    (j : BiExponent s) :
    (triangleMatrix s node).transpose.mulVec c j =
      biEval (node (triangleCoordEquiv s j).val.1) (node (triangleCoordEquiv s j).val.2)
        (biOfCoeffs s c) := by
  rw [biEval_biOfCoeffs]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, triangleMatrix,
    monomialVector, Fintype.sum_prod_type]

theorem triangleMatrix_isUnit (s : ℕ) (node : ℕ → ℝ)
    (hn : Set.InjOn node (Set.Icc 1 (2*s+1))) : IsUnit (triangleMatrix s node) := by
  rw [← Matrix.isUnit_transpose, ← Matrix.mulVec_injective_iff_isUnit]
  intro c d hcd
  apply biOfCoeffs_injective s
  apply twoTriangle_evaluation_injective s node hn (biOfCoeffs s c) (biOfCoeffs s d)
    (biOfCoeffs_bounded s c) (biOfCoeffs_bounded s d)
  intro p q hpq
  let j := (triangleCoordEquiv s).symm ⟨(p,q), hpq⟩
  have hh := congrFun hcd j
  rw [triangleMatrix_eval, triangleMatrix_eval] at hh
  simpa only [j, Equiv.apply_symm_apply] using hh

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

theorem detectorWeight_ne_zero (node : ι → ℝ) (hn : Function.Injective node)
    {p q : ι} (hpq : p ≠ q) : detectorWeight node p q ≠ 0 := by
  exact div_ne_zero (sub_ne_zero.mpr (hn.ne hpq))
    (mul_ne_zero (derivativeAtNode_ne_zero node hn p) (derivativeAtNode_ne_zero node hn q))

theorem detectorAtom_entry
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (node : ι → ℝ) (p q : ι) (ab cd : BiExponent s) :
    detectorAtom s node p q ab cd =
      (node p-node q) * node p^(ab.1.val+cd.1.val) * node q^(ab.2.val+cd.2.val) /
        (derivativeAtNode node p * derivativeAtNode node q) := by
  simp only [detectorAtom, detectorWeight, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, detectorVector, pow_add]
  ring

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

theorem detectorAtom_rank_one (s : ℕ) (hs : 0 < s) (node : ι → ℝ)
    (hn : Function.Injective node) {p q : ι} (hpq : p ≠ q) :
    (detectorAtom s node p q).rank = 1 := by
  have hw := detectorWeight_ne_zero node hn hpq
  have hne : detectorAtom s node p q ≠ 0 := by
    intro hz
    have he := congrArg (fun A : Matrix (BiExponent s) (BiExponent s) ℝ =>
      A (⟨0,hs⟩,⟨0,hs⟩) (⟨0,hs⟩,⟨0,hs⟩)) hz
    apply hw
    simpa [detectorAtom, detectorVector, Matrix.vecMulVec_apply] using he
  have hr0 := (matrix_rank_eq_zero_iff (detectorAtom s node p q)).not.mpr hne
  have hr1 := detectorAtom_rank_le_one s node p q
  omega

theorem rankDetector_single (s : ℕ) (node : ι → ℝ) (p q : ι) (c : ℝ) :
    rankDetector s node (Matrix.single p q c) = c • detectorAtom s node p q := by
  change (∑ i, ∑ j, Matrix.single p q c i j • detectorAtom s node i j) = _
  simp [Matrix.single_apply, ite_and]

end Zarankiewicz

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

theorem cycleIntersectionMatrix_diagonal_block (hnorm : NoAdjacentCrossings D) (i : Fin m) :
    edgeBlock C.cycleIntersectionMatrix i i=C.leftHalfOrder i := by
  ext p q
  rw [edgeBlock,C.cycleIntersectionMatrix_entry,V.signedIntersection_adjacent_zero hnorm (i,p) (i,q) (Or.inl rfl),ite_eq_left rfl]
  have hz : C.rightHalfOrder p i i=0 := by simp [rightHalfOrder,orderSign]
  rw [hz]
  simp

end Zarankiewicz.TruncatedSpokeCoordinates

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
-- module Solutions.OAIB3_Zar.Crossing_DetectorRelabeling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem nodePolynomial_equiv
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (node : ι → ℝ) (e : κ ≃ ι) :
    nodePolynomial (node ∘ e) = nodePolynomial node := by
  exact e.prod_comp (fun i => Polynomial.X-Polynomial.C (node i))

theorem derivativeAtNode_equiv (node : ι → ℝ) (e : κ ≃ ι) (p : κ) :
    derivativeAtNode (node ∘ e) p = derivativeAtNode node (e p) := by
  simp only [derivativeAtNode, nodePolynomial_equiv, Function.comp_apply]

theorem detectorAtom_equiv (s : ℕ) (node : ι → ℝ) (e : κ ≃ ι) (p q : κ) :
    detectorAtom s (node ∘ e) p q = detectorAtom s node (e p) (e q) := by
  unfold detectorAtom detectorWeight
  rw [derivativeAtNode_equiv, derivativeAtNode_equiv]
  rfl

theorem rankDetector_equiv (s : ℕ) (node : ι → ℝ) (e : κ ≃ ι) (H : Matrix ι ι ℝ) :
    rankDetector s (node ∘ e) (H.submatrix e e) = rankDetector s node H := by
  change (∑ p, ∑ q, H (e p) (e q) • detectorAtom s (node ∘ e) p q) = _
  simp only [detectorAtom_equiv]
  calc
    _ = ∑ p : κ, ∑ q : ι, H (e p) q • detectorAtom s node (e p) q := by
      apply Finset.sum_congr rfl
      intro p hp
      exact e.sum_comp (fun q => H (e p) q • detectorAtom s node (e p) q)
    _ = _ := e.sum_comp (fun p => ∑ q, H p q • detectorAtom s node p q)

theorem halfOrderMatrix_orderIso
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [LinearOrder ι] [LinearOrder κ] (e : κ ≃o ι) :
    (halfOrderMatrix ι).submatrix e e = halfOrderMatrix κ := by
  funext p q
  simp [halfOrderMatrix]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OrderedNodeIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem extendOrderedNode_injOn (s : ℕ) (node : OrderedNode s → ℝ)
    (hn : Function.Injective node) : Set.InjOn (extendOrderedNode s node) (Set.Icc 1 (2*s+1)) := by
  intro p hp q hq he
  have hp' : p ∈ Finset.Icc 1 (2*s+1) := Finset.mem_Icc.mpr hp
  have hq' : q ∈ Finset.Icc 1 (2*s+1) := Finset.mem_Icc.mpr hq
  simp only [extendOrderedNode, dite_eq_left hp', dite_eq_left hq'] at he
  exact congrArg Subtype.val (hn he)

theorem triangleMatrix_ordered_entry (s : ℕ) (node : OrderedNode s → ℝ)
    (ab j : BiExponent s) :
    triangleMatrix s (extendOrderedNode s node) ab j =
      node (triangleNodePair s (triangleCoordEquiv s j)).1 ^ ab.1.val *
      node (triangleNodePair s (triangleCoordEquiv s j)).2 ^ ab.2.val := by
  unfold triangleMatrix monomialVector
  change extendOrderedNode s node (triangleNodePair s (triangleCoordEquiv s j)).1.val ^ ab.1.val *
    extendOrderedNode s node (triangleNodePair s (triangleCoordEquiv s j)).2.val ^ ab.2.val = _
  rw [extendOrderedNode_apply, extendOrderedNode_apply]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_HalfOrderReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

variable {ι : Type*}

theorem halfOrder_decomposition [LinearOrder ι] :
    halfOrderMatrix ι = Matrix.of (fun (_ _ : ι) => (1/2 : ℝ)) - strictLowerMatrix ι -
      Matrix.diagonal (fun _ => (1/2 : ℝ)) := by
  funext p q
  rcases lt_trichotomy p q with h | rfl | h
  · norm_num [halfOrderMatrix, strictLowerMatrix, Matrix.diagonal_apply, Matrix.of_apply, ne_of_lt h,
      h, not_lt.mpr h.le]
  · norm_num [halfOrderMatrix, strictLowerMatrix, Matrix.diagonal_apply]
  · norm_num [halfOrderMatrix, strictLowerMatrix, Matrix.diagonal_apply, Matrix.of_apply, (ne_of_lt h).symm,
      h, not_lt.mpr h.le]

theorem lower_triangle_decomposition (s : ℕ) :
    strictLowerMatrix (OrderedNode s) = Matrix.of (fun p q => triangleCoefficient s p q) +
      Matrix.of (fun p (_ : OrderedNode s) => rowCut s p) + Matrix.diagonal (fun p => -rowCut s p) := by
  funext p q
  rcases lt_trichotomy p q with h | rfl | h
  · simp [strictLowerMatrix, triangleCoefficient, rowCut, Matrix.of_apply,
      h, not_lt.mpr h.le, ne_of_lt h]
    split_ifs <;> norm_num <;> omega
  · simp [strictLowerMatrix, triangleCoefficient, rowCut]
  · simp [strictLowerMatrix, triangleCoefficient, rowCut, Matrix.of_apply,
      h, not_lt.mpr h.le, (ne_of_lt h).symm]
    split_ifs <;> norm_num <;> omega

theorem triangleCoefficient_nat_nonzero (s p q : ℕ) (hp : 1 ≤ p ∧ p ≤ 2*s+1)
    (hq : 1 ≤ q ∧ q ≤ 2*s+1) :
    (if p ≤ s+1 then (if q < p then (1 : ℝ) else 0)
      else (if p < q then -1 else 0)) ≠ 0 ↔ (p,q) ∈ twoTriangle s := by
  obtain ⟨hp_lower, hp_upper⟩ := hp
  rw [mem_twoTriangle]
  split_ifs <;> norm_num <;> omega

theorem triangleCoefficient_ne_zero_iff (s : ℕ) (p q : OrderedNode s) :
    triangleCoefficient s p q ≠ 0 ↔ (p.val,q.val) ∈ twoTriangle s :=
  triangleCoefficient_nat_nonzero s p.val q.val (Finset.mem_Icc.mp p.property)
    (Finset.mem_Icc.mp q.property)

theorem rankDetector_halfOrder_reduction (s : ℕ) (node : OrderedNode s → ℝ)
    (hn : Function.Injective node) :
    rankDetector s node (halfOrderMatrix (OrderedNode s)) =
      -rankDetector s node (Matrix.of (fun p q => triangleCoefficient s p q)) := by
  have hrow := rankDetector_additive s node hn (card_orderedNode s) (rowCut s) (fun _ => 0)
  simp only [add_zero] at hrow
  change rankDetector s node (Matrix.of (fun p (_ : OrderedNode s) => rowCut s p)) = 0 at hrow
  have hconst := rankDetector_additive s node hn (card_orderedNode s) (fun _ => (1/2 : ℝ)) (fun _ => 0)
  simp only [add_zero] at hconst
  change rankDetector s node (Matrix.of (fun (_ _ : OrderedNode s) => (1/2 : ℝ))) = 0 at hconst
  have hlower : rankDetector s node (strictLowerMatrix (OrderedNode s)) =
      rankDetector s node (Matrix.of (fun p q => triangleCoefficient s p q)) := by
    rw [lower_triangle_decomposition, map_add, map_add, hrow, rankDetector_diagonal, add_zero, add_zero]
  rw [halfOrder_decomposition, map_sub, map_sub, hconst, hlower, rankDetector_diagonal,
    zero_sub, sub_zero]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_WeightedGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem weightedGram_eq_sum (A : Matrix κ κ ℝ) (w : κ → ℝ) :
    A * Matrix.diagonal w * A.transpose =
      ∑ k, w k • Matrix.vecMulVec (fun i => A i k) (fun i => A i k) := by
  funext i j
  rw [Matrix.mul_apply, Matrix.sum_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem weightedGram_isUnit (A : Matrix κ κ ℝ) (w : κ → ℝ)
    (hA : IsUnit A) (hw : ∀ k, w k ≠ 0) : IsUnit (A * Matrix.diagonal w * A.transpose) := by
  have hD : IsUnit (Matrix.diagonal w) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => hw k)
  exact (hA.mul hD).mul ((Matrix.isUnit_transpose A).mpr hA)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TriangleFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem triangleDiagonalWeight_ne_zero (s : ℕ) (node : OrderedNode s → ℝ)
    (hn : Function.Injective node) (j : BiExponent s) : triangleDiagonalWeight s node j ≠ 0 := by
  let pq := triangleNodePair s (triangleCoordEquiv s j)
  have hmem : (pq.1.val,pq.2.val) ∈ twoTriangle s := (triangleCoordEquiv s j).property
  have hpq : pq.1 ≠ pq.2 := by
    intro he
    have hv := congrArg Subtype.val he
    rw [mem_twoTriangle] at hmem
    omega
  exact mul_ne_zero ((triangleCoefficient_ne_zero_iff s pq.1 pq.2).mpr hmem)
    (detectorWeight_ne_zero node hn hpq)

theorem rankDetector_triangle_sum (s : ℕ) (node : OrderedNode s → ℝ) :
    rankDetector s node (fun p q => triangleCoefficient s p q) =
      ∑ j : BiExponent s,
        let pq := triangleNodePair s (triangleCoordEquiv s j)
        triangleCoefficient s pq.1 pq.2 • detectorAtom s node pq.1 pq.2 := by
  let f := fun pq : OrderedNode s × OrderedNode s =>
    triangleCoefficient s pq.1 pq.2 • detectorAtom s node pq.1 pq.2
  have hfull : rankDetector s node (fun p q => triangleCoefficient s p q) = ∑ pq, f pq :=
    (Fintype.sum_prod_type f).symm
  have hfilter : (∑ pq ∈ orderedTriangle s, f pq) = ∑ pq, f pq := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro pq hpq hnot
    have hm : (pq.1.val,pq.2.val) ∉ twoTriangle s := by simpa [orderedTriangle] using hnot
    have hz : triangleCoefficient s pq.1 pq.2 = 0 :=
      not_ne_iff.mp (mt (triangleCoefficient_ne_zero_iff s pq.1 pq.2).mp hm)
    simp only [f, hz, zero_smul]
  rw [hfull, ← hfilter, ← Finset.sum_coe_sort]
  exact ((triangleCoordEquiv s).trans (triangleNodeEquiv s)).sum_comp
    (fun pq : ↥(orderedTriangle s) => f pq.val) |>.symm

theorem rankDetector_triangle_factorization (s : ℕ) (node : OrderedNode s → ℝ) :
    rankDetector s node (fun p q => triangleCoefficient s p q) =
      triangleMatrix s (extendOrderedNode s node) * Matrix.diagonal (triangleDiagonalWeight s node) *
        (triangleMatrix s (extendOrderedNode s node)).transpose := by
  rw [rankDetector_triangle_sum, weightedGram_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [triangleDiagonalWeight, detectorAtom, smul_smul]
  congr 2
  · funext ab
    exact (triangleMatrix_ordered_entry s node ab j).symm
  · funext ab
    exact (triangleMatrix_ordered_entry s node ab j).symm

theorem rankDetector_ordered_isUnit (s : ℕ) (node : OrderedNode s → ℝ)
    (hn : Function.Injective node) :
    IsUnit (rankDetector s node (halfOrderMatrix (OrderedNode s))) := by
  rw [rankDetector_halfOrder_reduction s node hn]
  apply IsUnit.neg
  change IsUnit (rankDetector s node (fun p q => triangleCoefficient s p q))
  rw [rankDetector_triangle_factorization]
  exact weightedGram_isUnit _ _
    (triangleMatrix_isUnit s (extendOrderedNode s node) (extendOrderedNode_injOn s node hn))
    (triangleDiagonalWeight_ne_zero s node hn)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_HalfOrderInvertibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rankDetector_halfOrder_isUnit [LinearOrder ι] (s : ℕ) (node : ι → ℝ)
    (hn : Function.Injective node) (hcard : Fintype.card ι = 2*s+1) :
    IsUnit (rankDetector s node (halfOrderMatrix ι)) := by
  let e : OrderedNode s ≃o ι :=
    (Fintype.orderIsoFinOfCardEq (OrderedNode s) (card_orderedNode s)).symm.trans
      (Fintype.orderIsoFinOfCardEq ι hcard)
  have hunit := rankDetector_ordered_isUnit s (node ∘ e) (hn.comp e.injective)
  have he := rankDetector_equiv s node e.toEquiv (halfOrderMatrix ι)
  change rankDetector s (node ∘ e) ((halfOrderMatrix ι).submatrix e e) =
    rankDetector s node (halfOrderMatrix ι) at he
  rw [halfOrderMatrix_orderIso e] at he
  rwa [he] at hunit

theorem lemma4_2 (s : ℕ) (hs : 0 < s) (node : ι → ℝ) (hn : Function.Injective node)
    (hcard : Fintype.card ι = 2*s+1) :
    (∀ r c : ι → ℝ, rankDetector s node (fun p q => r p+c q) = 0) ∧
    (∀ d : ι → ℝ, rankDetector s node (Matrix.diagonal d) = 0) ∧
    (∀ p q : ι, p ≠ q → (rankDetector s node (Matrix.single p q 1)).rank = 1) ∧
    (∀ order : LinearOrder ι, IsUnit (rankDetector s node (@halfOrderMatrix ι order))) := by
  refine ⟨rankDetector_additive s node hn hcard, rankDetector_diagonal s node, ?_, ?_⟩
  · intro p q hpq
    rw [rankDetector_single, one_smul]
    exact detectorAtom_rank_one s hs node hn hpq
  · intro order
    let := order
    exact rankDetector_halfOrder_isUnit s node hn hcard

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

theorem leftHalfOrder_eq_halfOrder (i : Fin m) :
    C.leftHalfOrder i=@halfOrderMatrix (Fin n) (C.leftOrder i) := by
  ext p q
  change orderSign (C.leftNode i p) (C.leftNode i q)/2=
    if C.leftNode i p<C.leftNode i q then (1/2 : ℝ) else if C.leftNode i q<C.leftNode i p then -1/2 else 0
  unfold orderSign
  split_ifs <;> norm_num

theorem diagonal_detector_isUnit_oai (hnorm : NoAdjacentCrossings D)
    (s : ℕ) (hs : 0 < s) (node : Fin n → ℝ) (hn : Function.Injective node)
    (hcard : n=2*s+1) (i : Fin m) :
    IsUnit (rankDetector s node (edgeBlock C.cycleIntersectionMatrix i i)) := by
  rw [C.cycleIntersectionMatrix_diagonal_block hnorm,C.leftHalfOrder_eq_halfOrder]
  exact (lemma4_2 s hs node hn (by simpa only [Fintype.card_fin] using hcard)).2.2.2 (C.leftOrder i)

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

theorem solution : type_of% @OAI.Zarankiewicz.TruncatedSpokeCoordinates.diagonal_detector_isUnit_oai := @OAI.Zarankiewicz.TruncatedSpokeCoordinates.diagonal_detector_isUnit_oai
