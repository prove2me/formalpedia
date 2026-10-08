-- Prove2me | solution 1 for PlaneDrawingDartArcDataExists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:51:16.910453+00:00
-- url     : https://prove2.me/submissions/e54481f8-3c89-4e22-a7a9-03cc7a8341bc

import Mathlib
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData

set_option autoImplicit false

open Classical

theorem PDDA705_rev_rev (Γ : PolygonalArc) :
    PolygonalArcReverse (PolygonalArcReverse Γ) = Γ := by
  cases Γ
  simp only [PolygonalArcReverse, List.reverse_reverse]

theorem PDDA705_endpoints {V : Type*} [Fintype V]
    {G : SimpleGraph V} [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (e : G.edgeFinset) (a b : V)
    (he : e.1 = s(a, b)) :
    ((D.edgeArc e).source = D.vertexPlacement a ∧
        (D.edgeArc e).target = D.vertexPlacement b) ∨
      ((D.edgeArc e).source = D.vertexPlacement b ∧
        (D.edgeArc e).target = D.vertexPlacement a) := by
  obtain ⟨u, v, _, huv, h⟩ := D.edgeArc_endpoints e
  rw [he] at huv
  rcases Sym2.eq_iff.1 huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h
  · exact h.symm

theorem solution {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0) :
    Nonempty (PlaneDrawingDartArcData G D) := by
  classical
  let dE : G.Dart → G.edgeFinset := fun d =>
    ⟨d.edge, by simpa [SimpleGraph.mem_edgeFinset] using d.edge_mem⟩
  have dE_val : ∀ d : G.Dart, (dE d).1 = d.edge := fun d => rfl
  have dE_symm : ∀ d : G.Dart, dE d.symm = dE d := by
    intro d; apply Subtype.ext; simp [dE_val]
  have hedge : ∀ d : G.Dart, (dE d).1 = s(d.toProd.1, d.toProd.2) := by
    intro d; rfl
  have hne : ∀ d : G.Dart, D.vertexPlacement d.toProd.1 ≠ D.vertexPlacement d.toProd.2 :=
    fun d h => d.adj.ne (D.vertexPlacement_injective h)
  let dA : G.Dart → PolygonalArc := fun d =>
    if (D.edgeArc (dE d)).source = D.vertexPlacement d.toProd.1 then D.edgeArc (dE d)
    else PolygonalArcReverse (D.edgeArc (dE d))
  have key : ∀ d : G.Dart,
      ((D.edgeArc (dE d)).source = D.vertexPlacement d.toProd.1 ∧
        (D.edgeArc (dE d)).target = D.vertexPlacement d.toProd.2 ∧
        dA d = D.edgeArc (dE d)) ∨
      ((D.edgeArc (dE d)).source = D.vertexPlacement d.toProd.2 ∧
        (D.edgeArc (dE d)).target = D.vertexPlacement d.toProd.1 ∧
        dA d = PolygonalArcReverse (D.edgeArc (dE d))) := by
    intro d
    rcases PDDA705_endpoints D (dE d) d.toProd.1 d.toProd.2 (hedge d) with h | h
    · left; exact ⟨h.1, h.2, by simp [dA, h.1]⟩
    · right
      refine ⟨h.1, h.2, ?_⟩
      have : (D.edgeArc (dE d)).source ≠ D.vertexPlacement d.toProd.1 := by
        rw [h.1]; exact (hne d).symm
      simp [dA, this]
  refine ⟨{ dartEdge := dE, dartEdge_eq := dE_val, dartArc := dA,
            dartArc_orientation := ?_, dartArc_carrier := ?_,
            dartArc_source := ?_, dartArc_target := ?_,
            dartArc_symm_eq_reverse := ?_ }⟩
  · intro d
    rcases key d with h | h
    · exact Or.inl ⟨h.2.2, h.1⟩
    · exact Or.inr ⟨h.2.2, h.2.1⟩
  · intro d
    rcases key d with h | h
    · rw [h.2.2]
    · rw [h.2.2]; rfl
  · intro d
    rcases key d with h | h
    · rw [h.2.2, h.1]
    · rw [h.2.2]; exact h.2.1
  · intro d
    rcases key d with h | h
    · rw [h.2.2, h.2.1]
    · rw [h.2.2]; exact h.1
  · intro d
    have hs1 : d.symm.toProd.1 = d.toProd.2 := rfl
    have hs2 : d.symm.toProd.2 = d.toProd.1 := rfl
    rcases key d with h | h <;> rcases key d.symm with h' | h' <;>
      rw [dE_symm, hs1, hs2] at h' <;> rw [h.2.2, h'.2.2]
    · exact absurd (h.1.symm.trans h'.1) (hne d)
    · rw [PDDA705_rev_rev]
    · exact absurd (h.1.symm.trans h'.1) (hne d).symm
