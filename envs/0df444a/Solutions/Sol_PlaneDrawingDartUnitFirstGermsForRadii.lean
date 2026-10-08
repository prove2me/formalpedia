-- Prove2me | solution 1 for PlaneDrawingDartUnitFirstGermsForRadii
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T17:21:56.214944+00:00
-- url     : https://prove2.me/submissions/2cacda78-2d28-4ec4-af15-31d98761d39a

import Mathlib
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData

set_option autoImplicit false

theorem pdg9a_head (Γ : PolygonalArc) :
    Γ.vertices[0]'(by have := Γ.length_ge_two; omega) = Γ.source := by
  have h := Γ.source_eq_head
  rw [List.head?_eq_getElem?] at h
  rw [List.getElem?_eq_getElem (by have := Γ.length_ge_two; omega)] at h
  exact Option.some.inj h

theorem pdg9a_carrier (Γ : PolygonalArc) (c : EuclideanSpace ℝ (Fin 2)) (hc : Γ.source = c)
    (R : ℝ) (hR : 0 < R)
    (hle : R ≤ ‖Γ.vertices[1]'(Nat.lt_of_succ_le Γ.length_ge_two) - c‖) :
    openSegment ℝ c (c + R • ((‖Γ.vertices[1]'(Nat.lt_of_succ_le Γ.length_ge_two) - c‖)⁻¹ •
        (Γ.vertices[1]'(Nat.lt_of_succ_le Γ.length_ge_two) - c))) ⊆ Γ.carrier := by
  set q := Γ.vertices[1]'(Nat.lt_of_succ_le Γ.length_ge_two) - c with hq
  have hpos : 0 < ‖q‖ := lt_of_lt_of_le hR hle
  have hseg : segment ℝ c (Γ.vertices[1]'(Nat.lt_of_succ_le Γ.length_ge_two)) ⊆ Γ.carrier := by
    intro p hp
    rw [Γ.carrier_eq]
    refine ⟨0, Nat.lt_of_succ_le Γ.length_ge_two, ?_⟩
    rw [pdg9a_head Γ, hc]
    simpa using hp
  refine subset_trans (openSegment_subset_segment ℝ _ _) (subset_trans ?_ hseg)
  apply (convex_segment _ _).segment_subset (left_mem_segment _ _ _)
  rw [segment_eq_image']
  refine ⟨R * ‖q‖⁻¹, ⟨by positivity, ?_⟩, ?_⟩
  · rw [mul_inv_le_iff₀ hpos]; linarith
  · simp only [hq, smul_smul]

theorem pdg9a_ball (c u : EuclideanSpace ℝ (Fin 2)) (hu : ‖u‖ = 1) (R : ℝ) (hR : 0 < R) :
    openSegment ℝ c (c + R • u) ⊆ Metric.ball c R := by
  intro p hp
  rw [openSegment_eq_image'] at hp
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hp
  rw [Metric.mem_ball, dist_eq_norm]
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos h0, abs_of_pos hR, hu,
    mul_one]
  nlinarith

open Classical in
theorem solution {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G)
    (A : PlaneDrawingDartArcData G D)
    (R : V → ℝ) (hR : ∀ v : V, 0 < R v)
    (hR_le_first :
      ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        R v ≤ ‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le (A.dartArc d.1).length_ge_two) -
          D.vertexPlacement v‖) :
    ∃ germDirection :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} → EuclideanSpace ℝ (Fin 2),
      ∃ radialGerm :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} →
          Set (EuclideanSpace ℝ (Fin 2)),
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          germDirection v d ≠ 0) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          germDirection v d =
            (‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc d.1).length_ge_two) - D.vertexPlacement v‖)⁻¹ •
              ((A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc d.1).length_ge_two) - D.vertexPlacement v)) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          ∃ r : ℝ, 0 < r ∧ r ≤ R v ∧
            radialGerm v d =
              openSegment ℝ (D.vertexPlacement v)
                (D.vertexPlacement v + r • germDirection v d)) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          radialGerm v d =
            openSegment ℝ (D.vertexPlacement v)
              (D.vertexPlacement v + R v • germDirection v d)) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          radialGerm v d ⊆ (D.edgeArc (A.dartEdge d.1)).carrier) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          radialGerm v d ⊆ Metric.ball (D.vertexPlacement v) (R v)) := by
  have hq : ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
      (0:ℝ) < ‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le (A.dartArc d.1).length_ge_two) -
          D.vertexPlacement v‖ := fun v d => (hR v).trans_le (hR_le_first v d)
  refine ⟨fun v d => (‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc d.1).length_ge_two) - D.vertexPlacement v‖)⁻¹ •
              ((A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc d.1).length_ge_two) - D.vertexPlacement v),
    fun v d => openSegment ℝ (D.vertexPlacement v)
      (D.vertexPlacement v + R v • ((‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc d.1).length_ge_two) - D.vertexPlacement v‖)⁻¹ •
              ((A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc d.1).length_ge_two) - D.vertexPlacement v))),
    ?_, fun v d => rfl, fun v d => ⟨R v, hR v, le_rfl, rfl⟩, fun v d => rfl, ?_, ?_⟩
  · intro v d
    have h := hq v d
    exact smul_ne_zero (inv_ne_zero h.ne') (norm_pos_iff.mp h)
  · intro v d
    rw [← A.dartArc_carrier d.1]
    exact pdg9a_carrier _ _ (by rw [A.dartArc_source, d.2]) _ (hR v) (hR_le_first v d)
  · intro v d
    have h := hq v d
    refine pdg9a_ball _ _ ?_ _ (hR v)
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h.ne']
