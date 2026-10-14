-- Prove2me | solution 1 for Plasticity.U16
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T07:54:50.882191+00:00
-- url     : https://prove2.me/submissions/a86c2f3b-6267-43db-ac54-e7230eb073dc

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_U16_linearize
import Theorems.Thm_Plasticity_U16_onto
import Theorems.Thm_Plasticity_U16_complete

theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] [Nontrivial Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (hcover : Metric.sphere (0 : Y) 1 ⊆ F '' Metric.closedBall (0 : X) 1) :
    ∃ T : X ≃ₗᵢ[ℝ] Y, Set.EqOn F T (Metric.closedBall (0 : X) 1) := by
  obtain ⟨T, hT⟩ := Plasticity.U16.linearize F hmaps hlip hsphere hcover
  have hsurj := Plasticity.U16.onto F hmaps hlip hsphere hcover T 8 hT
  let S : X ≃ₗᵢ[ℝ] Y := LinearIsometryEquiv.ofSurjective T hsurj
  have hS : ∀ x ∈ Metric.closedBall (0 : X) 1, ‖F x - S x‖ ≤ 8 * ‖x‖ ^ 2 := fun x hx => hT x hx
  exact ⟨S, Plasticity.U16.complete F hmaps hlip hsphere S 8 hS⟩
