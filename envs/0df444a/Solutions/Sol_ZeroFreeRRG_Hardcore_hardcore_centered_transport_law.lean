-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_centered_transport_law
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:23:53.876313+00:00
-- url     : https://prove2.me/submissions/66eed4aa-973c-4659-a44d-cc2595a7d533

import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_edge_transport
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (α α' : ℝ) (ha : 0 < α) (hlt : α < α') (ha' : α' < 1/2)
    (ν : ProbabilityMeasure (Fin 2 → ℝ)) (hν : ν ∈ cavityLaws .hardcore α)
    (ν' : ProbabilityMeasure (Fin 2 → ℝ))
    (hmap : (ν' : Measure (Fin 2 → ℝ)) = Measure.map
      (fun x : Fin 2 → ℝ => fun i =>
        (1-(1-α')/(1-α))*(if i.val=1 then 1 else 0) + ((1-α')/(1-α))*x i)
      (ν : Measure (Fin 2 → ℝ))) :
    Measure.map (fun x : Fin 2 → ℝ => (x 1-α')/(1-α')) (ν' : Measure (Fin 2 → ℝ)) =
      Measure.map (fun x : Fin 2 → ℝ => (x 1-α)/(1-α)) (ν : Measure (Fin 2 → ℝ)) := by
  let c := (1-α')/(1-α)
  let T := fun (x : Fin 2 → ℝ) i => (1-c)*(if i.val=1 then 1 else 0)+c*x i
  let C := fun (x : Fin 2 → ℝ) => (x 1-α)/(1-α)
  let C' := fun (x : Fin 2 → ℝ) => (x 1-α')/(1-α')
  have hT : Measurable T := by
    apply measurable_pi_lambda
    intro i
    dsimp [T]
    fun_prop
  have hC : Measurable C' := by dsimp [C']; fun_prop
  have hae : ∀ᵐ x ∂(ν : Measure (Fin 2 → ℝ)), x ∈ stdSimplex ℝ (Fin 2) := by
    apply ae_iff.mpr
    exact hν.1
  change Measure.map C' (ν' : Measure (Fin 2 → ℝ)) = Measure.map C (ν : Measure (Fin 2 → ℝ))
  rw [hmap, Measure.map_map hC hT]
  apply Measure.map_congr
  filter_upwards [hae] with x hx
  have hs : (∑ i, x i) = 1 := hx.2
  have hh := hardcore_edge_transport α α' ha hlt ha' x x hs hs
  exact hh.2.2.1
