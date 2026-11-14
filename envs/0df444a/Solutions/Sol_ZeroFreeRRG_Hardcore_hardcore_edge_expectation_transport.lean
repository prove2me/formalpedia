-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_edge_expectation_transport
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:23:53.812197+00:00
-- url     : https://prove2.me/submissions/15ff3d3b-3340-41a7-8d5e-654b45c47e8b

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
    (∫ p : (Fin 2 → ℝ) × (Fin 2 → ℝ), xlogx (edgeFactor .hardcore α' p.1 p.2)
      ∂((ν' : Measure (Fin 2 → ℝ)).prod (ν' : Measure (Fin 2 → ℝ)))) =
    ∫ p : (Fin 2 → ℝ) × (Fin 2 → ℝ), xlogx (edgeFactor .hardcore α p.1 p.2)
      ∂((ν : Measure (Fin 2 → ℝ)).prod (ν : Measure (Fin 2 → ℝ))) := by
  let c := (1-α')/(1-α)
  let T := fun (x : Fin 2 → ℝ) i => (1-c)*(if i.val=1 then 1 else 0)+c*x i
  let H := fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => xlogx (edgeFactor .hardcore α' p.1 p.2)
  have hT : Measurable T := by
    apply measurable_pi_lambda
    intro i
    dsimp [T]
    fun_prop
  have hH : Measurable H := by
    dsimp [H,xlogx,edgeFactor]
    fun_prop
  have hae : ∀ᵐ x ∂(ν : Measure (Fin 2 → ℝ)), x ∈ stdSimplex ℝ (Fin 2) := by
    apply ae_iff.mpr
    exact hν.1
  have hpair : ∀ᵐ p ∂((ν : Measure (Fin 2 → ℝ)).prod (ν : Measure (Fin 2 → ℝ))),
      p.1 ∈ stdSimplex ℝ (Fin 2) ∧ p.2 ∈ stdSimplex ℝ (Fin 2) := by
    apply (Measure.ae_prod_iff_ae_ae _).2
    · filter_upwards [hae] with x hx
      filter_upwards [hae] with y hy
      exact ⟨hx,hy⟩
    · exact ((isClosed_stdSimplex ℝ (Fin 2)).measurableSet.preimage measurable_fst).inter
        ((isClosed_stdSimplex ℝ (Fin 2)).measurableSet.preimage measurable_snd)
  change (∫ p, H p ∂((ν' : Measure (Fin 2 → ℝ)).prod (ν' : Measure (Fin 2 → ℝ)))) = _
  rw [hmap, Measure.map_prod_map _ _ hT hT,
    integral_map (hT.prodMap hT).aemeasurable hH.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hpair] with p hp
  have hx : (∑ i, p.1 i)=1 := hp.1.2
  have hy : (∑ i, p.2 i)=1 := hp.2.2
  have hh := hardcore_edge_transport α α' ha hlt ha' p.1 p.2 hx hy
  dsimp [H]
  rw [hh.2.2.2.2]
