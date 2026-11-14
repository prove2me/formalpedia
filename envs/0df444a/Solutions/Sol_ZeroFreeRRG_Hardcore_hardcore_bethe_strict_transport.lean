-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_bethe_strict_transport
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:23:53.779322+00:00
-- url     : https://prove2.me/submissions/16bb62fc-1bb0-4320-bf0d-a49d9b6b6061

import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_vertex_entropy_strict_mono
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_centered_cavity_law
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_centered_vertex_expectation
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_centered_transport_law
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_edge_expectation_transport
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d : ℕ) (hd : 2 ≤ d) (α α' : ℝ) (ha : 0 < α) (hlt : α < α') (ha' : α' < 1/2)
    (ν : ProbabilityMeasure (Fin 2 → ℝ)) (hν : ν ∈ cavityLaws .hardcore α)
    (hne : ν ≠ diracPi .hardcore α)
    (ν' : ProbabilityMeasure (Fin 2 → ℝ)) (hν' : ν' ∈ cavityLaws .hardcore α')
    (hmap : (ν' : Measure (Fin 2 → ℝ)) = Measure.map
      (fun x : Fin 2 → ℝ => fun i =>
        (1-(1-α')/(1-α))*(if i.val=1 then 1 else 0) + ((1-α')/(1-α))*x i)
      (ν : Measure (Fin 2 → ℝ))) :
    betheK .hardcore α d ν < betheK .hardcore α' d ν' := by
  let C := fun x : Fin 2 → ℝ => (x 1-α)/(1-α)
  let C' := fun x : Fin 2 → ℝ => (x 1-α')/(1-α')
  let η := Measure.map C (ν : Measure (Fin 2 → ℝ))
  let η' := Measure.map C' (ν' : Measure (Fin 2 → ℝ))
  let θ := α/(1-α)
  let θ' := α'/(1-α')
  have ha0' : 0 < α' := by linarith
  have ha1 : α < 1/2 := by linarith
  have hden : 0 < 1-α := by linarith
  have hden' : 0 < 1-α' := by linarith
  have ht0 : 0 < θ := div_pos ha hden
  have ht'0 : 0 < θ' := div_pos ha0' hden'
  have ht1 : θ < 1 := by dsimp [θ]; apply (div_lt_one₀ hden).2; linarith
  have ht'1 : θ' < 1 := by dsimp [θ']; apply (div_lt_one₀ hden').2; linarith
  have htt : θ < θ' := by
    dsimp [θ,θ']
    apply (div_lt_div_iff₀ hden hden').2
    nlinarith
  have hη := hardcore_centered_cavity_law α ha ha1 ν hν hne
  letI : IsProbabilityMeasure η := hη.1
  have hηeq : η'=η := hardcore_centered_transport_law α α' ha hlt ha' ν hν ν' hmap
  have hmono := hardcore_vertex_entropy_strict_mono d hd η hη.2.1 hη.2.2.1 hη.2.2.2.1 hη.2.2.2.2
  have hcmp := hmono (show θ ∈ Ioo (0:ℝ) 1 from ⟨ht0,ht1⟩)
    (show θ' ∈ Ioo (0:ℝ) 1 from ⟨ht'0,ht'1⟩) htt
  have hv := hardcore_centered_vertex_expectation d α ha ha1 ν hν
  have hv' := hardcore_centered_vertex_expectation d α' ha0' ha' ν' hν'
  change (∫ xs : Fin d → Fin 2 → ℝ, xlogx (vertexFactor .hardcore α d xs)
      ∂(Measure.pi fun _ : Fin d => (ν : Measure (Fin 2 → ℝ)))) = _ at hv
  change (∫ xs : Fin d → Fin 2 → ℝ, xlogx (vertexFactor .hardcore α' d xs)
      ∂(Measure.pi fun _ : Fin d => (ν' : Measure (Fin 2 → ℝ)))) = _ at hv'
  change _ = (∫ hs : Fin d → ℝ, (let V := ((∏ i, (1+θ*hs i))+θ*(∏ i, (1-hs i)))/(1+θ); V*Real.log V)
      ∂(Measure.pi fun _ : Fin d => η)) at hv
  change _ = (∫ hs : Fin d → ℝ, (let V := ((∏ i, (1+θ'*hs i))+θ'*(∏ i, (1-hs i)))/(1+θ'); V*Real.log V)
      ∂(Measure.pi fun _ : Fin d => η')) at hv'
  rw [hηeq] at hv'
  change _ < (∫ hs : Fin d → ℝ, (let V := ((∏ i, (1+θ'*hs i))+θ'*(∏ i, (1-hs i)))/(1+θ'); V*Real.log V)
      ∂(Measure.pi fun _ : Fin d => η)) at hcmp
  have he := hardcore_edge_expectation_transport α α' ha hlt ha' ν hν ν' hmap
  unfold betheK
  change (∫ xs : Fin d → Fin 2 → ℝ, xlogx (vertexFactor .hardcore α d xs)
    ∂(Measure.pi fun _ : Fin d => (ν : Measure (Fin 2 → ℝ)))) - (d:ℝ)/2 *
      (∫ p : (Fin 2 → ℝ) × (Fin 2 → ℝ), xlogx (edgeFactor .hardcore α p.1 p.2)
        ∂((ν : Measure (Fin 2 → ℝ)).prod (ν : Measure (Fin 2 → ℝ)))) <
    (∫ xs : Fin d → Fin 2 → ℝ, xlogx (vertexFactor .hardcore α' d xs)
    ∂(Measure.pi fun _ : Fin d => (ν' : Measure (Fin 2 → ℝ)))) - (d:ℝ)/2 *
      (∫ p : (Fin 2 → ℝ) × (Fin 2 → ℝ), xlogx (edgeFactor .hardcore α' p.1 p.2)
        ∂((ν' : Measure (Fin 2 → ℝ)).prod (ν' : Measure (Fin 2 → ℝ))))
  rw [hv,hv',he]
  exact sub_lt_sub_right hcmp _
