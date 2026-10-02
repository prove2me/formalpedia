-- Prove2me | solution 1 for PolyakovAction.translation_invariance
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T12:54:11.596782+00:00
-- url     : https://prove2.me/submissions/6285c4ea-caba-4c44-8cc5-e67a6683a72a

import Mathlib
import Definitions.Def_PolyakovAction_Defs
open MeasureTheory Filter Asymptotics
open scoped Matrix Topology
open PolyakovAction

theorem solution {D : ℕ} (T : ℝ) (g : Matrix (Fin D) (Fin D) ℝ)
    (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ) (X : Worldsheet → Spacetime D)
    (b : Spacetime D) (U : Set Worldsheet) :
    polyakovAction T (fun _ => g) h (fun σ => X σ + b) U
      = polyakovAction T (fun _ => g) h X U := by
  -- partialDeriv (X+b) = partialDeriv X since fderiv of constant is 0
  have hpd : ∀ a μ σ, partialDeriv (fun σ => X σ + b) a μ σ = partialDeriv X a μ σ := by
    intro a μ σ
    simp [partialDeriv, fderiv_add, fderiv_const]
  -- induced metric equal
  have him : ∀ σ, inducedMetric (fun _ => g) (fun σ => X σ + b) σ =
      inducedMetric (fun _ => g) X σ := by
    intro σ
    ext a b'
    simp [inducedMetric, hpd]
  -- Lagrangian equal pointwise
  have hL : ∀ σ, polyakovLagrangian (fun _ => g) h (fun σ => X σ + b) σ =
      polyakovLagrangian (fun _ => g) h X σ := by
    intro σ
    simp [polyakovLagrangian, him]
  unfold polyakovAction
  simp [hL]
