-- Prove2me | solution 1 for PettisIntegral.weakIntegral_prod
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:14:00.610998+00:00
-- url     : https://prove2.me/submissions/ecd124a1-1fac-4f58-899a-dabf93de923a

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace Sol_PettisIntegral_weakIntegral_prod

open PettisIntegral

/-- The Pettis integral of a Pettis integrable function represents its weak integral. -/
theorem apply_pettisIntegral {𝕜 E X : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [MeasurableSpace X] {μ : Measure X} {g : X → E}
    (h : PettisIntegrable 𝕜 μ g) (φ : StrongDual 𝕜 E) :
    φ (pettisIntegral 𝕜 μ g) = ∫ x, φ (g x) ∂μ := by
  have hspec : HasPettisIntegral 𝕜 μ g (Classical.choose h) := Classical.choose_spec h
  have heq : pettisIntegral 𝕜 μ g = Classical.choose h := by
    unfold pettisIntegral
    exact dif_pos h
  rw [heq]
  exact hspec.2 φ

end Sol_PettisIntegral_weakIntegral_prod

open PettisIntegral Sol_PettisIntegral_weakIntegral_prod

theorem solution {𝕜 E X Y : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E]
    [T2Space E] [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (f : X × Y → E) (hf : WeaklyIntegrable 𝕜 (μ.prod ν) f)
    (hx : ∀ x : X, PettisIntegrable 𝕜 ν (fun y => f (x, y)))
    (hy : ∀ y : Y, PettisIntegrable 𝕜 μ (fun x => f (x, y))) :
    WeaklyIntegrable 𝕜 μ (fun x => pettisIntegral 𝕜 ν (fun y => f (x, y))) ∧
      WeaklyIntegrable 𝕜 ν (fun y => pettisIntegral 𝕜 μ (fun x => f (x, y))) ∧
      weakIntegral 𝕜 μ (fun x => pettisIntegral 𝕜 ν (fun y => f (x, y))) =
        weakIntegral 𝕜 (μ.prod ν) f ∧
      weakIntegral 𝕜 ν (fun y => pettisIntegral 𝕜 μ (fun x => f (x, y))) =
        weakIntegral 𝕜 (μ.prod ν) f := by
  -- the scalar functions `φ ∘ (partial Pettis integral)` are the partial integrals of `φ ∘ f`
  have hX : ∀ φ : StrongDual 𝕜 E,
      (fun x => φ (pettisIntegral 𝕜 ν (fun y => f (x, y)))) =
        fun x => ∫ y, φ (f (x, y)) ∂ν := fun φ =>
    funext fun x => apply_pettisIntegral (hx x) φ
  have hY : ∀ φ : StrongDual 𝕜 E,
      (fun y => φ (pettisIntegral 𝕜 μ (fun x => f (x, y)))) =
        fun y => ∫ x, φ (f (x, y)) ∂μ := fun φ =>
    funext fun y => apply_pettisIntegral (hy y) φ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro φ
    have h := (hf φ).integral_prod_left
    rw [hX φ]
    exact h
  · intro φ
    have h := (hf φ).integral_prod_right
    rw [hY φ]
    exact h
  · funext φ
    show ∫ x, φ (pettisIntegral 𝕜 ν (fun y => f (x, y))) ∂μ = ∫ z, φ (f z) ∂(μ.prod ν)
    rw [hX φ]
    exact (integral_prod (fun z : X × Y => φ (f z)) (hf φ)).symm
  · funext φ
    show ∫ y, φ (pettisIntegral 𝕜 μ (fun x => f (x, y))) ∂ν = ∫ z, φ (f z) ∂(μ.prod ν)
    rw [hY φ]
    exact (integral_prod_symm (fun z : X × Y => φ (f z)) (hf φ)).symm
