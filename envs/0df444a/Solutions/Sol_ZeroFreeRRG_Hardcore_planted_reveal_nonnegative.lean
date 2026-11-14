-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.planted_reveal_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:02:12.12614+00:00
-- url     : https://prove2.me/submissions/04b3fea4-b0e6-43dd-8d1c-6635ce96cee8

import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (t s : ℝ) (d n : ℕ)
    (hπ : ∀ a, 0 ≤ m.pi t a) (hP : ∀ a b, 0 ≤ m.P t a b) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ (M : Matching n d) (σ : Fin n → m.Spin) (U : Finset (Fin n)),
      0 ≤ planted m t M σ * revealProb s U := by
  classical
  have hM : ∀ a b, 0 ≤ m.M t a b := fun a b => div_nonneg (hP a b) (mul_nonneg (hπ a) (hπ b))
  have hw (M : Matching n d) (σ : Fin n → m.Spin) : 0 ≤ weight m t M σ := by
    unfold weight
    exact mul_nonneg (Finset.prod_nonneg fun v hv => hπ (σ v))
      (Finset.prod_nonneg fun x hx => hM (σ x.1) (σ (M.1 x).1))
  have hZ (M : Matching n d) : 0 ≤ normZ m t M := Finset.sum_nonneg fun σ hσ => hw M σ
  have han : 0 ≤ an m d n t := by
    unfold an cmE
    apply div_nonneg
    · exact Finset.sum_nonneg fun M hM => hZ M
    · positivity
  intro M σ U
  apply mul_nonneg
  · unfold planted
    apply div_nonneg (hw M σ)
    exact mul_nonneg (by positivity) han
  · unfold revealProb
    exact mul_nonneg (pow_nonneg hs _) (pow_nonneg (sub_nonneg.mpr hs1) _)
