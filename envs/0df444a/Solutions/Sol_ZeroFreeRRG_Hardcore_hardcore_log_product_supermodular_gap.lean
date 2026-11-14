-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_log_product_supermodular_gap
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:30:21.646869+00:00
-- url     : https://prove2.me/submissions/abb110a7-855d-4116-bf5b-d4166b358f78

import Theorems.Thm_ZeroFreeRRG_Hardcore_finite_supermodular_telescoping
import Theorems.Thm_ZeroFreeRRG_Hardcore_finite_supermodular_telescoping_strict
import Theorems.Thm_ZeroFreeRRG_Hardcore_log_product_set_supermodular
import Theorems.Thm_ZeroFreeRRG_Hardcore_log_product_strict_mixed_difference
import Mathlib
set_option autoImplicit false
open scoped BigOperators
open ZeroFreeRRG.Hardcore

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (θ : ℝ) (hθ : 0 ≤ θ)
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    let g := fun S : Finset ι => Real.log (1+θ*∏ a, if a ∈ S then y a else x a)
    g Finset.univ ≥ g ∅ + ∑ i, (g {i}-g ∅) ∧
    (0 < θ → ∀ i j, i ≠ j → x i < y i → x j < y j →
      (∀ a, a ≠ i → a ≠ j → 0 < x a) →
      g Finset.univ > g ∅ + ∑ i, (g {i}-g ∅)) := by
  classical
  let g : Finset ι → ℝ := fun S => Real.log (1+θ*∏ a, if a ∈ S then y a else x a)
  have hsm : ∀ S : Finset ι, ∀ i j, i ∉ S → j ∉ S → i ≠ j →
      g (insert i (insert j S))+g S ≥ g (insert i S)+g (insert j S) := by
    intro S i j hi hj hij
    exact log_product_set_supermodular θ hθ x y hx hxy S i j hi hj hij
  constructor
  · exact finite_supermodular_telescoping g hsm Finset.univ
  · intro hθ' i j hij hi hj hrest
    let T : Finset ι := (Finset.univ.erase i).erase j
    have hiT : i ∉ T := by simp [T]
    have hjT : j ∉ T := by simp [T]
    have hpair : g {i,j}+g ∅ > g {i}+g {j} := by
      have hh := log_product_strict_mixed_difference θ hθ' x y hx hxy i j hij hi hj hrest
      simpa [g] using hh
    have hh := finite_supermodular_telescoping_strict g hsm T i j hiT hjT hij hpair
    have hset : insert i (insert j T) = Finset.univ := by
      ext a
      simp [T]
      tauto
    change g Finset.univ > g ∅ + ∑ i, (g {i}-g ∅)
    simpa only [hset] using hh
