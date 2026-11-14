-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.safe_spin_preserves_support
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:07:57.141206+00:00
-- url     : https://prove2.me/submissions/6595a9bf-ba80-4517-962a-685182f2eed3

import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (t : ℝ) (d n : ℕ) (M : Matching n d)
    (σ : Fin n → m.Spin) (v : Fin n) (a₀ : m.Spin)
    (hπ : ∀ a, m.pi t a ≠ 0)
    (hsafeL : ∀ a, m.M t a₀ a ≠ 0) (hsafeR : ∀ a, m.M t a a₀ ≠ 0)
    (hw : weight m t M σ ≠ 0) :
    weight m t M (Function.update σ v a₀) ≠ 0 := by
  classical
  have hedge : (∏ x ∈ edgeReps M, m.M t (σ x.1) (σ (M.1 x).1)) ≠ 0 := by
    exact (mul_ne_zero_iff.mp hw).2
  have hold (x : Fin n × Fin d) (hx : x ∈ edgeReps M) : m.M t (σ x.1) (σ (M.1 x).1) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hedge) x hx
  unfold weight
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun u hu => hπ _)
  · apply Finset.prod_ne_zero_iff.mpr
    intro x hx
    by_cases h1 : x.1 = v
    · simpa [h1] using hsafeL (Function.update σ v a₀ (M.1 x).1)
    · by_cases h2 : (M.1 x).1 = v
      · simpa [h1,h2] using hsafeR (σ x.1)
      · simpa [h1,h2] using hold x hx
