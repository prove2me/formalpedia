-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.pinned_likelihood_density
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:12:40.917753+00:00
-- url     : https://prove2.me/submissions/0eedaa38-79d2-433b-83d2-7d40caea7f74

import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (t : ℝ) (d n : ℕ) (M : Matching n d)
    (σ : Fin n → m.Spin) (U : Finset (Fin n))
    (hπ : ∀ a, 0 < m.pi t a) (hG : 0 < gibbsMarg m t M σ U) :
    Real.exp (pinnedLL m t M σ U) =
      gibbsMarg m t M σ U / ∏ v ∈ U, m.pi t (σ v) := by
  unfold pinnedLL
  rw [Real.exp_sub, Real.exp_log hG, Real.exp_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  exact Real.exp_log (hπ (σ v))
