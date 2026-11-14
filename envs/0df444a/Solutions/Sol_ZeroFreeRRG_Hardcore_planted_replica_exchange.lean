-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.planted_replica_exchange
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:08:18.183216+00:00
-- url     : https://prove2.me/submissions/a0857ec0-284a-4f75-a4be-1a639722be8d

import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (t : ℝ) (d n : ℕ)
    (M : Matching n d) (σ σ' : Fin n → m.Spin) :
    planted m t M σ * gibbs m t M σ' = planted m t M σ' * gibbs m t M σ := by
  unfold planted gibbs
  simp only [div_eq_mul_inv]
  ring
