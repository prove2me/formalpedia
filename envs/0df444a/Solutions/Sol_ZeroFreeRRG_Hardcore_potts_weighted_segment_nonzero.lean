-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_weighted_segment_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:23:46.905205+00:00
-- url     : https://prove2.me/submissions/750a0b90-1353-4ef3-a528-5f845dbb83be

import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_local_phase_step
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_joint_induction
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q)
    (V : Type) [Fintype V] (G : SimpleGraph V) (hG : ∀ v, G.degree v ≤ d)
    (β : ℂ) (hβ : ‖β-1‖ < 0.35/(d:ℝ))
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (hseg : ∀ e ∈ G.edgeFinset, ∀ i j, ∃ t : ℝ, t ∈ Icc 0 1 ∧ W e i j = 1+(t:ℂ)*(β-1))
    (S : Finset V) (τ : V → Fin q) : pottsWeightedPartial q G W hW S τ ≠ 0 := by
  classical
  have hstep (T : Finset V) := potts_local_phase_step d q hd hq V G hG β hβ T
  have hh := potts_joint_induction d q hd hq V G β hβ hstep S
  exact hh.1 W hW hseg τ
