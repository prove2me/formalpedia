-- Prove2me | solution 1 for QEC.Semantics.Davies.weightedJump_dissipator_apply
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T14:42:20.147695+00:00
-- url     : https://prove2.me/submissions/6339ca08-4c0d-4de2-9595-fe49a0f38dd2

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_Davies_weightedJump_term
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem solution {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (A : κ → Operator V)
    (rate : κ → Frequency e → ℝ) (hn : ∀ a w, 0 ≤ rate a w) (F : Operator V) :
    lindbladDissipator (weightedJump b e A rate) F =
      ∑ a, ∑ w : Frequency e, (rate a w : ℂ) •
        lindbladJumpTerm (frequencyComponent b e (A a) w.val) F := by
  rw [lindbladDissipator_apply, Fintype.sum_prod_type]
  simp only [weightedJump_term b e A rate hn]
