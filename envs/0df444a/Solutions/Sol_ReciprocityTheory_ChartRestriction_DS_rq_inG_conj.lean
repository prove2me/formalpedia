-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rq_inG_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:55.253878+00:00
-- url     : https://prove2.me/submissions/e3961082-191e-43e5-be2e-05d1b547dddc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_K_JH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : inG ε (k * X * kᴴ) := by
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have hc : k * Jm ε = Jm ε * k := hk.2
  have hc' := rq_K_JH hk
  show (k * X * kᴴ)ᴴ * Jm ε + Jm ε * (k * X * kᴴ) = 0
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc _ = k * (Xᴴ * Jm ε + Jm ε * X) * kᴴ := by
        rw [mul_add, add_mul]
        simp only [mul_assoc]
        rw [hc', ← mul_assoc (Jm ε) k, ← hc, mul_assoc]
    _ = 0 := by rw [hX', mul_zero, zero_mul]
end ReciprocityTheory.ChartRestriction.DS
