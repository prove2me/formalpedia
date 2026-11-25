-- Prove2me | solution 1 for PI.VolStabW.FiniteFieldSplitting.gram_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:04:20.328802+00:00
-- url     : https://prove2.me/submissions/932e37f6-a0dc-4761-9579-6912ae94e968

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
import Theorems.Thm_PI_VolStabW_FiniteFieldSplitting_ffH_fst
import Theorems.Thm_PI_VolStabW_FiniteFieldSplitting_ffH_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k] {M a : ℕ}
namespace PI.VolStabW.FiniteFieldSplitting
theorem _root_.solution (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j)
    (X : Fin a → Fin M → k × k) :
    ffGram (swapR k) J X = T ↔
      V1 X * J.map Prod.fst * (U1 X)ᵀ = T.map Prod.fst := by
  have key : ∀ r s, (ffGram (swapR k) J X r s).1 = (V1 X * J.map Prod.fst * (U1 X)ᵀ) r s := by
    intro r s
    simp only [ffGram, ffH_fst, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, U1,
      V1, Finset.sum_mul]
    exact Finset.sum_comm
  have key2 : ∀ r s, (ffGram (swapR k) J X r s).2 = (ffGram (swapR k) J X s r).1 := by
    intro r s
    simp only [ffGram, ffH_fst, ffH_snd]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    have h1 : (J j i).2 = (J i j).1 := by
      have := congrArg Prod.fst (hJ i j)
      simpa using this
    rw [h1]
    ring
  constructor
  · intro h
    ext r s
    rw [← key, h]
    rfl
  · intro h
    funext r s
    refine Prod.ext ?_ ?_
    · rw [key, h]
      rfl
    · rw [key2, key, h, Matrix.map_apply]
      have := congrArg Prod.fst (hT s r)
      simpa using this.symm
end PI.VolStabW.FiniteFieldSplitting
