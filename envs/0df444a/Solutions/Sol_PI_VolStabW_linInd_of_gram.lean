-- Prove2me | solution 1 for PI.VolStabW.linInd_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:03:56.426749+00:00
-- url     : https://prove2.me/submissions/5bd413fa-c037-4a4a-9f24-eff67595305e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_HformSmulLeft
import Theorems.Thm_PI_VolStabW_hSes_apply

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
variable {E : Type} [Field E] {M : ℕ}
variable [StarRing E]
namespace PI.VolStabW
theorem _root_.solution (J : Matrix (Fin M) (Fin M) E) {a : ℕ} (X : Fin a → Fin M → E)
    (G : Matrix (Fin a) (Fin a) E) (hG : ∀ i j, G i j = Formalism.UG.hform (starRingEnd E) J (X i) (X j))
    (hdet : G.det ≠ 0) : LinearIndependent E X := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 : G *ᵥ c = 0 := by
    funext j
    have := congrArg (hSes J (X j)) hc
    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at this
    simp only [mulVec, dotProduct, Pi.zero_apply, hG]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hSes_apply]
    ring
  intro i
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet h1) i
end PI.VolStabW
