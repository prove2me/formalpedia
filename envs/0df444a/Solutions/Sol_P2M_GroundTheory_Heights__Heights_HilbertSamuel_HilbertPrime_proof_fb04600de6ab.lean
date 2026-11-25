-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertPrime_proof_fb04600de6ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:15.875866+00:00
-- url     : https://prove2.me/submissions/54160895-4ae2-4546-b72f-e0ba1944f091

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_hilbertPrime_succ_c5af2ec32262

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace HilbertPrime
theorem _root_.solution (hZ : HilbertDimZero.Statement.{u}) (hI : HilbertIncrement.Statement.{u})
    (hM : MixedNumberPolynomial.Statement.{u}) (hMP : ModulesFromPrimes.Statement.{u, u}) :
    HilbertPrime.Statement.{u} := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    cases d with
    | zero =>
      intro F _ K _ _ ι _ q hq hdim
      obtain ⟨a₀, ha₀⟩ := hZ F K ι q hq (by simpa using hdim)
      refine ⟨a₀, 0, fun a ha => ?_⟩
      have hfun : (fun _ : Fin 0 => fun k => (a k : ℤ)) = (![] : Fin 0 → K → ℤ) :=
        Subsingleton.elim _ _
      rw [hfun, ha₀ a ha]
      simp
    | succ d =>
      exact hilbertPrime_succ d hM hI (hMP d (fun e he => ih e (by omega)))
end HilbertPrime
end GroundTheory.Heights₂.Heights.HilbertSamuel
