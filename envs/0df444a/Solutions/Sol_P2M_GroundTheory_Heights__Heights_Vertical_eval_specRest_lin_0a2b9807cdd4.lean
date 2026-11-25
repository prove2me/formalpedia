-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_eval_specRest_lin_0a2b9807cdd4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:24:37.075683+00:00
-- url     : https://prove2.me/submissions/9c28cd67-3b16-4a64-8f22-72d84af85a48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormIdentity
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_kToFrac_algebraMap_0a543f23bec3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) (u : Fin n → 𝓞 K) :
    eval (fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j)))
        (specRest (kToFrac K e n) (g.map (algebraMap (𝓞 K) K)) (parYF K e n)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (rename Sum.inl (specFirst g u)) := by
  have h : ((eval fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j))).comp
      ((eval₂Hom (C.comp (kToFrac K e n)) (fun ij => Fin.cases
        (motive := fun _ => MvPolynomial (Fin n) (ParFrac K e n)) (X ij.2)
        (fun i => C (parYF K e n (.inl (i, ij.2)))) ij.1)).comp (map (algebraMap (𝓞 K) K)))) =
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n)).comp
        ((rename (Sum.inl : Fin e × Fin n → Par e n)).toRingHom.comp (bind₁ (specFirstVar u)).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun ij => ?_)
    · simp [kToFrac_algebraMap]
    · rcases ij with ⟨i, j⟩
      induction i using Fin.cases <;> simp [specFirstVar, parYF, kToFrac_algebraMap]
  exact congrArg (fun φ => φ g) h
end GroundTheory.Heights₂.Heights.Vertical
