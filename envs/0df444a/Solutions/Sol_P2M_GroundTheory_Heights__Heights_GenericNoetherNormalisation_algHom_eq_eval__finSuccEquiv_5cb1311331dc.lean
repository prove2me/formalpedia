-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_algHom_eq_eval__finSuccEquiv_5cb1311331dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:55:10.616189+00:00
-- url     : https://prove2.me/submissions/f1711ffd-7500-4827-ae4e-7248a93712f0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericNoetherNormalisation
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumRMulNe
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProofSimp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericNoetherNormalisation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_add_1bf00d984f76

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Polynomial MvPolynomial Ideal Nat RingHom List
open GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
namespace GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
theorem _root_.solution {A D : Type*} [CommRing A] [CommRing D] [Algebra A D] {n : ℕ}
    (ψ : MvPolynomial (Fin (n + 1)) A →ₐ[A] D) (P : MvPolynomial (Fin (n + 1)) A) :
    ψ P = (finSuccEquiv A n P).eval₂
      (MvPolynomial.aeval (R := A) (fun i : Fin n ↦ ψ (X i.succ))).toRingHom (ψ (X 0)) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add P Q hP hQ => rw [map_add, map_add, Polynomial.eval₂_add, hP, hQ]
  | mul_X P i ih =>
    rw [map_mul, map_mul, Polynomial.eval₂_mul, ih]
    congr 1
    cases i using Fin.cases <;> simp [finSuccEquiv_X_zero, finSuccEquiv_X_succ]
end GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
