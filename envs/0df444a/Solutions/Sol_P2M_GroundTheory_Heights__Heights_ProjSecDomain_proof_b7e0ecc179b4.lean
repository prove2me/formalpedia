-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjSecDomain_proof_b7e0ecc179b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:07:39.177138+00:00
-- url     : https://prove2.me/submissions/e607324a-b405-4b81-98b2-e908ee970767

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjSecDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjSecDomain_chi_g_9edd29643ac0

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ProjSecDomain
variable {n e : ℕ} (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)
variable {W A}
variable (W A)
variable {W A}
variable (W A)
variable {W A}
namespace GroundTheory.Heights₂.Heights.ProjSecDomain
theorem _root_.solution : ProjSecDomain.Statement := by
  intro n e W A hW hA
  have hM : M W A ≤ nonZeroDivisors _ := by
    rintro _ ⟨p, hp, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero fun h =>
      nonZeroDivisors.ne_zero hp (hA.injective (by rw [map_zero]; exact h))
  have : IsDomain (T W A) := IsLocalization.isDomain_localization hM
  refine ⟨Function.Injective.isDomain (g W A) (Function.LeftInverse.injective chi_g), ?_⟩
  let _ : Algebra (MvPolynomial (Fin (e + 1)) ℂ) (MvPolynomial (Fin n) ℂ ⧸ W) :=
    (ComplexSets.projHom W A).toRingHom.toAlgebra
  have hint (j : Fin n) : IsIntegral (Kf e) (Ideal.Quotient.mk
      (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A)) (X j)) := by
    have := IsIntegral.map_of_comp_eq (algebraMap _ (Kf e)) (psi W A) psi_comp_projHom.symm
      (hA.finite.to_isIntegral (Ideal.Quotient.mk W (X j)))
    rwa [psi_mk, map_X] at this
  have : Algebra.IsIntegral (Kf e) (S W A) := ⟨fun s => by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
    induction f using MvPolynomial.induction_on with
    | C c => exact isIntegral_algebraMap
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p j hp => rw [map_mul]; exact hp.mul (hint j)⟩
  have : Algebra.FiniteType (Kf e) (S W A) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (Kf e) _)
      (Ideal.Quotient.mkₐ_surjective _ _)
  exact Algebra.IsIntegral.finite
end GroundTheory.Heights₂.Heights.ProjSecDomain
