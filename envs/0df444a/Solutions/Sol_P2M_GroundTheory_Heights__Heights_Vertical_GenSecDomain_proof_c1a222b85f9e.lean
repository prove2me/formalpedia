-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_proof_c1a222b85f9e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:01.161488+00:00
-- url     : https://prove2.me/submissions/1c812c3a-3ef5-4e23-a16f-9c532b885176

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_exists_point_c551114588d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_secR_isDomain_c132ea3486ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_map_secIdeal_f302b2e73333

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
open MvPolynomial
noncomputable section
open GenSecDomain
namespace GroundTheory.Heights₂.Heights.Vertical
namespace GenSecDomain
theorem _root_.solution (h₁ : ChartDomain.Statement) (h₂ : IncidenceGeneric.Statement)
    (h₃ : IncIdealBelow.Statement) : GenSecDomain.Statement := by
  intro k _ n e Q g hQ hg
  obtain ⟨Ω, _, Ψ, hinj, hΨ⟩ := exists_point h₂ h₃ Q e g hQ hg
  have := secR_isDomain h₁ Q e hQ Ψ hΨ
  have hJ := map_secIdeal Q e
  let M : Submonoid (MvPolynomial (Fin n) (MvPolynomial (Par e n) k)) :=
    (nonZeroDivisors (MvPolynomial (Par e n) k)).map
      (C : MvPolynomial (Par e n) k →+* MvPolynomial (Fin n) (MvPolynomial (Par e n) k))
  let φ : SecR Q e →+* GenSec k e Q :=
    Ideal.quotientMap _ (MvPolynomial.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n)))
      (hJ ▸ Ideal.le_comap_map)
  let := φ.toAlgebra
  let : Algebra (MvPolynomial (Fin n) (MvPolynomial (Par e n) k)) (MvPolynomial (Fin n) (GenParField k e n)) :=
    MvPolynomial.algebraMvPolynomial
  have := MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors (MvPolynomial (Par e n) k))
    (GenParField k e n)
  have key := IsLocalization.of_surjective M
    (MvPolynomial (Fin n) (GenParField k e n)) (S' := GenSec k e Q)
    (Ideal.Quotient.mk (secIdeal (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
      (X : Par e n → MvPolynomial (Par e n) k))) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n))))
      (genPar k e n))) Ideal.Quotient.mk_surjective
    (Ideal.quotientMap_comp_mk _).symm
    (by rw [Ideal.mk_ker, Ideal.mk_ker, ← hJ]; rfl)
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (GenSec k e Q)
    (M := M.map (Ideal.Quotient.mk (secIdeal (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
      (X : Par e n → MvPolynomial (Par e n) k)))) ?_
  rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => nonZeroDivisors.ne_zero hr (hinj ?_)
  rw [map_zero]
  exact (congrArg Ψ h0).trans (map_zero Ψ)
end GenSecDomain
end GroundTheory.Heights₂.Heights.Vertical
