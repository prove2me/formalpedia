-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_FibreCompDim_proof_408f77c658d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:25:16.754805+00:00
-- url     : https://prove2.me/submissions/c42ac84a-c0ba-4d94-ba19-ca2228c1d64a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCompDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PFibreCompDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_exists_ringKrullDim_quotient_eq_nat_52c672d92a95

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
open MvPolynomial IsDedekindDomain
namespace GroundTheory.Heights₂.Heights.Vertical
namespace FibreCompDim
theorem _root_.solution (hBase : FibreClosedComponent.Statement) (hCut : FibreCut.Statement)
    (hDrop : GenericFibreDrop.Statement) : FibreCompDim.Statement := by
  intro O _ _ F _ _ _ n P W v hP hPC hW
  have key : ∀ (m : ℕ) (P W : Ideal (MvPolynomial (Fin n) O)), P.IsPrime →
      P.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ →
      W ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes →
      ringKrullDim (MvPolynomial (Fin n) O ⧸ W) = m →
      ringKrullDim (MvPolynomial (Fin n) O ⧸ W) =
        ringKrullDim (MvPolynomial (Fin n) F ⧸ P.map (MvPolynomial.map (algebraMap O F))) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro P W hP hPC hW hm
    by_cases hmax : W.IsMaximal
    · rw [hBase O F n P W v hP hPC hW hmax]
      let _ := Ideal.Quotient.field W
      exact ringKrullDim_eq_zero_of_field _
    · obtain ⟨P', W', f, hfP, hP', hP'C, hW', hdim⟩ := hCut O n P W v hP hPC hW hmax
      have : W'.IsPrime := hW'.1.1
      have : P'.IsPrime := hP'.1.1
      obtain ⟨m', hm'⟩ := exists_ringKrullDim_quotient_eq_nat v W' hW'.1.1
        (le_sup_right.trans hW'.1.2)
      have hmm : m' + 1 = m := by
        rw [hm', hm] at hdim
        exact_mod_cast hdim
      rw [hDrop O F n P P' f hP hP'C hfP hP', ← ih m' (by omega) P' W' hP'.1.1 hP'C hW' hm', hdim]
  have : W.IsPrime := hW.1.1
  obtain ⟨m, hm⟩ := exists_ringKrullDim_quotient_eq_nat v W hW.1.1 (le_sup_right.trans hW.1.2)
  rw [← ringKrullDim_eq_of_ringEquiv (quotientResidueEquiv v W (le_sup_right.trans hW.1.2))]
  exact key m P W hP hPC hW hm
end FibreCompDim
end GroundTheory.Heights₂.Heights.Vertical
