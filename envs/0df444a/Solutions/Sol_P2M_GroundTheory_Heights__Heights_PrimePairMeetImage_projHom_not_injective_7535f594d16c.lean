-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PrimePairMeetImage_projHom_not_injective_7535f594d16c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:07:30.066056+00:00
-- url     : https://prove2.me/submissions/f63aacea-5b36-4af5-8544-13af1b03fb36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimePairMeetImage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFiniteFibresDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PImageDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBadSetSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_HeightCoheightQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPrimePairMeetImage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_BadSetSmaller_proof_2a2d0eb10d77
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ImageDimLe_proof_3abb98a6e401
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_eq_coheight_d0c00cc69dc4


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace PrimePairMeetImage
theorem _root_.solution (hF : FiniteFibresDimLe.Statement) {n d : ℕ}
    {Q Q' P : Ideal (MvPolynomial (Fin n) ℂ)} (A : Matrix (Fin d) (Fin n) ℂ) (hQ : Q.IsPrime)
    (hQ' : Q'.IsPrime) (hne : Q ≠ Q') (hfin : ∀ y, (ComplexSets.fibre Q A y).Finite)
    (hfin' : ∀ y, (ComplexSets.fibre Q' A y).Finite) (hP : P.IsPrime) (hle : Q ⊔ Q' ≤ P) :
    ¬ Function.Injective (ComplexSets.projHom P A) := by
  intro hinj
  obtain ⟨R, hR, hRfin, hlt⟩ :
      ∃ R : Ideal (MvPolynomial (Fin n) ℂ), R.IsPrime ∧ (∀ y, (ComplexSets.fibre R A y).Finite) ∧ R < P := by
    by_cases h : Q = P
    · refine ⟨Q', hQ', hfin', lt_of_le_of_ne (le_sup_right.trans hle) ?_⟩
      intro h'
      exact hne (h.trans h'.symm)
    · exact ⟨Q, hQ, hfin, lt_of_le_of_ne (le_sup_left.trans hle) h⟩

  have hlow : ((d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) := by
    have h := ImageDimLe.proof n d P (ComplexSets.linPoly A) hP
    have hker : RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval (ComplexSets.linPoly A))) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).1 hinj
    rw [hker, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    simpa using h

  have hup := hF n d R A hR hRfin
  have hdrop := Order.coheight_add_one_le (a := (⟨P, hP⟩ : PrimeSpectrum (MvPolynomial (Fin n) ℂ)))
    (b := ⟨R, hR⟩) hlt
  rw [ringKrullDim_quotient_eq_coheight] at hlow hup
  have h1 : ((d : ℕ) : ℕ∞) ≤ Order.coheight (⟨P, hP⟩ : PrimeSpectrum (MvPolynomial (Fin n) ℂ)) := by
    exact_mod_cast hlow
  have h2 : Order.coheight (⟨R, hR⟩ : PrimeSpectrum (MvPolynomial (Fin n) ℂ)) ≤ ((d : ℕ) : ℕ∞) := by
    exact_mod_cast hup
  have h3 := (add_le_add h1 (le_refl (1 : ℕ∞))).trans (hdrop.trans h2)
  exact lt_irrefl _ ((ENat.add_one_le_iff (ENat.natCast_ne_top d)).1 h3)
end PrimePairMeetImage
end GroundTheory.Heights₂.Heights
