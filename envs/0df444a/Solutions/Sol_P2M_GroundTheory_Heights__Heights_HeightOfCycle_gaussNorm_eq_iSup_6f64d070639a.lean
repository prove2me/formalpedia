-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HeightOfCycle_gaussNorm_eq_iSup_6f64d070639a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:16.144833+00:00
-- url     : https://prove2.me/submissions/af8d9a4b-aae9-4d2b-82d1-5c0910dff22b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHeightOfCycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_gaussNormOf_eq_b0903c48cd28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_eq_gaussNormOf_d4ed71b31023
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_gaussNormOf_6379dd47bf35


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
open MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.HeightOfCycle
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.HeightOfCycle
theorem _root_.solution {ι : Type*} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {f : MvPolynomial ι K} (hf : f ≠ 0) (S : Finset (ι →₀ ℕ)) (hS : f.support ⊆ S) :
    gaussNorm v f = ⨆ m : S, FinitePlace.equivHeightOneSpectrum.symm v (f.coeff m) := by
  have e : ∀ m, FinitePlace.equivHeightOneSpectrum.symm v (f.coeff m) =
      NumberField.HeightOneSpectrum.adicAbv K v (f.coeff m) := fun m ↦ by
    rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  simp_rw [e]
  obtain ⟨m, hm, hmax⟩ := exists_gaussNormOf_eq (NumberField.HeightOneSpectrum.adicAbv K v) hf
  have : Nonempty S := ⟨⟨m, hS hm⟩⟩
  apply le_antisymm
  · rw [gaussNorm_eq_gaussNormOf, hmax]
    exact le_ciSup (f := fun m : S ↦ NumberField.HeightOneSpectrum.adicAbv K v (f.coeff m))
      (Set.finite_range _).bddAbove ⟨m, hS hm⟩
  · exact ciSup_le fun m ↦ le_gaussNormOf _ f m
end GroundTheory.Heights₂.Heights.HeightOfCycle
