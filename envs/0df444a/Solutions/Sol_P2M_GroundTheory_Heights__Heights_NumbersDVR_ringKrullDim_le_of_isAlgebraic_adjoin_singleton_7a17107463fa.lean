-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_le_of_isAlgebraic_adjoin_singleton_7a17107463fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:53:06.963345+00:00
-- url     : https://prove2.me/submissions/b429f183-b279-472e-ad9e-1d0b6172db60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ComapLiftFormConstChartPrimeExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PComponentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTopDimMinimal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyDimensionInequality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_RingKrullDimLeOfIsAlgebraicAdjoinSingleton
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpModel_full_8b291331d559
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DimensionInequalityOneGenerator_full_2e439ceebee9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DimensionInequality_full_a7632a1120d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PolynomialDimensionInequality_full_3cc0f9177f7f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ReesAlgebraDim_full_2e5d789dbb84


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {A B : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B)) (y : B)
    [Algebra.IsAlgebraic (Algebra.adjoin A ({y} : Set B)) B] (N : ℕ)
    (hA : ringKrullDim A < (N : WithBot ℕ∞)) : ringKrullDim B ≤ (N : WithBot ℕ∞) := by
  rw [ringKrullDim_le_iff_height_le]
  intro 𝔓 h𝔓
  have key := DimensionInequality.full A B hinj 𝔓
  have htd : Algebra.trdeg A B ≤ 1 := by
    simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk A ({y} : Set B)
  have hp : (𝔓.under A).height + 1 ≤ (N : ℕ∞) := by
    have h1 := Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top (inferInstance :
      (𝔓.under A).IsPrime))
    have h2 : ((𝔓.under A).height : WithBot ℕ∞) < (N : WithBot ℕ∞) := h1.trans_lt hA
    have h3 : (𝔓.under A).height < (N : ℕ∞) := by exact_mod_cast h2
    exact Order.add_one_le_of_lt h3
  have hc : Cardinal.ofENat 𝔓.height ≤ Cardinal.ofENat (N : ℕ∞) := by
    calc Cardinal.ofENat 𝔓.height
        ≤ Cardinal.ofENat 𝔓.height + Algebra.trdeg (A ⧸ 𝔓.under A) (B ⧸ 𝔓) := le_self_add
      _ ≤ Cardinal.ofENat (𝔓.under A).height + Algebra.trdeg A B := key
      _ ≤ Cardinal.ofENat (𝔓.under A).height + 1 := by gcongr
      _ = Cardinal.ofENat ((𝔓.under A).height + 1) := by simp
      _ ≤ Cardinal.ofENat (N : ℕ∞) := Cardinal.ofENat_le_ofENat.mpr hp
  exact_mod_cast Cardinal.ofENat_le_ofENat.mp hc
end GroundTheory.Heights₂.Heights.NumbersDVR
