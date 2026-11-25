-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DivisorBranches_quotient_inf_dim_lt_0a71c29a111f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:34.575568+00:00
-- url     : https://prove2.me/submissions/581801df-1354-4e4e-adac-782b3cc49e95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorRegularGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDivisorChartGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDoublePointsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPointBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDivisorBranches

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
open MvPolynomial Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.DivisorBranches
namespace GroundTheory.Heights₂.Heights.DivisorBranches
theorem _root_.solution {R : Type*} [CommRing R] {I₁ I₂ : Ideal R} {d : ℕ}
    (h₁ : ringKrullDim (R ⧸ I₁) < (d : ℕ)) (h₂ : ringKrullDim (R ⧸ I₂) < (d : ℕ)) :
    ringKrullDim (R ⧸ (I₁ ⊓ I₂)) < (d : ℕ) := by
  rw [ringKrullDim_quotient] at h₁ h₂ ⊢
  rw [Order.krullDim_lt_coe_iff] at h₁ h₂ ⊢
  intro l
  have hhead : l.head.1 ∈ PrimeSpectrum.zeroLocus (I₁ : Set R) ∪ PrimeSpectrum.zeroLocus (I₂ : Set R) := by
    rw [← PrimeSpectrum.zeroLocus_inf]
    exact l.head.2
  have hup : ∀ (I : Ideal R), l.head.1 ∈ PrimeSpectrum.zeroLocus (I : Set R) →
      ∀ i, (l i).1 ∈ PrimeSpectrum.zeroLocus (I : Set R) := fun I hI i =>
    (PrimeSpectrum.mem_zeroLocus _ _).2
      (((PrimeSpectrum.mem_zeroLocus _ _).1 hI).trans (show l.head.1.asIdeal ≤ (l i).1.asIdeal from l.head_le i))
  rcases hhead with h | h
  · exact h₁ { length := l.length, toFun := fun i => ⟨(l i).1, hup I₁ h i⟩, step := fun i => l.step i }
  · exact h₂ { length := l.length, toFun := fun i => ⟨(l i).1, hup I₂ h i⟩, step := fun i => l.step i }
end GroundTheory.Heights₂.Heights.DivisorBranches
