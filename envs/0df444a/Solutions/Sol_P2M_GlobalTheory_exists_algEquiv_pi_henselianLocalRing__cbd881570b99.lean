-- Prove2me | solution 1 for P2M_GlobalTheory_exists_algEquiv_pi_henselianLocalRing__cbd881570b99
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:53:14.494165+00:00
-- url     : https://prove2.me/submissions/ec5e947d-8c28-46ea-bdb1-b6e9f90c7b4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_finite_maximalSpectrum_of_finite_of_isLocalRing
import Theorems.Thm_GlobalTheory_finite_localization_of_henselian
import Theorems.Thm_GlobalTheory_henselianLocalRing_localization_of_henselian
import Theorems.Thm_GlobalTheory_bijective_toPiLocalization_of_henselian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
namespace exists_algEquiv_pi_henselianLocalRing
theorem _root_.solution.{v} (R : Type*) (S : Type v) [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] :
    ∃ (ι : Type v) (_ : Finite ι) (T : ι → Type v) (_ : ∀ i, CommRing (T i))
      (_ : ∀ i, Algebra R (T i)) (_ : S ≃ₐ[R] Π i, T i),
      ∀ i, HenselianLocalRing (T i) ∧ Module.Finite R (T i) :=
  ⟨MaximalSpectrum S, finite_maximalSpectrum_of_finite_of_isLocalRing R S,
    fun q ↦ Localization.AtPrime q.asIdeal, inferInstance, inferInstance,
    .ofBijective ((MaximalSpectrum.toPiLocalization S).restrictScalars R)
      (bijective_toPiLocalization_of_henselian R S),
    fun q ↦ have := q.isMaximal
      ⟨henselianLocalRing_localization_of_henselian R _, finite_localization_of_henselian R _⟩⟩
end exists_algEquiv_pi_henselianLocalRing
end GlobalTheory
