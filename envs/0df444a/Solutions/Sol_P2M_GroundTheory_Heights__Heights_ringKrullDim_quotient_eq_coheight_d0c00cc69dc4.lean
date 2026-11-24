-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_eq_coheight_d0c00cc69dc4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:05.362967+00:00
-- url     : https://prove2.me/submissions/1ecfaae3-6908-4645-ab2c-f467287f37ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_HeightCoheightQuotient

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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {B : Type*} [CommRing B] (P : Ideal B) [hP : P.IsPrime] :
    ringKrullDim (B ⧸ P) = Order.coheight (⟨P, hP⟩ : PrimeSpectrum B) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  have h : PrimeSpectrum.zeroLocus (P : Set B) = Set.Ici (⟨P, hP⟩ : PrimeSpectrum B) := by
    ext q
    rw [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici, ← PrimeSpectrum.asIdeal_le_asIdeal]
    exact SetLike.coe_subset_coe
  rw [h]
end GroundTheory.Heights₂.Heights
