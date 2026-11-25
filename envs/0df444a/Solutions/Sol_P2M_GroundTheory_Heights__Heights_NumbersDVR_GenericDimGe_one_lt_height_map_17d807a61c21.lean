-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_one_lt_height_map_17d807a61c21
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:24:31.150778+00:00
-- url     : https://prove2.me/submissions/0d37e1d2-00ea-485a-adb0-756301e4b081

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericDimGe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_map_mk_lt_4b93d3dede51

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
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
theorem _root_.solution {p a b : Ideal R} [p.IsPrime] [a.IsPrime] [b.IsPrime] (hpa : p < a)
    (hab : a < b) : 1 < (b.map (Ideal.Quotient.mk p)).height := by
  have hk : ∀ c : Ideal R, p ≤ c → RingHom.ker (Ideal.Quotient.mk p) ≤ c := fun c hc => by
    rw [Ideal.mk_ker]; exact hc
  have := Ideal.map_isPrime_of_surjective (I := p) Ideal.Quotient.mk_surjective (hk p le_rfl)
  have := Ideal.map_isPrime_of_surjective (I := a) Ideal.Quotient.mk_surjective (hk a hpa.le)
  have := Ideal.map_isPrime_of_surjective (I := b) Ideal.Quotient.mk_surjective
    (hk b (hpa.trans hab).le)
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (map_mk_lt le_rfl hpa)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (map_mk_lt hpa.le hab)
  have h3 : (1 : ℕ∞) ≤ (a.map (Ideal.Quotient.mk p)).height := le_trans le_add_self h1
  have h4 : (1 : ℕ∞) + 1 ≤ (b.map (Ideal.Quotient.mk p)).height :=
    le_trans (add_le_add h3 le_rfl) h2
  exact lt_of_lt_of_le (by norm_num) h4
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
