-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_map_a70e80c1c816
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:35:21.773306+00:00
-- url     : https://prove2.me/submissions/dda68600-acda-4069-861c-000a1fb96946

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFundCycleBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMinimalPrimeComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFundCycleBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_comap_mem_minimalPrimes_0a2d3ff74ce5

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
variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
  (hc : ∀ I : Ideal A, I.IsPrime → ∀ P ∈ (I.map f).minimalPrimes, P.comap f = I)
include hc
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {J W : Ideal A} (hW : W ∈ J.minimalPrimes) {P : Ideal B}
    (hP : P ∈ (W.map f).minimalPrimes) : P ∈ (J.map f).minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  have hPp : P.IsPrime := hP.1.1
  refine ⟨⟨hPp, (Ideal.map_mono hW.1.2).trans hP.1.2⟩, fun Q hQ hQP => ?_⟩
  have hQp : Q.IsPrime := hQ.1
  obtain ⟨Q₀, hQ₀, hQ₀le⟩ := Ideal.exists_minimalPrimes_le hQ.2
  obtain ⟨h1, -⟩ := comap_mem_minimalPrimes f hc hQ₀
  have hle : Q₀.comap f ≤ W := by
    rw [← hc W hWp P hP]
    exact Ideal.comap_mono (hQ₀le.trans hQP)
  have hWQ : W ≤ Q₀.comap f := hW.2 h1.1 hle
  have hQ₀p : Q₀.IsPrime := hQ₀.1.1
  exact (hP.2 ⟨hQ₀p, Ideal.map_le_iff_le_comap.mpr hWQ⟩ (hQ₀le.trans hQP)).trans hQ₀le
end GroundTheory.Heights₂.Heights
