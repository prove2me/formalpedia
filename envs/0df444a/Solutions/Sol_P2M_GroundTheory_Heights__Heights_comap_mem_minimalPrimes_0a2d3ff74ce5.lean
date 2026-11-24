-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_comap_mem_minimalPrimes_0a2d3ff74ce5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:53.142906+00:00
-- url     : https://prove2.me/submissions/9638584a-dcb8-424a-9615-a491f5c932cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFundCycleBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMinimalPrimeComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFundCycleBaseChange

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
theorem _root_.solution {J : Ideal A} {P : Ideal B} (hP : P ∈ (J.map f).minimalPrimes) :
    P.comap f ∈ J.minimalPrimes ∧ P ∈ ((P.comap f).map f).minimalPrimes := by
  have hPp : P.IsPrime := hP.1.1
  obtain ⟨W₀, hW₀, hW₀le⟩ :=
    Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mp hP.1.2)
  have hW₀p : W₀.IsPrime := hW₀.1.1
  obtain ⟨P₀, hP₀, hP₀le⟩ :=
    Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mpr hW₀le)
  have hP₀p : P₀.IsPrime := hP₀.1.1
  have hEq : P₀ = P :=
    le_antisymm hP₀le (hP.2 ⟨hP₀p, (Ideal.map_mono hW₀.1.2).trans hP₀.1.2⟩ hP₀le)
  subst hEq
  rw [hc W₀ hW₀p P₀ hP₀]
  exact ⟨hW₀, hP₀⟩
end GroundTheory.Heights₂.Heights
