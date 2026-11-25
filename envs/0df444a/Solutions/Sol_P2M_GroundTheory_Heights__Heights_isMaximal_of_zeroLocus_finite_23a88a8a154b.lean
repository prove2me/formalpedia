-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isMaximal_of_zeroLocus_finite_23a88a8a154b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:55.115826+00:00
-- url     : https://prove2.me/submissions/e59f8cfa-cbfe-402b-a096-993b12de4172

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFiniteFibresDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMaximalIdealHeightFG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFiniteFibresDimLe

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
theorem _root_.solution {n : ℕ} (P : Ideal (MvPolynomial (Fin n) ℂ)) [hP : P.IsPrime]
    (hfin : (zeroLocus ℂ P : Set (Fin n → ℂ)).Finite) : P.IsMaximal := by
  have hle : (hfin.toFinset.inf fun z => vanishingIdeal ℂ ({z} : Set (Fin n → ℂ))) ≤ P := by
    intro q hq
    rw [← IsPrime.vanishingIdeal_zeroLocus (K := ℂ) P, mem_vanishingIdeal_iff]
    intro z hz
    have hq' := (Finset.inf_le (f := fun z => vanishingIdeal ℂ ({z} : Set (Fin n → ℂ)))
      (hfin.mem_toFinset.2 hz)) hq
    exact (mem_vanishingIdeal_iff.1 hq') z rfl
  obtain ⟨z, -, hz⟩ := hP.inf_le'.1 hle
  have hmax : (vanishingIdeal ℂ ({z} : Set (Fin n → ℂ))).IsMaximal :=
    isMaximal_iff_eq_vanishingIdeal_singleton.2 ⟨z, rfl⟩
  rwa [← hmax.eq_of_le hP.ne_top hz]
end GroundTheory.Heights₂.Heights
