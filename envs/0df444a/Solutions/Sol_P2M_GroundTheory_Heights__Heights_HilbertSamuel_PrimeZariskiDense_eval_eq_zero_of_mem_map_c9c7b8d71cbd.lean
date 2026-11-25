-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeZariskiDense_eval_eq_zero_of_mem_map_c9c7b8d71cbd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:00.21673+00:00
-- url     : https://prove2.me/submissions/6c8951d4-6c8f-4279-9694-c7a28874f06a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPrimeZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexFormsOnPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPrimeComplexRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexMinimalPrimesContract
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPrimeZariskiDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace PrimeZariskiDense
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) {F : MvPolynomial (Σ k, ι k) ℂ}
    (hF : F ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ))) : eval z F = 0 := by
  have hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker (eval z) := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact hz.2 f hf
  exact RingHom.mem_ker.mp (hle hF)
end PrimeZariskiDense
end GroundTheory.Heights₂.Heights.HilbertSamuel
