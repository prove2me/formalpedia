-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ChowNormFormGeneric_proof_fa4fec175ea3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:49:19.270097+00:00
-- url     : https://prove2.me/submissions/9011dd43-df7a-4b78-a875-f680bd005e8e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowNormFormGeneric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_genPar_algebraicIndependent_ebc49d3b0520
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_secCoord_adjoin_702b1310c2e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_secCoord_chart_58c3f1290d13

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace ChowNormFormGeneric
theorem _root_.solution (h₁ : SecAlgFinite.Statement) (h₂ : GenSecDomain.Statement)
    (h₃ : GenSecSeparable.Statement) (h₄ : ChowSecDvd.Statement)
    (h₅ : NormFormIrreducible.Statement) (h₆ : GenChowIrreducible.Statement)
    (h₇ : NormFormDvd.Statement) : ChowNormFormGeneric.Statement := by
  intro k _ _ n e Q g hQ hg
  have hfin := h₁ k (GenParField k e n) n e Q g (genPar k e n)
    (genPar_algebraicIndependent k e n) hQ hg
  refine ⟨hfin, ?_⟩
  have := h₂ k n e Q g hQ hg
  have := h₃ k n e Q g hQ hg
  have hirr := h₅ (GenParField k e n) (GenSec k e Q) n _ (fun j => genPar k e n (.inr j))
    (secCoord_adjoin _ _) (secCoord_chart _ _)
  obtain ⟨m, -, hm⟩ := h₄ k (GenParField k e n) n e Q g (genPar k e n) hQ hg
  have hd := h₇ (GenParField k e n) (GenSec k e Q) n _
    ((specRest (algebraMap k (GenParField k e n)) g (genPar k e n)) ^ m) (by rwa [map_pow])
  rw [← pow_mul] at hd
  obtain ⟨u, hu⟩ := hirr.prime.dvd_of_dvd_pow hd
  rcases (h₆ k n e Q g hQ hg).isUnit_or_isUnit hu with hN | hu'
  · exact absurd hN hirr.not_isUnit
  obtain ⟨c, hc, rfl⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp hu'
  exact ⟨c, hc.ne_zero, by rw [hu, mul_comm]⟩
end ChowNormFormGeneric
end GroundTheory.Heights₂.Heights.Vertical
