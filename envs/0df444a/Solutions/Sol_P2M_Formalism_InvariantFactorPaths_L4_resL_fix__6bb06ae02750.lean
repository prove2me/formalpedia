-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_L4_resL_fix__6bb06ae02750
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:36.400809+00:00
-- url     : https://prove2.me/submissions/0b36e431-8767-4b66-a5de-88138c8de8e8

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution {σ : Type} (v : σ) (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ FreeOf p v) : resL p v 0 x = x := by
  have hx' : ↑x.support ⊆ {m : σ →₀ ℕ | m v = 0} := by
    have h' := hx
    simp only [FreeOf, MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported, Submodule.mem_comap,
      LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply] at h'
    exact h'
  change initPart v 0 x = x
  unfold initPart
  conv_rhs => rw [x.as_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [if_pos (show m v = 0 from hx' (Finset.mem_coe.mpr hm))]
end Formalism.InvariantFactorPaths.L4
