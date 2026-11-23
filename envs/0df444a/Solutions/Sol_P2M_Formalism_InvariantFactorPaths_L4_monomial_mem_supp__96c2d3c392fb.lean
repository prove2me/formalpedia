-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_L4_monomial_mem_supp__96c2d3c392fb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:49.436794+00:00
-- url     : https://prove2.me/submissions/eabea02f-2625-433c-9b5c-486a6bc4cffe

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
theorem _root_.solution {σ : Type} (Q : Set (σ →₀ ℕ)) (m : σ →₀ ℕ) (hm : m ∈ Q) :
    monomial m (1 : ℚ_[p]) ∈ restrictSupport ℚ_[p] Q := by
  simp only [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported, Submodule.mem_comap,
      LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply]
  intro n hn
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset (show n ∈ (monomial m (1 : ℚ_[p])).support from hn))]
  exact hm
end Formalism.InvariantFactorPaths.L4
