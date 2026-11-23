-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_L4_fock_monomial_zero__a5d7011b8429
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:49.017304+00:00
-- url     : https://prove2.me/submissions/17737ff6-8a64-47b8-88ce-896d3537dc3d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution {σ : Type} (g : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ) (hm : m ∉ g.support) :
    fock p g (monomial m 1) = 0 := by
  classical
  unfold fock
  refine Finset.sum_eq_zero (fun n hn => ?_)
  have hne : m ≠ n := fun h => hm (by rw [h]; exact hn)
  rw [MvPolynomial.coeff_monomial, if_neg hne, mul_zero, zero_mul]
end Formalism.InvariantFactorPaths.L4
