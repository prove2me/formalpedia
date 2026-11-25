-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prod_tuple_1b1f6df7d3f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:14.95896+00:00
-- url     : https://prove2.me/submissions/c88584ba-cdd6-4fd6-a1b4-888df030ee5b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ZetaSevenHalves
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid
noncomputable section
open GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
theorem _root_.solution {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : ∏ j, tuple K I j = absNorm I := by
  classical
  unfold tuple
  rw [Finset.prod_comm]
  simp only [Finset.prod_ite_eq, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.prod_multiset_map_count, ← map_multiset_prod,
    associated_iff_eq.mp (prod_normalizedFactors hI)]
end GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
