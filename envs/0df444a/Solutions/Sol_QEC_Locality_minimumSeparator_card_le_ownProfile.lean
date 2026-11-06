-- Prove2me | solution 1 for QEC.Locality.minimumSeparator_card_le_ownProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:29:17.195203+00:00
-- url     : https://prove2.me/submissions/1d6cc0ac-8703-4b15-9a1e-fa52fbc89292

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
import Theorems.Thm_QEC_Locality_minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile


set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (vertices separator : Finset ι)
    (hminimum :
      separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices) :
    separator.card ≤ twoThirdsSeparationProfile G vertices.card := by
  rw [hminimum]
  exact minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile
    G vertices.card vertices (Finset.subset_univ _) le_rfl
end QEC.Locality
