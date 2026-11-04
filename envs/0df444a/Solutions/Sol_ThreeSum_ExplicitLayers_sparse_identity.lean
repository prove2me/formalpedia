-- Prove2me | solution 1 for ThreeSum.ExplicitLayers.sparse_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:59.074208+00:00
-- url     : https://prove2.me/submissions/472bffd8-c8e5-4db1-b7e5-6ca33e580c23

import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_ExplicitLayers
import Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_eq_explicit
import Theorems.Thm_ThreeSum_SparseBoxes_sparse_query_identity_enumerated


set_option autoImplicit false
open ThreeSum ThreeSum.ExplicitLayers
open Finset ThreeSum.SubsetAddress
open scoped BigOperators
namespace ThreeSum.ExplicitLayers
theorem _root_.solution {W : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) (t : ℕ) :
    (∑ S ∈ Q.powerset, weight S) = valueSum Q weight t+
      ∑ U ∈ Q.powersetCard t, SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight := by
  rw [valueSum_eq_explicit]
  exact SparseBoxes.sparse_query_identity_enumerated Q t weight
end ThreeSum.ExplicitLayers
