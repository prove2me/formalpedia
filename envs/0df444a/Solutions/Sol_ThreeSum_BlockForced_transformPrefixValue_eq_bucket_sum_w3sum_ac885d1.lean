-- Prove2me | solution 1 for ThreeSum.BlockForced.transformPrefixValue_eq_bucket_sum_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:17.230196+00:00
-- url     : https://prove2.me/submissions/c643a522-fda2-4ed8-9bf4-a1436835466f

import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Definitions.Def_Submission_ThreeSum_BlockForced
import Definitions.Def_WeightedCache3SUM_Alias_0c7e703d0de4ed4f
import Theorems.Thm_ThreeSum_BlockEncoding_leftWeights_cardinality
import Theorems.Thm_ThreeSum_BlockEncoding_rightWeights_cardinality
import Theorems.Thm_ThreeSum_BlockRows_forced_sizes
import Theorems.Thm_ThreeSum_BlockRows_join_disjoint_compl
import Theorems.Thm_ThreeSum_BlockRows_join_subset
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_4bfffe55ebbb2ee0
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.BlockForced
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.BlockForced
theorem _root_.solution {h J : ℕ} (P d : ℤ)
    (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h)))
    (hu : ∀ i ∈ I, u i ⊆ outputRows q i ∧ (u i).card = h) :
    transformPrefixValue P d B C b c q I u =
      (∑ t ∈ completedTuples q I u, leftBucket P B b t * rightBucket P d C c t : ℕ) := by
  have hQ : ∀ i, (outputRows q i).card = 2 * h :=
    fun i => LayerCounts.mem_vertices.mp (q i).2.property
  have he := Subset.forced_prefix_identity
    (fun S => (leftWeights (outputOccurrences q) P B b S : ℤ))
    (fun V => (rightWeights (outputOccurrences q) P d C c V : ℤ))
    (prefixLeft I u) (prefixRight I (outputRows q) u) (suffixDomain I)
    (remaining I (outputRows q)) (J * h) (J * h)
    (leftWeights_cardinality (outputOccurrences q) P B b)
    (rightWeights_cardinality (outputOccurrences q) P d C c)
    (join_disjoint_compl I u (fun _ => univ))
    (join_disjoint_compl I (fun i => outputRows q i \ u i) (fun _ => univ))
    (join_subset Iᶜ (fun _ _ => Finset.subset_univ _))
    (forced_sizes I (outputRows q) u hQ hu)
  rw [transformPrefixValue, he]
  exact_mod_cast (completed_bucket_sum P d B C b c q I u (fun i hi => (hu i hi).1)).symm
end ThreeSum.BlockForced
