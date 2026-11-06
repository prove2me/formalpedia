-- Prove2me | solution 2 for QEC.Locality.twoThirdsSeparationProfile_vertexRestricted_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:29:54.5032+00:00
-- url     : https://prove2.me/submissions/5d7edb40-5118-45fe-9024-7ac2759d93e9

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QLAux.minSize_restricted_le (G : ConnectivityGraph ι) (vertices W : Finset ι) :
    minimumTwoThirdsBalancedVertexSeparatorSize (vertexRestrictedGraph G vertices) W ≤
      minimumTwoThirdsBalancedVertexSeparatorSize G W := by
  have hmem := Finset.min'_mem (twoThirdsBalancedSeparatorCardinalities G W)
    (twoThirdsBalancedSeparatorCardinalities_nonempty G W)
  obtain ⟨sep, hsep, hcard⟩ := Finset.mem_image.1 hmem
  rw [mem_twoThirdsBalancedSeparatorCandidates_iff] at hsep
  obtain ⟨hsub, left, right, hp⟩ := hsep
  have hsep' : sep ∈ twoThirdsBalancedSeparatorCandidates (vertexRestrictedGraph G vertices) W := by
    rw [mem_twoThirdsBalancedSeparatorCandidates_iff]
    refine ⟨hsub, left, right, ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
    refine ⟨h1, h2, h3, h4, h5, ?_⟩
    intro x hx y hy hadj
    exact h6 hx hy hadj.2.2
  unfold minimumTwoThirdsBalancedVertexSeparatorSize
  rw [← hcard]
  exact Finset.min'_le _ _ (Finset.mem_image.2 ⟨sep, hsep', rfl⟩)

theorem solution
    (G : ConnectivityGraph ι) (vertices : Finset ι) (scale : Nat) :
    twoThirdsSeparationProfile (vertexRestrictedGraph G vertices) scale ≤
      twoThirdsSeparationProfile G scale := by
  unfold twoThirdsSeparationProfile
  apply Finset.max'_le
  intro y hy
  obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hy
  refine le_trans (QLAux.minSize_restricted_le G vertices W) ?_
  exact Finset.le_max' _ _ (Finset.mem_image.2 ⟨W, hW, rfl⟩)
