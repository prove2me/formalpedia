-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_proof_a093d4456c45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:02:41.023872+00:00
-- url     : https://prove2.me/submissions/449eb9f9-07e4-487b-83d7-424293d9d613

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpenPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_lastRows_mulVec_e023a6c4759e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_firstPart_graphPt_177b1d982e4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphPt_natAdd_be63f7604ada
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_continuous_firstPart_81c0042172c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_isPrime_graphIdeal_6a8de62d33d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_ringKrullDim_graphIdeal_1956fa4ebe80
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphPt_mem_78c06350742c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_firstPart_mem_38bb86ee4503
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_natAdd_of_mem_4bb9909352d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_eq_graphPt_of_mem_4583e741b80e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Topology Filter Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
theorem _root_.solution (hOpen : IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpen.Statement) : IsolatedFibreOpenPoly.Statement := by
  intro n d P p x hP hdim hx ⟨W, hW, hiso⟩ W' hW'
  have hV : IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety (graphIdeal P p) d :=
    ⟨isPrime_graphIdeal hP p, by rw [ringKrullDim_graphIdeal]; exact hdim⟩
  have hAx : lastRows n d *ᵥ graphPt p x = fun i => eval x (p i) := by
    rw [lastRows_mulVec]
    funext i
    exact graphPt_natAdd p x i
  have hN : ∀ U ∈ 𝓝 x, firstPart ⁻¹' U ∈ 𝓝 (graphPt p x) := fun U hU =>
    continuous_firstPart.continuousAt.preimage_mem_nhds (by rw [firstPart_graphPt]; exact hU)
  have hisoG : ∀ z ∈ firstPart ⁻¹' W, z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p) →
      lastRows n d *ᵥ z = lastRows n d *ᵥ graphPt p x → z = graphPt p x := by
    intro z hzW hz hAz
    have hfz : firstPart z = x := by
      refine hiso _ ⟨firstPart_mem hz, hzW⟩ fun i => ?_
      have h := congrFun hAz i
      rw [lastRows_mulVec, lastRows_mulVec] at h
      simp only at h
      rw [natAdd_of_mem hz, graphPt_natAdd] at h
      exact h
    rw [eq_graphPt_of_mem hz, hfz]
  have h := hOpen (n + d) d (graphIdeal P p) (lastRows n d) (graphPt p x) hV (graphPt_mem p hx)
    ⟨firstPart ⁻¹' W, hN W hW, hisoG⟩ (firstPart ⁻¹' W') (hN W' hW')
  rw [hAx] at h
  refine Filter.mem_of_superset h ?_
  rintro _ ⟨z, ⟨hz, hzW'⟩, rfl⟩
  refine ⟨firstPart z, ⟨firstPart_mem hz, hzW'⟩, ?_⟩
  show (fun i => eval (firstPart z) (p i)) = lastRows n d *ᵥ z
  rw [lastRows_mulVec]
  funext i
  exact (natAdd_of_mem hz i).symm
end GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
