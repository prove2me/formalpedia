-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ProjBundleArith_proof_b62405d0cbd6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:55.909811+00:00
-- url     : https://prove2.me/submissions/ee290e83-9ffa-40f9-a669-66a43c822c36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermOfIsPullHermInl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleArith
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_rename_inlV_mem_projBundleIdeal_iff_c30f3fd57594
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projBundleMap_X_inr_7730eace2592


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace ProjBundleArith
theorem _root_.solution (hMH : ProjBundleMultiHomog.Statement) (hDim : ProjBundleDim.Statement) :
    ProjBundleArith.Statement := by
  intro K _ ι _ N1 t P d c m B hP hQ hB
  have hP' := hP
  obtain ⟨hK, ⟨_, _, hPr⟩, hPz, hPd⟩ := hP
  have hmem := rename_inlV_mem_projBundleIdeal_iff P B
  refine ⟨inferInstance, ⟨RingHom.ker_isPrime _, hMH K ι N1 t 2 P d c m B hP' hQ hB, ?_⟩, ?_, ?_⟩
  · rintro (k | u)
    · obtain ⟨i, hi⟩ := hPr k
      refine ⟨i, fun h => hi ((hmem _).1 ?_)⟩
      simpa [inlV] using h
    · obtain ⟨j, hj⟩ := Function.ne_iff.mp (hB.1.ne_zero 0)
      refine ⟨j, fun h => hj ?_⟩
      have h' : projBundleMap P B (X ⟨Sum.inr u, j⟩) = 0 := h
      rw [projBundleMap_X_inr] at h'
      have := congrArg (coeff (Finsupp.single 0 1)) h'
      simpa [coeff_X, Finsupp.single_eq_single_iff] using this
  · ext z
    rw [Ideal.mem_comap, Ideal.mem_bot]
    constructor
    · intro h
      have h2 : (C z : MRing ι) ∈ P := (hmem (C z)).1 (by simpa using h)
      have h3 : z ∈ P.comap (C : ℤ →+* MRing ι) := h2
      rw [hPz] at h3
      exact h3
    · rintro rfl
      simp
  · rw [hDim K ι N1 2 P d B hP' hB.1, hPd, ← Nat.cast_add]
    congr 1
    simp [Fintype.card_sum]
    omega
end ProjBundleArith
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
