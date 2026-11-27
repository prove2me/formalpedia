-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ProjBundleDim_proof_a5bbf2a175d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:58:45.69413+00:00
-- url     : https://prove2.me/submissions/85e0b967-200f-4aac-8fe4-5237047b9fd3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_trdeg_projBundle_a12187b3c61c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_algebraMap_int_injective_bbfc0045ba62
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_rename_inlV_mem_projBundleIdeal_iff_c30f3fd57594


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
namespace ProjBundleDim
theorem _root_.solution (hInt : IntDomainDim.Statement) : ProjBundleDim.Statement := by
  intro K _ ι _ N1 n P d B hP hB
  obtain ⟨-, ⟨hPr, -, -⟩, hPz, -⟩ := hP
  have hHor : IsHorizontal (projBundleIdeal P B) := by
    ext z
    rw [Ideal.mem_comap, Ideal.mem_bot]
    constructor
    · intro h
      have h2 : (C z : MRing ι) ∈ P := (rename_inlV_mem_projBundleIdeal_iff P B (C z)).1 (by simpa using h)
      have h3 : z ∈ P.comap (C : ℤ →+* MRing ι) := h2
      rw [hPz] at h3
      exact h3
    · rintro rfl
      simp
  have hprime : (projBundleIdeal P B).IsPrime := RingHom.ker_isPrime _
  rw [hInt _ (algebraMap_int_injective _ hHor), hInt _ (algebraMap_int_injective P hPz),
    trdeg_projBundle P hPz B hB, map_add, map_natCast]
  push_cast
  ring
end ProjBundleDim
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
