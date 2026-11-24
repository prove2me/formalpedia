-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:39.105546+00:00
-- url     : https://prove2.me/submissions/3ff35146-7b1b-4943-8730-868d757f890b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ReachableFixingAddSmulSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ExistsMaxOfNotCoprime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_HfDecompSelf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_sub_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution (b : ι → K) :
    hf σ J (b - hf σ J b f • e - hf σ J b e • f) e = 0 ∧
      hf σ J (b - hf σ J b f • e - hf σ J b e • f) f = 0 := by
  have hfe := hf_fe hσ hJ he hff hef
  simp [hf_sub_left, hf_smul_left, he, hff, hef, hfe]
end ReciprocityTheory.ChartRestriction.G.SA
