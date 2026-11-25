-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_charOf_map_relabel_ff9c6d4a87db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:53.898476+00:00
-- url     : https://prove2.me/submissions/3062c04b-a016-446a-ac21-fef43c99a7ae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_relabelRingEquiv_apply_281506490fa6

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (V : Ideal (MRing ι)) :
    charOf (V.map (relabelRingEquiv ε h)) = charOf V := by
  have hC : (V.map (relabelRingEquiv ε h)).comap (C : ℤ →+* MRing ι') =
      V.comap (C : ℤ →+* MRing ι) := by
    ext n
    rw [Ideal.mem_comap, Ideal.mem_comap, ← mem_map_ringEquiv_iff (relabelRingEquiv ε h) V,
      relabelRingEquiv_apply, rename_C]
  simp only [charOf, hC]
end GroundTheory.Heights₂.Heights
