-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.posDef_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:34.989791+00:00
-- url     : https://prove2.me/submissions/bd091458-f885-4072-ad6b-2d5d1c8027fd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_isUnit_det_of_inG__484f4d84a40f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {g : M2 n} (hg : InG g) :
    (g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ).PosDef := by
  have hu : IsUnit gᴴ := by
    rw [Matrix.isUnit_iff_isUnit_det, det_conjTranspose]
    exact (isUnit_det_of_inG' hg).star
  have hP : (gᴴᴴ * gᴴ).PosDef := Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 hu)
  rw [conjTranspose_conjTranspose] at hP
  have h2 := hP.submatrix (e := (Sum.inr : Fin n → Fin n ⊕ Fin n)) Sum.inr_injective
  convert h2 using 1
  conv_rhs => rw [← fromBlocks_toBlocks g]
  ext i j
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.submatrix]
end PositivityTheory.Rg.Sw.LVs
