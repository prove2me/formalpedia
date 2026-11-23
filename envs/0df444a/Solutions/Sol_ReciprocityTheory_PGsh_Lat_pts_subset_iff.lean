-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Lat.pts_subset_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:31.512797+00:00
-- url     : https://prove2.me/submissions/ba3c090a-a2c8-4102-b747-edf1ba313eab

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_NearIdentityColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_isIntegralVec_single
import Theorems.Thm_ReciprocityTheory_PGsh_Lat_isUnit_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open Matrix
open ReciprocityTheory.PGsh.Lat
variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.PGsh.Lat
theorem _root_.solution (L' L : Lat v ι) :
    L'.pts ⊆ L.pts ↔ IsIntegralMat v (L.B⁻¹ * L'.B) := by
  constructor
  · intro h i j
    obtain ⟨c, hc, hx⟩ := h ⟨Pi.single j 1, ReciprocityTheory.PGsh.isIntegralVec_single j, rfl⟩
    have hM : (L.B⁻¹ * L'.B) *ᵥ Pi.single j 1 = c := by
      rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_det L), Matrix.one_mulVec]
    have e := congrFun hM i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at e
    rw [e]
    exact hc i
  · intro hM x ⟨c, hc, hx⟩
    refine ⟨(L.B⁻¹ * L'.B) *ᵥ c, hM.mulVec hc, ?_⟩
    rw [hx, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_det L),
      Matrix.one_mul]
end ReciprocityTheory.PGsh.Lat
