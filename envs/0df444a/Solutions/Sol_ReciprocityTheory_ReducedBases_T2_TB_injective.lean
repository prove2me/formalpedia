-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.TB_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:48.20496+00:00
-- url     : https://prove2.me/submissions/04967b05-f36b-4684-adf0-535445fb6ff3

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Matrix
variable {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hAB : A = Bᴴ * B) :
    Function.Injective (TB B) := by
  have hdet : IsUnit B.det := by
    have h1 := hA.det_pos
    rw [hAB, Matrix.det_mul, Matrix.det_conjTranspose] at h1
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0] at h1
    simp at h1
  have hinj : Function.Injective B.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det B).2 hdet)
  intro u w h
  have h' : B *ᵥ WithLp.ofLp u = B *ᵥ WithLp.ofLp w := by
    have := congrArg WithLp.ofLp h
    simpa [TB] using this
  have h'' := congrArg (WithLp.toLp 2) (hinj h')
  simpa using h''
end ReciprocityTheory.ReducedBases.T2
