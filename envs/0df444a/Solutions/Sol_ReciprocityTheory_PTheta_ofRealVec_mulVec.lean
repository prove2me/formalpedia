-- Prove2me | solution 1 for ReciprocityTheory.PTheta.ofRealVec_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:02.629074+00:00
-- url     : https://prove2.me/submissions/fd003074-4527-47f1-9ad9-9f4203e19a64

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.PTheta
theorem _root_.solution (M : Matrix ι ι ℤ) (a : ι → ℝ) :
    ofRealVec (M.map (fun x : ℤ => (x : ℝ)) *ᵥ a) = M.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec a := by
  funext i
  simp [ofRealVec, Matrix.mulVec, dotProduct]
end ReciprocityTheory.PTheta
