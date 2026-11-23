-- Prove2me | solution 1 for ReciprocityTheory.PTheta.ofIntVec_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:20.308064+00:00
-- url     : https://prove2.me/submissions/516d074f-d077-4565-a27c-9b73c0cbfa2a

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
theorem _root_.solution (M : Matrix ι ι ℤ) (l : ι → ℤ) :
    ofIntVec (M *ᵥ l) = M.map (fun x : ℤ => (x : ℂ)) *ᵥ ofIntVec l := by
  funext i
  simp [ofIntVec, Matrix.mulVec, dotProduct]
end ReciprocityTheory.PTheta
