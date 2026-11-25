-- Prove2me | solution 1 for ReciprocityTheory.PGsh.wt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:03:43.446844+00:00
-- url     : https://prove2.me/submissions/f19526f9-0bc7-44db-8a52-a6237fa40efe

import Definitions.Def_ReciprocityTheory_DualLattices_ConstantCoeffRowSubst
import Definitions.Def_ReciprocityTheory_DualLattices_WtGtRowSubstXSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open scoped Classical
open ReciprocityTheory ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (A B : Fin ν × ι →₀ ℕ) : wt (A + B) = wt A + wt B := by
  unfold wt
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)
end ReciprocityTheory.PGsh
