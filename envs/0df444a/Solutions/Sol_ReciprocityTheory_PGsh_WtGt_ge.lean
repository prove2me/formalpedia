-- Prove2me | solution 1 for ReciprocityTheory.PGsh.WtGt.ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:31:53.429031+00:00
-- url     : https://prove2.me/submissions/335e87fa-1c5f-4c8b-91c4-063c079fafb0

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
namespace WtGt
theorem _root_.solution {d : ℕ} {P : MvPolynomial (Fin ν × ι) ℂ} (h : WtGt d P) : WtGe d P :=
  fun A hA => le_of_lt (h A hA)
end WtGt
end ReciprocityTheory.PGsh
