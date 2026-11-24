-- Prove2me | solution 1 for ReciprocityTheory.PGsh.WtGe.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:46.896799+00:00
-- url     : https://prove2.me/submissions/d9f83108-848a-4746-a21b-b2de53304bda

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
namespace WtGe
theorem _root_.solution {d : ℕ} {P Q : MvPolynomial (Fin ν × ι) ℂ} (h1 : WtGe d P) (h2 : WtGe d Q) :
    WtGe d (P + Q) := by
  intro A hA
  rcases Finset.mem_union.mp (MvPolynomial.support_add hA) with h | h
  exacts [h1 A h, h2 A h]
end WtGe
end ReciprocityTheory.PGsh
