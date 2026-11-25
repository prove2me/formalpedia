-- Prove2me | solution 1 for ReciprocityTheory.PGsh.WtGe.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:15:31.049885+00:00
-- url     : https://prove2.me/submissions/3a712ef5-a7fb-4c2b-8086-7a88ba2316ef

import Definitions.Def_ReciprocityTheory_DualLattices_ConstantCoeffRowSubst
import Definitions.Def_ReciprocityTheory_DualLattices_WtGtRowSubstXSub
import Theorems.Thm_ReciprocityTheory_PGsh_wt_add

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
theorem _root_.solution {d e : ℕ} {P Q : MvPolynomial (Fin ν × ι) ℂ} (h1 : WtGe d P) (h2 : WtGe e Q) :
    WtGe (d + e) (P * Q) := by
  intro A hA
  obtain ⟨B, hB, B', hB', rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hA)
  rw [wt_add]
  have := h1 B hB
  have := h2 B' hB'
  omega
end WtGe
end ReciprocityTheory.PGsh
