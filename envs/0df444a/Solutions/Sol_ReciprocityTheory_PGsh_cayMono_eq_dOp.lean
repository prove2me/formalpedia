-- Prove2me | solution 1 for ReciprocityTheory.PGsh.cayMono_eq_dOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:39:26.197974+00:00
-- url     : https://prove2.me/submissions/1b57a1f1-fb7f-48c7-ac69-905051a84acb

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow

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
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (σ : Equiv.Perm (Fin n)) : cayMono n R σ = dOp σ id := by
  unfold cayMono dOp
  simp only [List.ofFn_eq_map, id_eq]
end ReciprocityTheory.PGsh
