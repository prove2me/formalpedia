-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Asm.isCoprime_list_prod_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:04.019566+00:00
-- url     : https://prove2.me/submissions/2a356a98-9123-4d12-ab88-74dba56c7b6f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_NilpotentHypotheses_AevalProdLinearFactors
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Asm_isCoprime_list_prod_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Asm
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.RgUd.T.Nil.Asm
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} (f : ι → R) (z : R) :
    ∀ l : List ι, (∀ x ∈ l, IsCoprime z (f x)) → IsCoprime z (l.map f).prod := by
  intro l h
  exact (isCoprime_list_prod_left f z l fun x hx => (h x hx).symm).symm
end PositivityTheory.RgUd.T.Nil.Asm
