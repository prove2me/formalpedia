-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.cosetLeaderMatrix_isCosetLeader
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:36:35.940465+00:00
-- url     : https://prove2.me/submissions/8e3f1f4a-02bb-4728-9386-d2e604854673

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq W] [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (z : Matrix W R F) (x₀ : Matrix W W F)
    (hx₀ : ∀ i, h.mulVec (row x₀ i) = z i) (i : W) :
    IsCosetLeader h (z i) (row (cosetLeaderMatrix h z x₀ hx₀) i) := by
  exact Classical.choose_spec
    (exists_cosetLeader h (z i) (row x₀ i) (hx₀ i))
end QEC.Coding.ProductExpansion
