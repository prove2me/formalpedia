-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lfMat_mulVec_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:22:46.100122+00:00
-- url     : https://prove2.me/submissions/8477c4ff-d9d0-4938-ab6b-670eae4d9a16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (a b : Fin n) (S : LfIdx ε) (c : ℂ)
    (h : sgE ε cpFock cmFock a b (fockBasis n S.1) = c • fockBasis n S.1) :
    lfMat ε a b *ᵥ Pi.single S 1 = c • Pi.single S 1 := by
  ext T
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [lfMat, Matrix.submatrix_apply, lfMatFull, LinearMap.toMatrix_apply]
  rw [h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Pi.smul_apply, Finsupp.single_apply,
    Pi.single_apply]
  by_cases hTS : T = S
  · subst hTS
    simp
  · rw [if_neg (fun h' => hTS (Subtype.ext h'.symm)), if_neg hTS]
end ReciprocityTheory.ChartRestriction.DS
