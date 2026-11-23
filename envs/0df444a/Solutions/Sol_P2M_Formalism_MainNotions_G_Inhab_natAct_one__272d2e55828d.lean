-- Prove2me | solution 1 for P2M_Formalism_MainNotions_G_Inhab_natAct_one__272d2e55828d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:25.775421+00:00
-- url     : https://prove2.me/submissions/8ea4db81-bddf-4040-ab77-2274129aebf6

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
import Theorems.Thm_Formalism_MainNotions_G_Inhab_lamAt_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (C : Level P)
variable (h0 : ∀ v, P.lam0 v = fun _ _ => 0)
include h0
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (A : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)) : P.natAct A 1 = 1 := by
  simp [Places.natAct, h0, lamAt_zero]
end Formalism.MainNotions.G.Inhab
