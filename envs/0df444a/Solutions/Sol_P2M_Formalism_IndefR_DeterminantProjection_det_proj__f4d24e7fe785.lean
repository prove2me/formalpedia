-- Prove2me | solution 1 for P2M_Formalism_IndefR_DeterminantProjection_det_proj__f4d24e7fe785
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:43.036286+00:00
-- url     : https://prove2.me/submissions/60546ab6-517d-4e40-879f-e8e8226dff28

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DeterminantProjection
import Theorems.Thm_Formalism_IndefR_DeterminantProjection_det_proj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.IndefR Formalism.IndefR.DeterminantProjection
variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]
namespace Formalism.IndefR.DeterminantProjection
theorem _root_.solution (σ : A →+* A) (J : Matrix n n A) (u : n → A) (ainv : A) (ha : ainv * hsq σ J u = 1) (x : A) :
    (1 + (x - 1) • proj σ J u ainv).det = x :=
  det_proj u _ (by rw [smul_dotProduct, smul_eq_mul]; exact ha) x
end Formalism.IndefR.DeterminantProjection
