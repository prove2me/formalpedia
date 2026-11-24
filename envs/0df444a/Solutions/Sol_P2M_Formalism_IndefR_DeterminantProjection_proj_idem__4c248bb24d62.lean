-- Prove2me | solution 1 for P2M_Formalism_IndefR_DeterminantProjection_proj_idem__4c248bb24d62
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:43.086859+00:00
-- url     : https://prove2.me/submissions/eae291a2-705e-44cc-abaf-8b2253f5240e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DeterminantProjection
import Theorems.Thm_Formalism_IndefR_DeterminantProjection_proj_idem

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
theorem _root_.solution (σ : A →+* A) (J : Matrix n n A) (u : n → A) (ainv : A) (ha : ainv * hsq σ J u = 1) :
    proj σ J u ainv * proj σ J u ainv = proj σ J u ainv :=
  proj_idem u _ (by rw [smul_dotProduct, smul_eq_mul]; exact ha)
end Formalism.IndefR.DeterminantProjection
