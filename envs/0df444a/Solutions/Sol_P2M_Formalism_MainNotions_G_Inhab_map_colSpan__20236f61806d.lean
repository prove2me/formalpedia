-- Prove2me | solution 1 for P2M_Formalism_MainNotions_G_Inhab_map_colSpan__20236f61806d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:25.646218+00:00
-- url     : https://prove2.me/submissions/23488611-6fcb-4860-97fa-78443dad9e49

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ}
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (A g : Matrix (Fin k) (Fin k) K) :
    (colSpan R g).map ((Matrix.mulVecLin A).restrictScalars R) = colSpan R (A * g) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1
end Formalism.MainNotions.G.Inhab
