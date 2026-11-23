-- Prove2me | solution 1 for P2M_GroundTheory_Global_InfinitePlace_tensorInfiniteAdeleRingEquiv_tmul__a0cdac9b4d94
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:03.575442+00:00
-- url     : https://prove2.me/submissions/54afe2ed-63ee-4dbd-9544-6ca568e09b4b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdele
import Theorems.Thm_GroundTheory_Global_InfinitePlace_tensorInfiniteAdeleRingEquiv_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct
open GroundTheory.Global.InfinitePlace
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [NumberField K] [NumberField L]
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution (l : L) (x : InfiniteAdeleRing K) :
    tensorInfiniteAdeleRingEquiv (l ⊗ₜ x) =
      algebraMap L (InfiniteAdeleRing L) l * infiniteAdeleRingMap x := by
  funext w
  rw [tensorInfiniteAdeleRingEquiv_tmul]
  rfl
end GroundTheory.Global.InfinitePlace
