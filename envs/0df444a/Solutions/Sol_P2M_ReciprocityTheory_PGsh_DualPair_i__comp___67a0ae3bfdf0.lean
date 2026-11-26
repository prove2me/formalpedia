-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_DualPair_i__comp___67a0ae3bfdf0
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:00:42.304003+00:00
-- url     : https://prove2.me/submissions/aeb9acd4-3c64-4767-b5a9-2bb30f04c156

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)
theorem _root_.solution : Dp.i₂L.comp Dp.σ = Dp.i₁L.comp Dp.σ := by
  refine Subtype.ext (AlgHom.ext fun d => ?_)
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show Dp.σ.1 (Dp.π.1 (Dp.σ.1 d)) = Dp.σ.1 d
    rw [Dp.sect]
  · show Dp.σ.1 d = Dp.σ.1 (Dp.π.1 (Dp.σ.1 d))
    rw [Dp.sect]



