-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_DualPair_s_comp_i__62d2eabb37ee
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:00:41.420555+00:00
-- url     : https://prove2.me/submissions/4766052e-2926-43be-8c9f-04614510586b

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
theorem _root_.solution : Dp.sL.comp Dp.i₂L = LHom.id Dp.D := by
  refine Subtype.ext (AlgHom.ext fun d => ?_)
  show Dp.fs _ = d
  unfold ReciprocityTheory.PGsh.DualPair.fs
  first
  | (show d + Dp.σ.1 (Dp.π.1 d) - Dp.σ.1 (Dp.π.1 d) = d; ring)
  | (show Dp.σ.1 (Dp.π.1 d) + d - Dp.σ.1 (Dp.π.1 (Dp.σ.1 (Dp.π.1 d))) = d; rw [Dp.sect]; ring)
  | (simp [Dp.sect])



