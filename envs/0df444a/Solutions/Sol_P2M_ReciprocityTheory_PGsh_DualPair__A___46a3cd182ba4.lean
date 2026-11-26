-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_DualPair__A___46a3cd182ba4
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:59:58.169629+00:00
-- url     : https://prove2.me/submissions/ec20b312-154d-4957-916a-14a3420f5a3c

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
theorem _root_.solution (c : (R : Type u)) : Dp.μA c Dp.η = Dp.σ.1 c * Dp.η := by
  show Dp.fμ c Dp.η = Dp.σ.1 c * Dp.η
  have h : Dp.π.1 Dp.η = 0 := Dp.η_mem
  simp [ReciprocityTheory.PGsh.DualPair.fμ, h]



