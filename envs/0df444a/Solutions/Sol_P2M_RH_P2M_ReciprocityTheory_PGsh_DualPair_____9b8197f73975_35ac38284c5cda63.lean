-- Prove2me | solution 1 for P2M_RH_P2M_ReciprocityTheory_PGsh_DualPair_____9b8197f73975_35ac38284c5cda63
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:10.16883+00:00
-- url     : https://prove2.me/submissions/f4030a4e-d45f-4e13-ba19-a3d2c673f0e2

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)
namespace ReciprocityTheory.PGsh.DualPair
theorem _root_.solution : Dp.π.1 Dp.η = 0 := by
  have h := Dp.η_mem
  rwa [Submodule.restrictScalars_mem, RingHom.mem_ker] at h
end ReciprocityTheory.PGsh.DualPair
