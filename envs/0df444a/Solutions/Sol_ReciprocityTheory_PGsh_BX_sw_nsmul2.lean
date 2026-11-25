-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.sw_nsmul2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:32:38.693412+00:00
-- url     : https://prove2.me/submissions/192884d3-0f17-46e8-be6e-75817ccec853

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Theorems.Thm_ReciprocityTheory_PGsh_BX_sw_nsmul1


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
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀}
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution {x y : B.G R} (u : B.P R x y) (n : ℕ) :
    B.sw (B.nsmul2 u n) = B.nsmul1 (B.sw u) n := by
  rw [← B.sw_sw (B.nsmul1 (B.sw u) n), B.sw_nsmul1, B.sw_sw]
end ReciprocityTheory.PGsh.BX
