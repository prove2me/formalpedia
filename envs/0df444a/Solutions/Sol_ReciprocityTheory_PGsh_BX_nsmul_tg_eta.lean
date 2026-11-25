-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.nsmul_tg_eta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:32:34.745959+00:00
-- url     : https://prove2.me/submissions/67dc0ac8-2548-4426-8677-fb9cab5ed895

import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_HeightFunctionalStatementOfPairingProperties
import Definitions.Def_ReciprocityTheory_DualLattices_IsHeightUnique

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
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀)
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (hN : (N : (R : Type u)) = 0) (v : B.gg) :
    N • B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk) = 0 := by
  rw [← map_nsmul, ← tmul_smul]
  have : N • Dp.ηk = 0 := by
    apply Subtype.ext
    change N • Dp.η = 0
    rw [nsmul_eq_mul, ← map_natCast Dp.σ.1, hN, map_zero, zero_mul]
  rw [this, tmul_zero, map_zero]
end ReciprocityTheory.PGsh.BX
