-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.pairing_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:32:25.907798+00:00
-- url     : https://prove2.me/submissions/d6b41ea4-4c99-474d-8d60-ff4db28e20f8

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight

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
theorem _root_.solution (N : ℕ) (x y : B.G R) (hx : N • x = 0) (hy : N • y = 0) :
    ∃ z, B.IsPairing N x y z := by
  obtain ⟨u⟩ := B.nonempty R x y
  obtain ⟨l₁, hl₁, -⟩ := B.trans (B.zero1 y) (B.tr1 hx (B.nsmul1 u N))
  obtain ⟨l₂, hl₂, -⟩ := B.trans (B.zero2 x) (B.tr2 hy (B.nsmul2 u N))
  exact ⟨l₁ / l₂, hx, hy, u, l₁, l₂, hl₁.symm, hl₂.symm, rfl⟩
end ReciprocityTheory.PGsh.BX
