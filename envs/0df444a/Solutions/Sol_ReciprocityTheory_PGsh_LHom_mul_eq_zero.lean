-- Prove2me | solution 1 for ReciprocityTheory.PGsh.LHom.mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:32:44.163341+00:00
-- url     : https://prove2.me/submissions/060437e5-31c7-4766-bd42-d68af1b8debf

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero

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
namespace ReciprocityTheory.PGsh
namespace LHom
theorem _root_.solution {R S : LAlg R₀} {π : LHom R S} (hπ : π.SqZero) {a b : (R : Type u)}
    (ha : π.1 a = 0) (hb : π.1 b = 0) : a * b = 0 := by
  have hab : a * b ∈ RingHom.ker π.1 ^ 2 := by
    rw [sq]
    exact Ideal.mul_mem_mul (RingHom.mem_ker.mpr ha) (RingHom.mem_ker.mpr hb)
  rw [hπ.2] at hab
  exact (Submodule.mem_bot _).mp hab
end LHom
end ReciprocityTheory.PGsh
