-- Prove2me | solution 1 for ReciprocityTheory.PGsh.LHom.exists_unit_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:40:12.570136+00:00
-- url     : https://prove2.me/submissions/44d0772a-2c5f-4f02-9dad-1ff561819e4b

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
theorem _root_.solution {R S : LAlg R₀} (π : LHom R S) (hs : Function.Surjective π.1)
    (l : (S : Type u)ˣ) : ∃ l' : (R : Type u)ˣ, Units.map (π.1 : R →* S) l' = l := by
  obtain ⟨a, ha⟩ := hs (l : (S : Type u))
  have hu : IsUnit a := π.2.map_nonunit a (by
    have h1 : IsUnit (π.1 a) := ha.symm ▸ l.isUnit
    exact h1)
  refine ⟨hu.unit, Units.ext ?_⟩
  simp [ha]
end LHom
end ReciprocityTheory.PGsh
