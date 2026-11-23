-- Prove2me | solution 1 for ReciprocityTheory.PGsh.LHom.sqZero_of_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:07.742522+00:00
-- url     : https://prove2.me/submissions/f4829840-9def-4515-ba36-61ab5d18aeb7

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
attribute [instance] LAlg.cr LAlg.alg LAlg.loc
variable {R₀ : Type u} [CommRing R₀]
namespace ReciprocityTheory.PGsh
namespace LHom
theorem _root_.solution {R S : LAlg R₀} (π : LHom R S) (ξ : (R : Type u))
    (hs : Function.Surjective π.1) (hk : RingHom.ker π.1 = Ideal.span {ξ}) (hξ : ξ * ξ = 0) :
    π.SqZero := by
  unfold ReciprocityTheory.PGsh.LHom.SqZero
  refine ⟨hs, ?_⟩
  rw [hk, Ideal.span_singleton_pow, pow_two, hξ]
  exact Ideal.span_singleton_eq_bot.mpr rfl
end LHom
end ReciprocityTheory.PGsh
