-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.hasLen_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:39:15.891411+00:00
-- url     : https://prove2.me/submissions/d7762981-b204-4361-9d58-76b56e18c466

import Definitions.Def_ReciprocityTheory_DualLattices_LenIdBStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {x : NNReal} (h : HasLen v R N x) : HasLen v R M x := by
  obtain ⟨k, c, ⟨f⟩, hx⟩ := h
  exact ⟨k, c, ⟨e.trans f⟩, hx⟩
end ReciprocityTheory.PGsh.Up
