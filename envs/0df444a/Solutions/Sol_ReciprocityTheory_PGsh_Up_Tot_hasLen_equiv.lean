-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Tot.hasLen_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:31:23.311275+00:00
-- url     : https://prove2.me/submissions/d0eee2a0-066e-4dc5-a7aa-1b19c5571947

import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthFrobeniusStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthProductStatementHolds

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
open ReciprocityTheory.PGsh.Up.Tot
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.Tot
theorem _root_.solution {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {x : NNReal} (h : HasLen v R N x) : HasLen v R M x := by
  obtain ⟨m, c, ⟨f⟩, hx⟩ := h
  exact ⟨m, c, ⟨e.trans f⟩, hx⟩
end ReciprocityTheory.PGsh.Up.Tot
