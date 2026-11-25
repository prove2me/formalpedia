-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.sq_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:48:11.819354+00:00
-- url     : https://prove2.me/submissions/4ef57a75-8bfa-476f-92d3-3bc3434f7f41

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatementOfClaim
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLat
import Definitions.Def_ReciprocityTheory_DualLattices_ImportsBis
import Definitions.Def_ReciprocityTheory_DualLattices_SqIdeal
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {X : Type} (I : Submodule R (X → C)) : sqIdeal I = I * I := by
  rw [sqIdeal, Submodule.mul_eq_span_mul_set]
  congr 1
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_mul]
  constructor
  · rintro ⟨f, hf, f', hf', rfl⟩
    exact ⟨f, hf, f', hf', rfl⟩
  · rintro ⟨f, hf, f', hf', rfl⟩
    exact ⟨f, hf, f', hf', rfl⟩
end ReciprocityTheory.PGsh.Up
