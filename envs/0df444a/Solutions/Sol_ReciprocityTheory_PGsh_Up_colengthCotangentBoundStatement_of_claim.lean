-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.colengthCotangentBoundStatement_of_claim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:38:32.260195+00:00
-- url     : https://prove2.me/submissions/58f903de-85be-4eb8-bf29-09e06a8a5a77

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatementOfClaim
import Theorems.Thm_ReciprocityTheory_PGsh_Up_colengthCotangentBound_of_claim

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
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hcl : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → v (p : C) < 1 → ColengthCotangentValuation p C v R) : ColengthCotangentBoundStatement := by
  intro p _ C _ _ _ v R _ _ hv hp N _ _ _ hN AA lenN lenOm hlen hom
  exact colengthCotangentBound_of_claim p C v R hv (hcl p C v R hv hp) N hN AA lenN lenOm hlen hom
end ReciprocityTheory.PGsh.Up
