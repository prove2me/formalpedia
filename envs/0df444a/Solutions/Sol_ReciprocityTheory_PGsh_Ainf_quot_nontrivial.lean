-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.quot_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:14.492297+00:00
-- url     : https://prove2.me/submissions/bb24a053-3ee6-48de-a542-8155b5ab3cd7

import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
open ReciprocityTheory ReciprocityTheory.PGsh
open ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
namespace ReciprocityTheory.PGsh.Ainf
theorem _root_.solution {R : Type} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) : Nontrivial (R ⧸ I) :=
  Ideal.Quotient.nontrivial_iff.2 hI
end ReciprocityTheory.PGsh.Ainf
