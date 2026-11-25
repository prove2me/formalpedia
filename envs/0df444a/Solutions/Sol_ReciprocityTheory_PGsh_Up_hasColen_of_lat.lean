-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.hasColen_of_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:48:06.040403+00:00
-- url     : https://prove2.me/submissions/f531dd10-19e9-4a01-b0c4-6305548d365b

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
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    (v : Valuation C NNReal) {X : Type} [Fintype X] [DecidableEq X] {M : Submodule R (X → C)}
    (h : IsLat R M) : ∃ c, HasColen R v M c := by
  obtain ⟨B, -, hB⟩ := h
  exact ⟨_, B, hB, rfl⟩
end ReciprocityTheory.PGsh.Up
