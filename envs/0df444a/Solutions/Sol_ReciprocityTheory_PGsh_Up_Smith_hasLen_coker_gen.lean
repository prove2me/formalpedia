-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Smith.hasLen_coker_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:42:06.731621+00:00
-- url     : https://prove2.me/submissions/4a213be1-332b-490b-9d4d-93fb8246f871

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith

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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.Smith
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.Smith
theorem _root_.solution (hv : v.Integers R) {b : ℕ} {ι : Type} [Fintype ι] (g : ι → Fin b → R) :
    HasLen v R ((Fin b → R) ⧸ Submodule.span R (Set.range g))
      (∏ i, v (algebraMap R C ((smith_gen hv b g).choose i))) :=
  ⟨b, _, (smith_gen hv b g).choose_spec, rfl⟩
end ReciprocityTheory.PGsh.Up.Smith
