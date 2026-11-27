-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.span_top_of_isLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:32:23.233982+00:00
-- url     : https://prove2.me/submissions/439cb263-2ad0-4fc3-9413-5562ca6590ae

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_Lemmata_MiscLemmasL_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsSmulMemOfMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
open Module
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
theorem _root_.solution {X : Type} [Fintype X] [DecidableEq X] {M : Submodule R (X → C)}
    (h : IsLat R M) : Submodule.span C (M : Set (X → C)) = ⊤ := by
  obtain ⟨B, hB, rfl⟩ := h
  rw [Submodule.span_span_of_tower]
  have hli : LinearIndependent C (fun j x => B x j) := by
    have := (Matrix.linearIndependent_cols_iff_isUnit (A := B)).2 ((Matrix.isUnit_iff_isUnit_det B).2 hB)
    convert this using 1; rfl
  exact hli.span_eq_top_of_card_eq_finrank' (by simp)
end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
