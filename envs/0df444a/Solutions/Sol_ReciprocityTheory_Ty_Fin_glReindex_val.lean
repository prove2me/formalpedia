-- Prove2me | solution 1 for ReciprocityTheory.Ty.Fin.glReindex_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:00.46981+00:00
-- url     : https://prove2.me/submissions/2f052cfe-97ef-4732-9659-1a49e54d1161

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_HCDisjointO
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_FiniteDimensionalHcSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open ReciprocityTheory ReciprocityTheory.Ty ReciprocityTheory.Ty.Fin
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
omit [Fintype K] [DecidableEq K]
namespace ReciprocityTheory.Ty.Fin
theorem _root_.solution {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (e : α ≃ β)
    (g : GL α K) : ((glReindex K e g : GL β K) : Matrix β β K) = (g : Matrix α α K).submatrix e.symm e.symm := rfl
end ReciprocityTheory.Ty.Fin
