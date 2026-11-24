-- Prove2me | solution 1 for ReciprocityTheory.Ty.Fin.mem_cj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:00.902396+00:00
-- url     : https://prove2.me/submissions/1018a62c-53a7-4641-8517-6e5e1e8c967b

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
variable {Γ : Type} [Group Γ]
namespace ReciprocityTheory.Ty.Fin
theorem _root_.solution {x h : Γ} {B : Subgroup Γ} : h ∈ cj x B ↔ x * h * x⁻¹ ∈ B := Iff.rfl
end ReciprocityTheory.Ty.Fin
