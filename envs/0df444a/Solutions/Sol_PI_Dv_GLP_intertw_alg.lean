-- Prove2me | solution 1 for PI.Dv.GLP.intertw_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:14.328266+00:00
-- url     : https://prove2.me/submissions/b11fa0af-9c6c-4deb-aa2b-3ad5b23faad2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLP
theorem _root_.solution {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W) (f : V →ₗ[K] W)
    (hf : ∀ g x, f (ρ g x) = σ g (f x)) (a : MonoidAlgebra K G) (x : V) :
    f (ρ.asAlgebraHom a x) = σ.asAlgebraHom a (f x) := by
  induction a using MonoidAlgebra.induction_on with
  | of g => simp [Representation.asAlgebraHom_of, hf]
  | add a b ha hb => simp [map_add, ha, hb]
  | smul r a ha => simp [map_smul, ha]
end PI.Dv.GLP
