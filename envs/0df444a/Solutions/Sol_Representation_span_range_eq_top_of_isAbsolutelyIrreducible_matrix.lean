-- Prove2me | solution 1 for Representation.span_range_eq_top_of_isAbsolutelyIrreducible_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/8596cd5d-1052-51bc-8a82-52549e80dbb4

import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_Representation_AbsolutelyIrreducible
import Theorems.Thm_Representation_span_range_eq_top_of_isIrreducible
import Theorems.Thm_Representation_span_range_baseChange_eq_top_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_span_range_eq_top_of_isAbsolutelyIrreducible_matrix

open scoped TensorProduct

universe u

theorem solution
    {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] {k : Type u} [Field k]
    (ρ : G →* GL n k) [Representation.IsAbsolutelyIrreducible.{u} (Deformation.matrixRepresentation ρ)] :
    Submodule.span k (Set.range fun g => (ρ g).val) = ⊤ := by
  classical
  set σ : Representation k G (n → k) := Deformation.matrixRepresentation ρ with hσ
  let K := AlgebraicClosure k

  haveI : (Representation.baseChange K σ).IsIrreducible :=
    Representation.IsAbsolutelyIrreducible.absolutelyIrreducible K inferInstance inferInstance

  have hK : Submodule.span K (Set.range fun g => (σ g).baseChange K) = ⊤ := by
    have := Representation.span_range_eq_top_of_isIrreducible (Representation.baseChange K σ)
    exact this

  have hk : Submodule.span k (Set.range ⇑σ) = ⊤ :=
    (Representation.span_range_baseChange_eq_top_iff (K := K) σ).mp hK

  have hrange : Set.range ⇑σ = Matrix.toLin' '' Set.range fun g => (ρ g).val := by
    rw [← Set.range_comp]
    refine congrArg Set.range (funext fun g => ?_)
    simp [hσ, Deformation.matrixRepresentation_apply, Matrix.toLin'_apply']
  set e : Matrix n n k ≃ₗ[k] ((n → k) →ₗ[k] (n → k)) := Matrix.toLin' with he
  have h2 : Submodule.map e.toLinearMap (Submodule.span k (Set.range fun g => (ρ g).val)) = ⊤ := by
    rw [Submodule.map_span, LinearEquiv.coe_toLinearMap, ← hrange]
    exact hk
  have hinj : Function.Injective e.toLinearMap := e.injective
  rw [← Submodule.comap_map_eq_of_injective hinj (Submodule.span k (Set.range fun g => (ρ g).val)), h2,
    Submodule.comap_top]

end S_Representation_span_range_eq_top_of_isAbsolutelyIrreducible_matrix
end P2MW
export P2MW.S_Representation_span_range_eq_top_of_isAbsolutelyIrreducible_matrix (solution)
