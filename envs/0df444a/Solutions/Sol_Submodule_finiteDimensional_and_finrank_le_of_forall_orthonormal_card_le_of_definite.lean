-- Prove2me | solution 1 for Submodule.finiteDimensional_and_finrank_le_of_forall_orthonormal_card_le_of_definite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8082a33e-f091-58af-8e53-4a8f7ebc788a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_finiteDimensional_and_finrank_le_of_forall_orthonormal_card_le_of_definite

set_option autoImplicit false

open scoped ComplexConjugate

theorem solution
    {E : Type*} [AddCommGroup E] [Module ℂ E] (V : Submodule ℂ E)
    (B : E → E → ℂ)
    (hadd : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul : ∀ (c : ℂ) (x y : E), B (c • x) y = c * B x y)
    (hsymm : ∀ x y, B y x = conj (B x y))
    (hpos : ∀ x ∈ V, 0 ≤ (B x x).re)
    (hdef : ∀ x ∈ V, B x x = 0 → x = 0)
    (D : ℕ) (hD : ∀ (n : ℕ) (e : Fin n → E), (∀ i, e i ∈ V) →
      (∀ i j, B (e i) (e j) = if i = j then 1 else 0) → n ≤ D) :
    FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ D := by
  classical

  let core : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => B (y : E) (x : E)
      conj_inner_symm := fun x y => (hsymm (x : E) (y : E)).symm
      re_inner_nonneg := fun x => hpos x x.2
      add_left := fun x y z => by
        change B (z : E) ((x : E) + (y : E)) = B (z : E) (x : E) + B (z : E) (y : E)
        rw [hsymm ((x : E) + (y : E)) (z : E), hadd, map_add, ← hsymm, ← hsymm]
      smul_left := fun x y r => by
        change B (y : E) (r • (x : E)) = conj r * B (y : E) (x : E)
        rw [hsymm (r • (x : E)) (y : E), hsmul, map_mul, ← hsymm]
      definite := fun x hx => Subtype.ext (by exact_mod_cast hdef x x.2 hx) }
  letI : NormedAddCommGroup V := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore

  have hli : ∀ s : Finset V, (LinearIndependent ℂ fun i : s => (i : V)) → s.card ≤ D := by
    intro s hs

    set n := s.card
    let e : Fin n ≃ s := (s.equivFin).symm
    have hs' : LinearIndependent ℂ (fun i : Fin n => ((e i : s) : V)) := hs.comp e e.injective

    have hon := InnerProductSpace.gramSchmidtNormed_orthonormal (𝕜 := ℂ) (E := ↥V) hs'
    rw [orthonormal_iff_ite] at hon
    refine hD n (fun i => ((InnerProductSpace.gramSchmidtNormed ℂ (fun i : Fin n => ((e i : s) : V)) i : V) : E))
      (fun i => Subtype.mem _) (fun i j => ?_)
    have := hon j i

    change B _ _ = _ at this
    rw [this]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]
  have hrank : Module.rank ℂ V ≤ D := rank_le hli
  have hfin : Module.Finite ℂ V := by
    rw [← Module.rank_lt_aleph0_iff]
    exact hrank.trans_lt (Cardinal.natCast_lt_aleph0 (n := D))
  exact ⟨hfin, Module.finrank_le_of_rank_le hrank⟩

end S_Submodule_finiteDimensional_and_finrank_le_of_forall_orthonormal_card_le_of_definite
end P2MW
export P2MW.S_Submodule_finiteDimensional_and_finrank_le_of_forall_orthonormal_card_le_of_definite (solution)
