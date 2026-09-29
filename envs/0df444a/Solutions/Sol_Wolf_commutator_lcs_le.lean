-- Prove2me | solution 1 for Wolf.commutator_lcs_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T06:43:42.081798+00:00
-- url     : https://prove2.me/submissions/d193b20a-cf86-4b61-bbfc-bea0a83fa48e

import Definitions.Def_MilnorWolf_Growth
import Mathlib

set_option autoImplicit false

open MilnorWolf
open scoped commutatorElement

namespace Ag4Aux_WolfComm

theorem three_mod {G : Type*} [Group G] (H₁ H₂ H₃ N : Subgroup G) [N.Normal]
    (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) : ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  have key : ∀ K : Subgroup G, K ≤ N ↔ K.map (QuotientGroup.mk' N) = ⊥ := by
    intro K; rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [key] at h1 h2 ⊢
  simp only [Subgroup.map_commutator] at h1 h2 ⊢
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem aux {G : Type*} [Group G] (l : ℕ) :
    ∀ k : ℕ, ⁅MilnorWolf.lcs G k, MilnorWolf.lcs G l⁆ ≤ MilnorWolf.lcs G (k + l + 1) := by
  induction l with
  | zero => intro k; exact le_rfl
  | succ l ih =>
    intro k
    show ⁅lcs G k, ⁅lcs G l, ⊤⁆⁆ ≤ lcs G (k + (l + 1) + 1)
    rw [Subgroup.commutator_comm (lcs G k)]
    apply three_mod
    · have h := ih (k + 1)
      rw [show k + 1 + l + 1 = k + (l + 1) + 1 by omega] at h
      rw [Subgroup.commutator_comm ⊤ (lcs G k)]
      exact h
    · have h := Subgroup.commutator_mono (ih k) (le_refl (⊤ : Subgroup G))
      rw [show k + (l + 1) + 1 = (k + l + 1) + 1 by omega]
      exact h

end Ag4Aux_WolfComm

theorem solution {G : Type*} [Group G] (k l : ℕ) : ⁅MilnorWolf.lcs G k, MilnorWolf.lcs G l⁆ ≤ MilnorWolf.lcs G (k + l + 1) :=
  Ag4Aux_WolfComm.aux l k
