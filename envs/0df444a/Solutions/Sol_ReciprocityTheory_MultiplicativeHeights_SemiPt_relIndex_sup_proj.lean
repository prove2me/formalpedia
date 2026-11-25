-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.relIndex_sup_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:08:12.187889+00:00
-- url     : https://prove2.me/submissions/d2baa3ea-2d14-4f89-bbe2-bdc662705e18

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegT
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {G : Type} [AddCommGroup G] (π : G →+ G) (A X C : AddSubgroup G)
    (hXC : X ≤ C) (hA : ∀ a ∈ A, π a = 0) (hC : ∀ x ∈ C, π x = x) :
    (A ⊔ X).relIndex (A ⊔ C) = X.relIndex C := by
  have heq : A ⊔ X = X.comap π ⊓ (A ⊔ C) := by
    apply le_antisymm
    · refine le_inf (sup_le ?_ ?_) (sup_le_sup_left hXC A)
      · intro a ha
        show π a ∈ X
        rw [hA a ha]
        exact X.zero_mem
      · intro x hx
        show π x ∈ X
        rw [hC x (hXC hx)]
        exact hx
    · rintro z ⟨hzX, hz⟩
      obtain ⟨a, ha, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hz
      have hπ : π (a + w) = w := by rw [map_add, hA a ha, hC w hw, zero_add]
      have hwX : w ∈ X := by
        have : π (a + w) ∈ X := hzX
        rwa [hπ] at this
      exact AddSubgroup.add_mem_sup ha hwX
  have hmap : (A ⊔ C).map π = C := by
    rw [AddSubgroup.map_sup]
    have h1 : A.map π = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨a, ha, rfl⟩
      rw [hA a ha]
      exact AddSubgroup.zero_mem _
    have h2 : C.map π = C := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        rw [hC x hx]
        exact hx
      · intro x hx
        exact ⟨x, hx, hC x hx⟩
    rw [h1, h2, bot_sup_eq]
  rw [heq, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap, hmap]
end ReciprocityTheory.MultiplicativeHeights.SemiPt
