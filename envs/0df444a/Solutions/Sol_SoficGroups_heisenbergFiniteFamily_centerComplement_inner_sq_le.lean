-- Prove2me | solution 1 for SoficGroups.heisenbergFiniteFamily_centerComplement_inner_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/9f448846-c760-41d4-83f9-15fa1104a5d3

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_unitaryImages_inner_sq_mul_card_le
import Theorems.Thm_SoficGroups_unitaryFixedSubmodule_orthogonal_map_of_centralizes
import Theorems.Thm_SoficGroups_unitaryFixedSubmodules_inner_eq_zero_of_commute_centerComplement

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁
namespace SoficGroups
theorem _root_.solution
    {G : Type u₁} {H : Type v₁} {ι : Type*}
    [Group G] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H)
    (X Z : Subgroup G) (y : ι → G)
    (hXZ : ∀ x : X, ∀ z : Z, Commute (x : G) (z : G))
    (hyZ : ∀ i : ι, ∀ z : Z, Commute (y i) (z : G))
    (hcomm : ∀ ⦃i j : ι⦄, i ≠ j →
      ∀ x : heisenbergConjugateSubgroup X (y i),
      ∀ x' : heisenbergConjugateSubgroup X (y j),
        Commute (x : G) (x' : G))
    (hcenter : ∀ ⦃i j : ι⦄, i ≠ j →
      Z ≤ heisenbergConjugateSubgroup X (y i) ⊔
        heisenbergConjugateSubgroup X (y j))
    {a b : H}
    (ha : a ∈ unitaryFixedSubmodule π X)
    (haZ : a ∈ (unitaryFixedSubmodule π Z)ᗮ)
    (hb : ∀ i : ι, π (y i) b = b) :
    (Fintype.card ι : ℝ) * ‖inner ℂ a b‖ ^ 2 ≤
      ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  have hfix (i : ι) :
      π (y i) a ∈ unitaryFixedSubmodule π
        (heisenbergConjugateSubgroup X (y i)) := by
    rw [mem_unitaryFixedSubmodule]
    rintro ⟨_, ⟨g, hg, rfl⟩⟩
    have hga := (mem_unitaryFixedSubmodule π X a).mp ha ⟨g, hg⟩
    simp [MulAut.conj_apply, map_mul, hga]
  have horthZ (i : ι) :
      π (y i) a ∈ (unitaryFixedSubmodule π Z)ᗮ :=
    unitaryFixedSubmodule_orthogonal_map_of_centralizes
      π Z (y i) (hyZ i) haZ
  have hJZ (i : ι) :
      ∀ x : heisenbergConjugateSubgroup X (y i),
      ∀ z : Z, Commute (x : G) (z : G) := by
    rintro ⟨_, ⟨g, hg, rfl⟩⟩ z
    change Commute (y i * g * (y i)⁻¹) (z : G)
    exact ((hyZ i z).mul_left (hXZ ⟨g, hg⟩ z)).mul_left
      (hyZ i z).inv_left
  apply unitaryImages_inner_sq_mul_card_le
    (fun i : ι => π (y i)) a b hb
  intro i j hij
  exact unitaryFixedSubmodules_inner_eq_zero_of_commute_centerComplement
    π (heisenbergConjugateSubgroup X (y i))
    (heisenbergConjugateSubgroup X (y j)) Z
    (hcomm hij) (hJZ i) (hcenter hij)
    (hfix i) (hfix j) (horthZ j)
end SoficGroups
