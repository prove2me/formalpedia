-- Prove2me | solution 1 for ThompsonAmenability.exists_const_forall_isFolner_le_card
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T02:01:00.72402+00:00
-- url     : https://prove2.me/submissions/fe0be70d-8e57-4117-8e58-0aa288e700cc

import Theorems.Thm_MooreFoelner_exists_const_forall_isFolnerSet_towerExp_le_card
import Definitions.Def_CannonFloydParry
import Definitions.Def_MooreFoelner
import Definitions.Def_ThompsonAmenability
import Mathlib

/-!
# Moore's Theorem 1.1, transported from Moore's `F` to `F`

Moore multiplies elements of `F` as `f · g = g ∘ f` ("`f` followed by `g`"), so the group of the
Moore mission is the opposite group `Fᵐᵒᵖ` (`MooreFoelner.MooreF`); its Theorem 1.1 is the published
`MooreFoelner.exists_const_forall_isFolnerSet_towerExp_le_card`. Left translates in `F` are right
translates in `Fᵐᵒᵖ`, so `MulOpposite.op` carries generating sets, inverses, Følner sets and
cardinalities across unchanged.
-/

open ThompsonAmenability in
open scoped symmDiff in
theorem solution (Γ : Finset CannonFloydParry.F) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set CannonFloydParry.F) = ⊤) :
    ∃ C : ℝ, 1 < C ∧ ∀ (n : ℕ) (A : Finset CannonFloydParry.F),
      IsFolner Γ A (C ^ (-(n : ℤ))) → towerExp n 0 ≤ A.card := by
  classical
  -- Moore's `F` is `Fᵐᵒᵖ`: left translates in `F` are right translates in `Fᵐᵒᵖ`
  set Γ' : Finset MooreFoelner.MooreF := Γ.image MulOpposite.op with hΓ'
  have hsymm' : ∀ γ ∈ Γ', γ⁻¹ ∈ Γ' := by
    intro γ hγ
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hγ
    exact Finset.mem_image.mpr ⟨g⁻¹, hsymm g hg, (MulOpposite.op_inv g).symm⟩
  have hgen' : Subgroup.closure (Γ' : Set MooreFoelner.MooreF) = ⊤ := by
    have hset : (Γ' : Set MooreFoelner.MooreF) = MulOpposite.unop ⁻¹' (Γ : Set CannonFloydParry.F) := by
      ext x
      simp only [hΓ', Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.mem_preimage]
      constructor
      · rintro ⟨g, hg, rfl⟩; exact hg
      · intro hx; exact ⟨x.unop, hx, rfl⟩
    rw [hset, ← Subgroup.op_closure, hgen, Subgroup.op_top]
  obtain ⟨C, hC, h29⟩ :=
    MooreFoelner.exists_const_forall_isFolnerSet_towerExp_le_card Γ' hsymm' hgen'
  refine ⟨C, hC, fun n A hA => ?_⟩
  have hinj : Function.Injective (MulOpposite.op : CannonFloydParry.F → MooreFoelner.MooreF) :=
    MulOpposite.op_injective
  have hcard : (A.image MulOpposite.op).card = A.card := Finset.card_image_of_injective _ hinj
  rw [← hcard]
  apply h29 n
  unfold MooreFoelner.IsFolnerSet
  unfold IsFolner at hA
  rw [hcard]
  convert hA using 2
  rw [hΓ', Finset.sum_image (fun x _ y _ h => hinj h)]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  have himg : (A.image MulOpposite.op).image (· * MulOpposite.op g) =
      (A.image (g * ·)).image MulOpposite.op := by
    rw [Finset.image_image, Finset.image_image]
    rfl
  have key : (((A.image MulOpposite.op).image (· * MulOpposite.op g)) ∆
      (A.image MulOpposite.op)).card = ((A.image (g * ·)) ∆ A).card := by
    rw [himg, ← Finset.image_symmDiff _ _ hinj, Finset.card_image_of_injective _ hinj]
  exact_mod_cast (by convert key)
