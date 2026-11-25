-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.herbrand_of_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:47:28.576123+00:00
-- url     : https://prove2.me/submissions/332defb7-8b62-444b-a97a-7dcac552d079

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_Herbrand
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrand
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_h_eq_of_finiteIndex
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_h_of_subsingleton
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_mem_ker_dHom_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_mk_eq_mk_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_nHom_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {G M : Type*} [Group G] [Fintype G] [AddCommGroup M] (ρ : Representation ℤ G M) (g₀ : G)
    (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (W : Submodule ℤ M) (hW1 : ∀ g, ∀ w ∈ W, ρ g w ∈ W)
    (hW2 : W.toAddSubgroup.FiniteIndex)
    (hW3 : ∀ w ∈ W, (∀ g, ρ g w = w) → ∃ w' ∈ W, ∑ g, ρ g w' = w)
    (hW4 : ∀ w ∈ W, ∑ g, ρ g w = 0 → ∃ w' ∈ W, ρ g₀ w' - w' = w) :
    Herbrand.HFin ρ g₀ ∧ Herbrand.h ρ g₀ = 1 := by
  let ρW : Representation ℤ G W :=
    { toFun := fun g => (ρ g).restrict (p := W) (q := W) (hW1 g)
      map_one' := LinearMap.ext fun x => Subtype.ext (by
        show ρ 1 x.1 = x.1
        rw [map_one]; rfl)
      map_mul' := fun a b => LinearMap.ext fun x => Subtype.ext (by
        show ρ (a * b) x.1 = ρ a (ρ b x.1)
        rw [map_mul]; rfl) }
  have hρ : ∀ g (x : W), ((ρW g x : W) : M) = ρ g x.1 := fun _ _ => rfl
  have hsum : ∀ x : W, ((∑ g, ρW g x : W) : M) = ∑ g, ρ g x.1 := by
    intro x
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun g _ => hρ g x
  have h0 : Subsingleton (Herbrand.TateZerothCohomology ρW g₀) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientAddGroup.induction_on with
    | H a =>
    induction b using QuotientAddGroup.induction_on with
    | H b =>
    rw [Herbrand.mk_eq_mk_iff]
    have hab : ((a : W) - (b : W)) ∈ (Herbrand.dHom ρW g₀).ker := (a - b).2
    rw [Herbrand.mem_ker_dHom_iff ρW g₀ hg] at hab
    obtain ⟨w', hw', hw⟩ := hW3 ((a : W) - (b : W) : W).1 ((a : W) - (b : W) : W).2
      (fun g => congrArg Subtype.val (hab g))
    refine ⟨⟨w', hw'⟩, ?_⟩
    rw [Herbrand.nHom_apply]
    exact Subtype.ext ((hsum _).trans hw)
  have h1 : Subsingleton (Herbrand.H1 ρW g₀) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientAddGroup.induction_on with
    | H a =>
    induction b using QuotientAddGroup.induction_on with
    | H b =>
    rw [Herbrand.mk_eq_mk_iff]
    have hab : ((a : W) - (b : W)) ∈ (Herbrand.nHom ρW).ker := (a - b).2
    rw [AddMonoidHom.mem_ker, Herbrand.nHom_apply] at hab
    obtain ⟨w', hw', hw⟩ := hW4 ((a : W) - (b : W) : W).1 ((a : W) - (b : W) : W).2
      ((hsum _).symm.trans (congrArg Subtype.val hab))
    exact ⟨⟨w', hw'⟩, Subtype.ext hw⟩
  obtain ⟨hf, hh⟩ := Herbrand.h_of_subsingleton ρW g₀
  have hfi : (W.subtype.toAddMonoidHom).range.FiniteIndex := by
    have : (W.subtype.toAddMonoidHom).range = W.toAddSubgroup := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩; exact y.2
      · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
    rw [this]; exact hW2
  obtain ⟨hiff, heq⟩ := Herbrand.h_eq_of_finiteIndex ρW ρ g₀ W.subtype.toAddMonoidHom
    Subtype.val_injective hfi (fun _ _ => rfl)
  exact ⟨hiff.1 hf, (heq hf).symm.trans hh⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
