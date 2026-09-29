-- Prove2me | solution 1 for Rep.finrank_invariants_tensor_eq_add_of_shortExact_of_trivial_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e202eb81-9498-55e9-a00e-039592824a8d

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Theorems.Thm_Rep_nonempty_iso_biprod_of_shortExact_of_trivial_of_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_finrank_invariants_tensor_eq_add_of_shortExact_of_trivial_of_coprime

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits"
open scoped Classical

namespace K4Aux

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits"

variable {k : Type} [Field k] {Γ : Type} [Group Γ]

theorem injective_of_comp_eq_id {A B : Rep.{0} k Γ} (f : A ⟶ B) (g : B ⟶ A) (h : f ≫ g = 𝟙 A) : Function.Injective f.hom := by
  intro x y hxy
  have hx : (f ≫ g).hom x = x := by rw [h]; rfl
  have hy : (f ≫ g).hom y = y := by rw [h]; rfl
  change g.hom (f.hom x) = x at hx
  change g.hom (f.hom y) = y at hy
  rw [← hx, ← hy, hxy]

theorem surjective_of_comp_eq_id {A B : Rep.{0} k Γ} (s : B ⟶ A) (g : A ⟶ B) (h : s ≫ g = 𝟙 B) : Function.Surjective g.hom := by
  intro y
  refine ⟨s.hom y, ?_⟩
  change (s ≫ g).hom y = y
  rw [h]
  rfl

theorem finrank_invariants_tensor_of_iso_biprod (N A B C : Rep.{0} k Γ) (e : C ≅ A ⊞ B)
    [FiniteDimensional k A] [FiniteDimensional k B] [FiniteDimensional k N] :
    Module.finrank k (C ⊗ N : Rep.{0} k Γ).ρ.invariants =
      Module.finrank k (A ⊗ N : Rep.{0} k Γ).ρ.invariants + Module.finrank k (B ⊗ N : Rep.{0} k Γ).ρ.invariants := by
  haveI := preservesBinaryBiproducts_of_preservesBinaryProducts (Rep.invariantsFunctor k Γ)
  haveI := preservesBinaryBiproducts_of_preservesBinaryProducts (tensorRight N : Rep.{0} k Γ ⥤ Rep.{0} k Γ)
  haveI : FiniteDimensional k (A ⊗ N : Rep.{0} k Γ) := inferInstanceAs (Module.Finite k (TensorProduct k A N))
  haveI : FiniteDimensional k (B ⊗ N : Rep.{0} k Γ) := inferInstanceAs (Module.Finite k (TensorProduct k B N))
  let e₁ : C ⊗ N ≅ (A ⊗ N) ⊞ (B ⊗ N) := (tensorRight N).mapIso e ≪≫ (tensorRight N).mapBiprod A B
  let F := Rep.invariantsFunctor k Γ
  let e₂ : F.obj (C ⊗ N) ≅ ModuleCat.of k (↥(A ⊗ N : Rep.{0} k Γ).ρ.invariants × ↥(B ⊗ N : Rep.{0} k Γ).ρ.invariants) :=
    F.mapIso e₁ ≪≫ F.mapBiprod _ _ ≪≫ ModuleCat.biprodIsoProd _ _
  have le : ↥(C ⊗ N : Rep.{0} k Γ).ρ.invariants ≃ₗ[k] (↥(A ⊗ N : Rep.{0} k Γ).ρ.invariants × ↥(B ⊗ N : Rep.{0} k Γ).ρ.invariants) :=
    e₂.toLinearEquiv
  rw [le.finrank_eq, Module.finrank_prod]

end K4Aux

theorem solution
    {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ] (Λ : Subgroup Γ) [Λ.Normal] [Finite (Γ ⧸ Λ)]
    (hcop : (Nat.card (Γ ⧸ Λ)).Coprime p)
    (X : ShortComplex (Rep.{0} (ZMod p) Γ)) (hX : X.ShortExact) [FiniteDimensional (ZMod p) X.X₂]
    (h₂ : ∀ s ∈ Λ, X.X₂.ρ s = 1)
    (N : Rep.{0} (ZMod p) Γ) [FiniteDimensional (ZMod p) N] :
    Module.finrank (ZMod p) (X.X₂ ⊗ N : Rep.{0} (ZMod p) Γ).ρ.invariants =
      Module.finrank (ZMod p) (X.X₁ ⊗ N : Rep.{0} (ZMod p) Γ).ρ.invariants +
      Module.finrank (ZMod p) (X.X₃ ⊗ N : Rep.{0} (ZMod p) Γ).ρ.invariants := by
  obtain ⟨e⟩ := Rep.nonempty_iso_biprod_of_shortExact_of_trivial_of_coprime Λ hcop X hX h₂
  haveI : FiniteDimensional (ZMod p) X.X₁ :=
    FiniteDimensional.of_injective (biprod.inl ≫ e.inv : X.X₁ ⟶ X.X₂).hom.toLinearMap
      (K4Aux.injective_of_comp_eq_id (biprod.inl ≫ e.inv) (e.hom ≫ biprod.fst) (by simp))
  haveI : FiniteDimensional (ZMod p) X.X₃ :=
    Module.Finite.of_surjective (e.hom ≫ biprod.snd : X.X₂ ⟶ X.X₃).hom.toLinearMap
      (K4Aux.surjective_of_comp_eq_id (biprod.inr ≫ e.inv) (e.hom ≫ biprod.snd) (by simp))
  exact K4Aux.finrank_invariants_tensor_of_iso_biprod N X.X₁ X.X₃ X.X₂ e

end S_Rep_finrank_invariants_tensor_eq_add_of_shortExact_of_trivial_of_coprime
end P2MW
export P2MW.S_Rep_finrank_invariants_tensor_eq_add_of_shortExact_of_trivial_of_coprime (solution)
