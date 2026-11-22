-- Prove2me | solution 1 for UlmsTheorem.socle_extend_build_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:59.768682+00:00
-- url     : https://prove2.me/submissions/010f265e-ea31-4095-9a03-5a45fc911e90

module
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
public import Theorems.Thm_UlmsTheorem_mem_adjoinElem_iff
public import Theorems.Thm_UlmsTheorem_dvd_of_zsmul_mem_of_not_mem
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.pOrder_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero



set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
namespace UlmsTheorem
theorem _root_.solution
    {A : AddSubgroup G} {B : AddSubgroup H}
    (φ : A →+ B)
    {g : G} (hg_notin : g ∉ A) {h : H}
    (hpg_in : p • g ∈ A)
    (hrel : p • h = (φ ⟨p • g, hpg_in⟩ : H)) :
    ∃ φ' : adjoinElem A g →+ (⊤ : AddSubgroup H),
      (∀ a : A, (φ' ⟨a, le_adjoinElem (A := A) (g := g) a.prop⟩ : H) = φ a) ∧
      (φ' ⟨g, mem_adjoinElem_right (A := A) g⟩ : H) = h := by
  let ψ : A × ℤ →+ adjoinElem A g :=
    { toFun := fun z ↦
        ⟨(z.1 : G) + z.2 • g, (mem_adjoinElem_iff (A := A) (g := g)).2 ⟨z.1, z.1.prop, z.2, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := fun x y ↦ by
        apply Subtype.ext
        change ((x.1 + y.1 : A) : G) + (x.2 + y.2) • g =
          ((x.1 : G) + x.2 • g) + ((y.1 : G) + y.2 • g)
        rw [add_zsmul]
        change ((x.1 : G) + (y.1 : G)) + (x.2 • g + y.2 • g) =
          ((x.1 : G) + x.2 • g) + ((y.1 : G) + y.2 • g)
        abel }
  have hψ_surj : Function.Surjective ψ := fun x ↦ by
    rcases (mem_adjoinElem_iff (A := A) (g := g) (x := (x : G))).1 x.prop with ⟨a, ha, n, hn⟩
    exact ⟨(⟨a, ha⟩, n), by ext; exact hn⟩
  let χ : A × ℤ →+ H :=
    { toFun := fun z ↦ (φ z.1 : H) + z.2 • h
      map_zero' := by simp
      map_add' := fun x y ↦ by
        change (φ (x.1 + y.1) : H) + (x.2 + y.2) • h =
          ((φ x.1 : H) + x.2 • h) + ((φ y.1 : H) + y.2 • h)
        rw [map_add, add_zsmul]
        change ((φ x.1 : H) + (φ y.1 : H)) + (x.2 • h + y.2 • h) =
          ((φ x.1 : H) + x.2 • h) + ((φ y.1 : H) + y.2 • h)
        abel }
  -- `χ` carries `ψ`'s kernel: a relation forces `p ∣ z.2`, and then `hrel` turns
  -- the `h`-component into the `φ`-image of the `A`-component.
  have hker : ψ.ker ≤ χ.ker := by
    intro z hz
    rw [AddMonoidHom.mem_ker] at hz ⊢
    have hz0 : ((z.1 : G) + z.2 • g : G) = 0 :=
      congrArg (fun t : adjoinElem A g ↦ (t : G)) hz
    have hzA : z.2 • g ∈ A := by
      rw [show z.2 • g = -((z.1 : A) : G) by
        rw [eq_neg_iff_add_eq_zero]; simpa [add_comm] using hz0]
      exact A.neg_mem z.1.prop
    obtain ⟨k, hk⟩ := dvd_of_zsmul_mem_of_not_mem p hg_notin hpg_in z.2 hzA
    have hzA0 : z.1 + k • ⟨p • g, hpg_in⟩ = 0 :=
      Subtype.ext (by
        simpa [hk, mul_zsmul, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc] using hz0)
    calc
      χ z = (φ z.1 : H) + ((p : ℤ) * k) • h := by simp [χ, hk]
      _ = (φ z.1 : H) + k • (p • h) := by simp [mul_zsmul, Int.mul_comm]
      _ = (φ z.1 : H) + k • (φ ⟨p • g, hpg_in⟩ : H) := by rw [hrel]
      _ = (φ (z.1 + k • ⟨p • g, hpg_in⟩) : H) := by simp [map_add, map_zsmul]
      _ = 0 := by simp [hzA0]
  let φ0 : adjoinElem A g →+ H := ψ.liftOfSurjective hψ_surj ⟨χ, hker⟩
  have hφ0ψ : ∀ z : A × ℤ, φ0 (ψ z) = χ z := fun z ↦ by simp [φ0]
  refine ⟨φ0.codRestrict ⊤ fun x ↦ by simp, fun a ↦ ?_, ?_⟩
  · have hψa : ψ (a, 0) = ⟨(a : G), le_adjoinElem (A := A) (g := g) a.prop⟩ := by ext; simp [ψ]
    change φ0 ⟨(a : G), le_adjoinElem (A := A) (g := g) a.prop⟩ = φ a
    rw [← hψa]
    simpa [χ] using hφ0ψ (a, 0)
  · have hψg : ψ (0, 1) = ⟨g, mem_adjoinElem_right (A := A) g⟩ := by ext; simp [ψ]
    change φ0 ⟨g, mem_adjoinElem_right (A := A) g⟩ = h
    rw [← hψg]
    simpa [χ] using hφ0ψ (0, 1)
end UlmsTheorem
