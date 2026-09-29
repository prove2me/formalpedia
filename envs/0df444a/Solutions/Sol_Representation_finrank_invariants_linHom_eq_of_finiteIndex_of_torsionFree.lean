-- Prove2me | solution 1 for Representation.finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/19de96d2-7e3b-5c6b-8547-da4cf9b4c9a7

import Mathlib
import Theorems.Thm_Representation_finrank_invariants_linHom_modP_add_torsion_eq_of_finiteIndex
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree

set_option autoImplicit false
universe u
open Module
open scoped IntermediateField Pointwise

private theorem finrank_hom_eq_zero_of_subsingleton₀ {k : Type*} [Field k] {Δ : Type*} [Group Δ]
    {VN : Type*} [AddCommGroup VN] [Module k VN] (N : Representation k Δ VN)
    {VA : Type*} [AddCommGroup VA] [Module k VA] [Subsingleton VA]
    (PA : Representation k Δ VA) : finrank k (N.linHom PA).invariants = 0 := by
  haveI : Subsingleton (VN →ₗ[k] VA) := inferInstance
  apply finrank_zero_of_subsingleton

theorem solution
    {p : ℕ} [Fact p.Prime] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ p ∣ Fintype.card Δ)
    {A : Type*} [AddCommGroup A] (act : Δ →* AddAut A) (htf : ∀ a : A, p • a = 0 → a = 0)
    (B : AddSubgroup A) [B.FiniteIndex] (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)
    {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] [FiniteDimensional (ZMod p) VN]
    (N : Representation (ZMod p) Δ VN)
    {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA] [FiniteDimensional (ZMod p) VA]
    (PA : Representation (ZMod p) Δ VA)
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a)
    (hπAΔ : ∀ (d : Δ) (a : A), πA (act d a) = PA d (πA a))
    {VB : Type*} [AddCommGroup VB] [Module (ZMod p) VB] [FiniteDimensional (ZMod p) VB]
    (PB : Representation (ZMod p) Δ VB)
    (πB : B →+ VB) (hπB : Function.Surjective πB) (hkerB : ∀ b : B, πB b = 0 ↔ ∃ b' : B, p • b' = b)
    (hπBΔ : ∀ (d : Δ) (b : B), πB ⟨act d b, hB d b b.2⟩ = PB d (πB b)) :
    finrank (ZMod p) (N.linHom PA).invariants = finrank (ZMod p) (N.linHom PB).invariants := by
  have hranA : ∀ a : A, a ∈ Set.range (0 : PUnit →+ A) ↔ p • a = 0 := fun a =>
    ⟨fun ⟨u, hu⟩ => by rw [← hu, AddMonoidHom.zero_apply, smul_zero],
     fun h => ⟨PUnit.unit, by rw [AddMonoidHom.zero_apply, htf a h]⟩⟩
  have hranB : ∀ b : B, b ∈ Set.range (0 : PUnit →+ B) ↔ p • b = 0 := fun b =>
    ⟨fun ⟨u, hu⟩ => by rw [← hu, AddMonoidHom.zero_apply, smul_zero],
     fun h => ⟨PUnit.unit, by
      rw [AddMonoidHom.zero_apply, eq_comm]
      apply Subtype.ext
      apply htf
      have := congrArg (fun x : B => (x : A)) h
      simpa using this⟩⟩
  have key := Representation.finrank_invariants_linHom_modP_add_torsion_eq_of_finiteIndex hΔ act B hB N
    PA πA hπA hkerA hπAΔ
    (Representation.trivial (ZMod p) Δ PUnit) (0 : PUnit →+ A) (fun _ _ _ => Subsingleton.elim _ _) hranA
    (fun d w => by simp only [AddMonoidHom.zero_apply]; exact (map_zero _).symm)
    PB πB hπB hkerB hπBΔ
    (Representation.trivial (ZMod p) Δ PUnit) (0 : PUnit →+ B) (fun _ _ _ => Subsingleton.elim _ _) hranB
    (fun d w => by simp only [AddMonoidHom.zero_apply, ZeroMemClass.coe_zero]; exact (map_zero _).symm)
  rw [finrank_hom_eq_zero_of_subsingleton₀ N (Representation.trivial (ZMod p) Δ PUnit)] at key
  omega

end S_Representation_finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree
end P2MW
export P2MW.S_Representation_finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree (solution)
