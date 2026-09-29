-- Prove2me | solution 1 for Representation.finrank_invariants_eq_one_of_natCard_map_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/b3ae34a8-09fb-5e05-8d85-08b5e3522245

import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_finrank_invariants_eq_one_of_natCard_map_eq_two

set_option autoImplicit false

open scoped MatrixGroups

universe u

namespace LTB0
namespace InvolutionLine

variable {k : Type u} [Field k]

lemma mem_center_of_val_eq_smul_one (g : GL (Fin 2) k) (c : k)
    (hg : (g : Matrix (Fin 2) (Fin 2) k) = c • (1 : Matrix (Fin 2) (Fin 2) k)) :
    g ∈ Subgroup.center (GL (Fin 2) k) := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply Units.ext
  simp only [Units.val_mul, hg, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]

lemma eq_of_forall_mulVec_eq (M M' : Matrix (Fin 2) (Fin 2) k)
    (h : ∀ v, M.mulVec v = M'.mulVec v) : M = M' :=
  Matrix.ext_iff_mulVec.2 h

theorem finrank_fixed_eq_one (g : Matrix (Fin 2) (Fin 2) k) (hgg : g * g = 1)
    (hns : ∀ c : k, g ≠ c • (1 : Matrix (Fin 2) (Fin 2) k))
    (W : Submodule k (Fin 2 → k)) (hW : ∀ v, v ∈ W ↔ g.mulVec v = v) :
    Module.finrank k W = 1 := by
  classical

  have hne_top : W ≠ ⊤ := by
    intro htop
    apply hns 1
    rw [one_smul]
    apply eq_of_forall_mulVec_eq
    intro v
    have hv : v ∈ W := htop ▸ Submodule.mem_top
    rw [(hW v).1 hv, Matrix.one_mulVec]

  have hne_bot : W ≠ ⊥ := by
    intro hbot

    have hex : ∃ w : Fin 2 → k, g.mulVec w + w ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hns (-1)
      apply eq_of_forall_mulVec_eq
      intro w
      have hw := hall w
      have hw' : g.mulVec w = -w := eq_neg_of_add_eq_zero_left hw
      rw [hw', Matrix.smul_mulVec, Matrix.one_mulVec, neg_one_smul]
    obtain ⟨w, hw⟩ := hex
    have hfix : g.mulVec (g.mulVec w + w) = g.mulVec w + w := by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, add_comm]
    have hmem : g.mulVec w + w ∈ W := (hW _).2 hfix
    rw [hbot, Submodule.mem_bot] at hmem
    exact hw hmem
  have hlt : Module.finrank k W < 2 := by
    have := Submodule.finrank_lt hne_top
    simpa [Module.finrank_fin_fun] using this
  have hpos : Module.finrank k W ≠ 0 := by
    intro h0
    exact hne_bot (Submodule.finrank_eq_zero.1 h0)
  omega

lemma eq_one_or_eq_of_card_eq_two {G : Type*} [Group G] (h2 : Nat.card G = 2)
    (g : G) (hg : g ≠ 1) (h : G) : h = 1 ∨ h = g := by
  classical
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : G)).1 h2
  by_cases hh : h = 1
  · exact Or.inl hh
  · exact Or.inr ((hy h hh).trans (hy g hg).symm)

lemma exists_ne_one_of_card_eq_two {G : Type*} [Group G] (h2 : Nat.card G = 2) :
    ∃ g : G, g ≠ 1 ∧ g * g = 1 := by
  classical
  obtain ⟨y, hy1, -⟩ := (Nat.card_eq_two_iff' (1 : G)).1 h2
  have hfin : Finite G := Nat.finite_of_card_ne_zero (by omega)
  refine ⟨y, hy1, ?_⟩
  have := pow_card_eq_one' (G := G) (x := y)
  rw [h2, pow_two] at this
  exact this

end LTB0.InvolutionLine

open LTB0.InvolutionLine in
theorem solution
    {Γ : Type u} [Group Γ] {k : Type u} [Field k]
    (ρ : Γ →* GL (Fin 2) k) (I : Subgroup Γ)
    (hcard : Nat.card (I.map ρ) = 2)
    (hcent : ¬ I.map ρ ≤ Subgroup.center (GL (Fin 2) k)) :
    Module.finrank k
        (Representation.invariants
          ((Deformation.matrixRepresentation ρ).comp I.subtype)) = 1 := by
  classical

  obtain ⟨g', hg'1, hg'sq⟩ := exists_ne_one_of_card_eq_two hcard
  have hall : ∀ h : I.map ρ, h = 1 ∨ h = g' := eq_one_or_eq_of_card_eq_two hcard g' hg'1
  set g : GL (Fin 2) k := (g' : GL (Fin 2) k) with hgdef
  have hg1 : g ≠ 1 := fun h => hg'1 (Subtype.ext h)
  have hgg : (g : Matrix (Fin 2) (Fin 2) k) * g = 1 := by
    have : g * g = 1 := by
      have := congrArg (fun x : I.map ρ => (x : GL (Fin 2) k)) hg'sq
      simpa using this
    have := congrArg (fun x : GL (Fin 2) k => (x : Matrix (Fin 2) (Fin 2) k)) this
    simpa using this

  have himg : ∀ σ ∈ I, ρ σ = 1 ∨ ρ σ = g := by
    intro σ hσ
    have hmem : ρ σ ∈ I.map ρ := Subgroup.mem_map_of_mem ρ hσ
    rcases hall ⟨ρ σ, hmem⟩ with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

  obtain ⟨τ, hτI, hτ⟩ : ∃ τ ∈ I, ρ τ = g := by
    have : g ∈ I.map ρ := g'.2
    exact Subgroup.mem_map.1 this

  have hgcent : g ∉ Subgroup.center (GL (Fin 2) k) := by
    intro hgc
    apply hcent
    intro h hh
    rcases hall ⟨h, hh⟩ with h1 | h2
    · rw [show h = 1 from congrArg Subtype.val h1]; exact Subgroup.one_mem _
    · rw [show h = g from congrArg Subtype.val h2]; exact hgc
  have hns : ∀ c : k, (g : Matrix (Fin 2) (Fin 2) k) ≠ c • (1 : Matrix (Fin 2) (Fin 2) k) :=
    fun c hc => hgcent (mem_center_of_val_eq_smul_one g c hc)

  refine finrank_fixed_eq_one (g : Matrix (Fin 2) (Fin 2) k) hgg hns _ ?_
  intro v
  rw [Representation.mem_invariants]
  constructor
  · intro hv
    have := hv ⟨τ, hτI⟩
    simpa [Deformation.matrixRepresentation_apply, hτ] using this
  · intro hv x
    rcases himg x.1 x.2 with h | h
    · simp [Deformation.matrixRepresentation_apply, h]
    · simp [Deformation.matrixRepresentation_apply, h, hv]

end S_Representation_finrank_invariants_eq_one_of_natCard_map_eq_two
end P2MW
export P2MW.S_Representation_finrank_invariants_eq_one_of_natCard_map_eq_two (solution)
