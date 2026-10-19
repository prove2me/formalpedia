-- Prove2me | solution 1 for SoficGroups.ThompsonFTwoRelatorLEF.not_lef_of_thompsonF_two_relations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/e79a212e-0529-47cd-b86d-484a35262408

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_local_word_control
import Theorems.Thm_SoficGroups_KunRootedWordPower_RootedIndicatorMarkovModel_IsRootedAtRadius_mono

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFTwoRelatorLEF
open scoped commutatorElement
namespace SoficGroups.ThompsonFTwoRelatorLEF
theorem _root_.solution
    {G : Type*} [Group G] (a b : G)
    (h₁ : Commute (a * b⁻¹) (a⁻¹ * b * a))
    (h₂ : Commute (a * b⁻¹) ((a ^ 2)⁻¹ * b * a ^ 2))
    (hne : ¬ Commute a b)
    (hfinite : ∀ (n : ℕ) (x y : Equiv.Perm (Fin n)),
      Commute (x * y⁻¹) (x⁻¹ * y * x) →
      Commute (x * y⁻¹) ((x ^ 2)⁻¹ * y * x ^ 2) →
      Commute x y) :
    ¬ SoficGroups.LEF G := by
  classical
  intro hlef
  let φ : FreeGroup (Fin 2) →* G := FreeGroup.lift ![a, b]
  let r₁ : FreeGroup (Fin 2) := thompsonFRelator 1
  let r₂ : FreeGroup (Fin 2) := thompsonFRelator 2
  let w : FreeGroup (Fin 2) := thompsonFGeneratorCommutator
  let tracked : Finset (FreeGroup (Fin 2)) := {r₁, r₂, w}
  let controls : FreeGroup (Fin 2) → Finset G :=
    fun q => Classical.choose (SoficGroups.exists_local_word_control φ q)
  have hcontrols (q : FreeGroup (Fin 2)) :
      ∀ (H : Type) [Group H] (f : G → H),
        SoficGroups.LocalMultiplicativeOn (controls q) f →
          FreeGroup.lift (fun i => f (φ (FreeGroup.of i))) q = f (φ q) :=
    Classical.choose_spec (SoficGroups.exists_local_word_control φ q)
  let support : Finset G :=
    insert 1 (insert (φ w) (tracked.biUnion controls))
  obtain ⟨n, f, hf_inj, hf_local⟩ := hlef.approximate support
  let ψ : FreeGroup (Fin 2) →* Equiv.Perm (Fin n) :=
    FreeGroup.lift (fun i => f (φ (FreeGroup.of i)))
  have hword (q : FreeGroup (Fin 2)) (hq : q ∈ tracked) :
      ψ q = f (φ q) := by
    apply hcontrols q (Equiv.Perm (Fin n)) f
    apply hf_local.mono
    intro z hz
    simp only [support, Finset.mem_insert, Finset.mem_biUnion]
    exact Or.inr (Or.inr ⟨q, hq, hz⟩)
  have hφ₁ : φ r₁ = 1 := by
    simpa [φ, r₁, thompsonFRelator] using h₁.commutator_eq
  have hφ₂ : φ r₂ = 1 := by
    simpa [φ, r₂, thompsonFRelator] using h₂.commutator_eq
  have hψ₁ : ψ r₁ = 1 := by
    calc
      ψ r₁ = f (φ r₁) := hword r₁ (by simp [tracked])
      _ = 1 := by rw [hφ₁, hf_local.map_one]
  have hψ₂ : ψ r₂ = 1 := by
    calc
      ψ r₂ = f (φ r₂) := hword r₂ (by simp [tracked])
      _ = 1 := by rw [hφ₂, hf_local.map_one]
  have hf₁ :
      Commute (f a * (f b)⁻¹) ((f a)⁻¹ * f b * f a) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [ψ, φ, r₁, thompsonFRelator] using hψ₁
  have hf₂ :
      Commute (f a * (f b)⁻¹)
        (((f a) ^ 2)⁻¹ * f b * (f a) ^ 2) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [ψ, φ, r₂, thompsonFRelator] using hψ₂
  have hψw : ψ w = 1 := by
    simpa [ψ, φ, w, thompsonFGeneratorCommutator] using
      (hfinite n (f a) (f b) hf₁ hf₂).commutator_eq
  have hφw : φ w ≠ 1 := by
    intro hz
    apply hne
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [φ, w, thompsonFGeneratorCommutator] using hz
  apply hφw
  apply hf_inj
  · simp [support]
  · simp [support]
  calc
    f (φ w) = ψ w := (hword w (by simp [tracked])).symm
    _ = 1 := hψw
    _ = f 1 := hf_local.map_one.symm
end SoficGroups.ThompsonFTwoRelatorLEF
