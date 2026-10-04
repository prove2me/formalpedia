-- Prove2me | solution 1 for TheoryOfGames.Minimax.saddlePoint_iff_mem_setA_setB
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T13:04:03.569752+00:00
-- url     : https://prove2.me/submissions/f529a858-23aa-4e88-9d98-103dfd6477d7

import Mathlib
import Definitions.Def_TheoryOfGames_Minimax_SaddlePoint

set_option autoImplicit false

namespace P2M_7e6d026c
open TheoryOfGames.Minimax

lemma minOver_le {X Y : Type*} (φ : X → Y → ℝ) (hφ : MaxMinAttained φ) (x : X) (y : Y) :
    minOver φ x ≤ φ x y := by
  obtain ⟨y₁, hy₁⟩ := hφ.min_attained x
  exact ciInf_le ⟨φ x y₁, by rintro _ ⟨z, rfl⟩; exact hy₁ z⟩ y

lemma le_maxOver {X Y : Type*} (φ : X → Y → ℝ) (hφ : MaxMinAttained φ) (x : X) (y : Y) :
    φ x y ≤ maxOver φ y := by
  obtain ⟨x₁, hx₁⟩ := hφ.max_attained y
  exact le_ciSup (f := fun x => φ x y) ⟨φ x₁ y, by rintro _ ⟨z, rfl⟩; exact hx₁ z⟩ x

lemma minOver_eq {X Y : Type*} (φ : X → Y → ℝ) (hφ : MaxMinAttained φ) (x : X) (y : Y)
    (h : ∀ y', φ x y ≤ φ x y') : minOver φ x = φ x y :=
  le_antisymm (minOver_le φ hφ x y) (by
    have : Nonempty Y := ⟨y⟩
    exact le_ciInf h)

lemma maxOver_eq {X Y : Type*} (φ : X → Y → ℝ) (hφ : MaxMinAttained φ) (x : X) (y : Y)
    (h : ∀ x', φ x' y ≤ φ x y) : maxOver φ y = φ x y :=
  le_antisymm (by
    have : Nonempty X := ⟨x⟩
    exact ciSup_le h) (le_maxOver φ hφ x y)

lemma maxMin_eq {X Y : Type*} (φ : X → Y → ℝ) (x₀ : X) (h : x₀ ∈ setA φ) :
    maxMin φ = minOver φ x₀ :=
  le_antisymm (by
    have : Nonempty X := ⟨x₀⟩
    exact ciSup_le h)
    (le_ciSup (f := fun x => minOver φ x) ⟨minOver φ x₀, by rintro _ ⟨z, rfl⟩; exact h z⟩ x₀)

lemma minMax_eq {X Y : Type*} (φ : X → Y → ℝ) (y₀ : Y) (h : y₀ ∈ setB φ) :
    minMax φ = maxOver φ y₀ :=
  le_antisymm
    (ciInf_le (f := fun y => maxOver φ y) ⟨maxOver φ y₀, by rintro _ ⟨z, rfl⟩; exact h z⟩ y₀)
    (by
      have : Nonempty Y := ⟨y₀⟩
      exact le_ciInf h)

end P2M_7e6d026c

open TheoryOfGames.Minimax in
theorem solution {X Y : Type*} (φ : X → Y → ℝ) (hφ : MaxMinAttained φ)
    (heq : maxMin φ = minMax φ) (x₀ : X) (y₀ : Y) :
    IsSaddlePoint φ x₀ y₀ ↔ x₀ ∈ setA φ ∧ y₀ ∈ setB φ := by
  constructor
  · rintro ⟨h1, h2⟩
    have e1 := P2M_7e6d026c.minOver_eq φ hφ x₀ y₀ h2
    have e2 := P2M_7e6d026c.maxOver_eq φ hφ x₀ y₀ h1
    refine ⟨fun x => ?_, fun y => ?_⟩
    · rw [e1]; exact (P2M_7e6d026c.minOver_le φ hφ x y₀).trans (h1 x)
    · rw [e2]; exact (h2 y).trans (P2M_7e6d026c.le_maxOver φ hφ x₀ y)
  · rintro ⟨hA, hB⟩
    have e : minOver φ x₀ = maxOver φ y₀ := by
      rw [← P2M_7e6d026c.maxMin_eq φ x₀ hA, ← P2M_7e6d026c.minMax_eq φ y₀ hB, heq]
    refine ⟨fun x => ?_, fun y => ?_⟩
    · calc φ x y₀ ≤ maxOver φ y₀ := P2M_7e6d026c.le_maxOver φ hφ x y₀
        _ = minOver φ x₀ := e.symm
        _ ≤ φ x₀ y₀ := P2M_7e6d026c.minOver_le φ hφ x₀ y₀
    · calc φ x₀ y₀ ≤ maxOver φ y₀ := P2M_7e6d026c.le_maxOver φ hφ x₀ y₀
        _ = minOver φ x₀ := e.symm
        _ ≤ φ x₀ y := P2M_7e6d026c.minOver_le φ hφ x₀ y
