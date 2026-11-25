-- Prove2me | solution 1 for SCCThm8.PRig.ctx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:57:43.316184+00:00
-- url     : https://prove2.me/submissions/aaa49bb7-414e-42b5-b432-b29e4b59b9d9

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_PowerRigidity

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.PRig
open Rig Function
variable {G : Type*} [Group G] {k m : ℕ} {f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G}
namespace SCCThm8.PRig
theorem _root_.solution (hP : Good k f₁ f₂ f₃) {A B C : Fin m → Finset (Fin (3 * k))}
    (hA : ∀ j, (A j).card = k) (hB : ∀ j, (B j).card = k) (hC : ∀ j, (C j).card = k)
    (hD : ∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) (j : Fin m) :
    ∀ X Y Z : Finset (Fin (3 * k)), X.card = k → Y.card = k → Z.card = k →
      Disjoint X Y → Disjoint X Z → Disjoint Y Z →
      f₁ (update A j X) * f₂ (update B j Y) * f₃ (update C j Z) = 1 := by
  intro X Y Z hX hY hZ h1 h2 h3
  apply hP
  · intro j'; by_cases h : j' = j
    · subst h; simp [hX]
    · simp [h, hA]
  · intro j'; by_cases h : j' = j
    · subst h; simp [hY]
    · simp [h, hB]
  · intro j'; by_cases h : j' = j
    · subst h; simp [hZ]
    · simp [h, hC]
  · intro j'; rcases eq_or_ne j' j with rfl | h
    · simpa using ⟨h1, h2, h3⟩
    · simpa [h] using hD j'
end SCCThm8.PRig
