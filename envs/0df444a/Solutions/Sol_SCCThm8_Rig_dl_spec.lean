-- Prove2me | solution 1 for SCCThm8.Rig.dl_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:55:40.505228+00:00
-- url     : https://prove2.me/submissions/de0384f5-6749-4243-98f0-2ad093eff8f8

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Theorems.Thm_SCCThm8_Rig_indep

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}
variable {G : Type*} [Group G] {k : ℕ} {f₁ f₂ f₃ : Finset (Fin (3 * k)) → G}
namespace SCCThm8.Rig
theorem _root_.solution (hk : 2 ≤ k)
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1)
    (A : Finset (Fin (3 * k))) (hA : A.card = k) (i j : Fin (3 * k)) (hi : i ∈ A) (hj : j ∉ A) :
    f₁ (sw A i j) = dl k f₁ i j * f₁ A := by
  have h : ∃ A : Finset (Fin (3 * k)), A.card = k ∧ i ∈ A ∧ j ∉ A := ⟨A, hA, hi, hj⟩
  have hc := h.choose_spec
  simp only [dl, h, ↓reduceDIte]
  rw [ ← indep hk hP hA hc.1 hi hc.2.1 hj hc.2.2]
  group
end SCCThm8.Rig
