-- Prove2me | solution 1 for SCCThm8.PRig.D_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:01:28.018375+00:00
-- url     : https://prove2.me/submissions/f3c6ce97-87e4-4783-b6d4-64addfc5f06e

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_PowerRigidity
public import Theorems.Thm_SCCThm8_PRig_indepP

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.PRig
open Rig Function
variable {G : Type*} [Group G] {k m : ℕ} {f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G}
namespace SCCThm8.PRig
theorem _root_.solution (hk : 2 ≤ k) (hP : Good k f₁ f₂ f₃) (A : Fin m → Finset (Fin (3 * k)))
    (hA : ∀ j, (A j).card = k) (j : Fin m) (s t : Fin (3 * k)) (hs : s ∈ A j) (ht : t ∉ A j) :
    f₁ (update A j (sw (A j) s t)) = D k f₁ j s t * f₁ A := by
  have h : ∃ A : Fin m → Finset (Fin (3 * k)), (∀ j', (A j').card = k) ∧ s ∈ A j ∧ t ∉ A j :=
    ⟨A, hA, hs, ht⟩
  have hc := h.choose_spec
  simp only [D, h, ↓reduceDIte]
  rw [← indepP hk hP hA hc.1 hs hc.2.1 ht hc.2.2]
  group
end SCCThm8.PRig
