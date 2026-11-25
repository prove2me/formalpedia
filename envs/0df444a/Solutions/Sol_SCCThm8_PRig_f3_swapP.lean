-- Prove2me | solution 1 for SCCThm8.PRig.f3_swapP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:03:24.639467+00:00
-- url     : https://prove2.me/submissions/a4da7a1c-52d2-4f82-9f28-52889542982f

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_PowerRigidity
public import Theorems.Thm_SCCThm8_PRig_swap_idP
public import Theorems.Thm_SCCThm8_PRig_D_spec
public import Theorems.Thm_SCCThm8_Rig_exists_kset


set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.PRig
open Rig Function
variable {G : Type*} [Group G] {k m : ℕ} {f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G}
namespace SCCThm8.PRig
theorem _root_.solution (hk : 2 ≤ k) (hP : Good k f₁ f₂ f₃) (C : Fin m → Finset (Fin (3 * k)))
    (hC : ∀ j, (C j).card = k) (j : Fin m) (t s : Fin (3 * k)) (ht : t ∈ C j) (hs : s ∉ C j) :
    f₃ (update C j (sw (C j) t s)) = f₃ C * (D k f₁ j s t)⁻¹ := by
  have hex : ∀ j', ∃ A : Finset (Fin (3 * k)), A.card = k ∧
      (if j' = j then {s} else ∅) ⊆ A ∧ Disjoint A (C j') := by
    intro j'
    refine exists_kset _ _ ?_ ?_ ?_
    · split_ifs with h
      · subst h; simp [hs]
      · simp
    · split_ifs <;> simp; omega
    · rw [hC j']; omega
  choose A hA hsub hdisj using hex
  have hsA : s ∈ A j := hsub j (by simp)
  have htA : t ∉ A j := fun h => disjoint_left.mp (hdisj j) h ht
  have e := swap_idP hP hA hC hdisj hsA ht
  rw [D_spec hk hP A hA j s t hsA htA] at e
  have e' : D k f₁ j s t = (f₃ (update C j (sw (C j) t s)))⁻¹ * f₃ C := by rw [← e]; group
  rw [e']; group
end SCCThm8.PRig
