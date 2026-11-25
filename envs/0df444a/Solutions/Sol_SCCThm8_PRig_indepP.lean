-- Prove2me | solution 1 for SCCThm8.PRig.indepP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:59:57.903503+00:00
-- url     : https://prove2.me/submissions/0e534f92-f19f-47e4-ba82-defc9d9157e3

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_PowerRigidity
public import Theorems.Thm_SCCThm8_PRig_swap_idP
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
theorem _root_.solution (hk : 2 ≤ k) (hP : Good k f₁ f₂ f₃) {A A' : Fin m → Finset (Fin (3 * k))}
    (hA : ∀ j, (A j).card = k) (hA' : ∀ j, (A' j).card = k) {j : Fin m} {s t : Fin (3 * k)}
    (hs : s ∈ A j) (hs' : s ∈ A' j) (ht : t ∉ A j) (ht' : t ∉ A' j) :
    f₁ (update A j (sw (A j) s t)) * (f₁ A)⁻¹ = f₁ (update A' j (sw (A' j) s t)) * (f₁ A')⁻¹ := by
  have hex : ∀ j', ∃ C : Finset (Fin (3 * k)), C.card = k ∧
      (if j' = j then {t} else ∅) ⊆ C ∧ Disjoint C (A j' ∪ A' j') := by
    intro j'
    refine exists_kset _ _ ?_ ?_ ?_
    · split_ifs with h
      · subst h; simp [ht, ht']
      · simp
    · split_ifs <;> simp; omega
    · have := card_union_le (A j') (A' j'); rw [hA j', hA' j'] at this; omega
  choose C hC hsub hdisj using hex
  have htC : t ∈ C j := hsub j (by simp)
  rw [swap_idP hP hA hC (fun j' => (hdisj j').symm.mono_left subset_union_left) hs htC,
    swap_idP hP hA' hC (fun j' => (hdisj j').symm.mono_left subset_union_right) hs' htC]
end SCCThm8.PRig
