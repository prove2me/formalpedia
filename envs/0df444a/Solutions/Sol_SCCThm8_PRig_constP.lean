-- Prove2me | solution 1 for SCCThm8.PRig.constP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:43.779682+00:00
-- url     : https://prove2.me/submissions/351eba5c-dad0-49a2-9511-f3e8f0c9bf85

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_PowerRigidity
public import Theorems.Thm_SCCThm8_Rig_const_of_swap


set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.PRig
open Rig Function
namespace SCCThm8.PRig
theorem _root_.solution {n m k : ℕ} {X : Type*} (F : (Fin m → Finset (Fin n)) → X)
    (h : ∀ A : Fin m → Finset (Fin n), (∀ j, (A j).card = k) → ∀ j s t, s ∈ A j → t ∉ A j →
      F (update A j (sw (A j) s t)) = F A)
    (A A' : Fin m → Finset (Fin n)) (hA : ∀ j, (A j).card = k) (hA' : ∀ j, (A' j).card = k) :
    F A = F A' := by
  have step : ∀ A : Fin m → Finset (Fin n), (∀ j, (A j).card = k) → ∀ j (Y : Finset (Fin n)),
      Y.card = k → F (update A j Y) = F A := by
    intro A hA j Y hY
    have := Rig.const_of_swap (k := k) (fun Y => F (update A j Y)) (by
      intro Z hZ s t hs ht
      have hv : ∀ j', (update A j Z j').card = k := by
        intro j'; rcases eq_or_ne j' j with rfl | h' <;> simp [*]
      have := h (update A j Z) hv j s t (by simpa using hs) (by simpa using ht)
      simpa using this) _ Y (A j) hY (hA j) rfl
    simpa using this
  let Ar : ℕ → Fin m → Finset (Fin n) := fun r j => if j.val < r then A' j else A j
  have hAr : ∀ r j, (Ar r j).card = k := by
    intro r j; simp only [Ar]; split_ifs <;> simp [*]
  have key : ∀ r, F (Ar r) = F A := by
    intro r
    induction r with
    | zero =>
      have e0 : Ar 0 = A := by funext j; simp [Ar]
      rw [e0]
    | succ r ih =>
      by_cases hr : r < m
      · have e : Ar (r + 1) = update (Ar r) ⟨r, hr⟩ (A' ⟨r, hr⟩) := by
          funext j
          rcases eq_or_ne j ⟨r, hr⟩ with rfl | h'
          · simp [Ar]
          · have : j.val ≠ r := fun h'' => h' (Fin.ext h'')
            simp only [Ar, update_of_ne h']
            split_ifs <;> first | rfl | omega
        rw [e, step _ (hAr r) _ _ (hA' _), ih]
      · have e : Ar (r + 1) = Ar r := by
          funext j
          have := j.isLt
          simp only [Ar]
          split_ifs <;> first | rfl | omega
        rw [e, ih]
  have e : Ar m = A' := by funext j; simp [Ar, j.isLt]
  rw [← key m, e]
end SCCThm8.PRig
