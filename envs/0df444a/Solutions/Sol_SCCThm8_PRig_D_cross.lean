-- Prove2me | solution 1 for SCCThm8.PRig.D_cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:03:27.573309+00:00
-- url     : https://prove2.me/submissions/6f8f9a01-ab29-4bc9-a3d7-a394088edb46

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_PowerRigidity
public import Theorems.Thm_SCCThm8_PRig_D_spec
public import Theorems.Thm_SCCThm8_Rig_card_sw
public import Theorems.Thm_SCCThm8_Rig_ex1


set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.PRig
open Rig Function
variable {G : Type*} [Group G] {k m : ℕ} {f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G}
namespace SCCThm8.PRig
theorem _root_.solution (hk : 2 ≤ k) (hP : Good k f₁ f₂ f₃) {j j' : Fin m} (hjj : j ≠ j')
    {s t s' t' : Fin (3 * k)} (hst : s ≠ t) (hst' : s' ≠ t') :
    D k f₁ j s t * D k f₁ j' s' t' = D k f₁ j' s' t' * D k f₁ j s t := by
  obtain ⟨X, hX, hsX, htX⟩ := Rig.ex1 hk hst
  obtain ⟨Y, hY, hsY, htY⟩ := Rig.ex1 hk hst'
  let A : Fin m → Finset (Fin (3 * k)) := update (fun _ => X) j' Y
  have hAj : A j = X := by simp [A, hjj]
  have hAj' : A j' = Y := by simp [A]
  have hA : ∀ i, (A i).card = k := by
    intro i; rcases eq_or_ne i j' with rfl | h <;> simp [A, *]
  let A1 := update A j (sw X s t)
  let A2 := update A j' (sw Y s' t')
  have hA1 : ∀ i, (A1 i).card = k := by
    intro i; rcases eq_or_ne i j with rfl | h
    · simp [A1, card_sw hX hsX htX]
    · simp [A1, h, hA]
  have hA2 : ∀ i, (A2 i).card = k := by
    intro i; rcases eq_or_ne i j' with rfl | h
    · simp [A2, card_sw hY hsY htY]
    · simp [A2, h, hA]
  have hA1j' : A1 j' = Y := by simp [A1, hjj.symm, hAj']
  have hA2j : A2 j = X := by simp [A2, hjj, hAj]
  have e1 := D_spec hk hP A hA j s t (hAj ▸ hsX) (hAj ▸ htX)
  have e2 := D_spec hk hP A hA j' s' t' (hAj' ▸ hsY) (hAj' ▸ htY)
  have e3 := D_spec hk hP A1 hA1 j' s' t' (hA1j' ▸ hsY) (hA1j' ▸ htY)
  have e4 := D_spec hk hP A2 hA2 j s t (hA2j ▸ hsX) (hA2j ▸ htX)
  rw [hAj] at e1
  rw [hAj'] at e2
  rw [hA1j'] at e3
  rw [hA2j] at e4
  have hcomm : update A1 j' (sw Y s' t') = update A2 j (sw X s t) := update_comm hjj _ _ _
  rw [hcomm, e4] at e3
  have e2' : f₁ A2 = D k f₁ j' s' t' * f₁ A := e2
  have e1' : f₁ A1 = D k f₁ j s t * f₁ A := e1
  rw [e2', e1', ← mul_assoc, ← mul_assoc] at e3
  exact mul_right_cancel e3
end SCCThm8.PRig
