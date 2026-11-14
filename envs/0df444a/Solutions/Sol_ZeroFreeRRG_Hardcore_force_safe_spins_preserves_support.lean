-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.force_safe_spins_preserves_support
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:07:57.808877+00:00
-- url     : https://prove2.me/submissions/6dc6b7d5-febc-4b65-94d2-c9b48881f7ef

import Theorems.Thm_ZeroFreeRRG_Hardcore_safe_spin_preserves_support
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (t : ℝ) (d n : ℕ) (M : Matching n d)
    (σ : Fin n → m.Spin) (S : Finset (Fin n)) (a₀ : m.Spin)
    (hπ : ∀ a, m.pi t a ≠ 0)
    (hsafeL : ∀ a, m.M t a₀ a ≠ 0) (hsafeR : ∀ a, m.M t a a₀ ≠ 0)
    (hw : weight m t M σ ≠ 0) :
    weight m t M (fun v => if v ∈ S then a₀ else σ v) ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hw
  | @insert v S hv ih =>
    have hh := safe_spin_preserves_support m t d n M (fun u => if u ∈ S then a₀ else σ u)
      v a₀ hπ hsafeL hsafeR ih
    have heq : (fun u => if u ∈ insert v S then a₀ else σ u) =
        Function.update (fun u => if u ∈ S then a₀ else σ u) v a₀ := by
      funext u
      by_cases h : u=v
      · subst u
        simp
      · simp [h]
    rw [heq]
    exact hh
