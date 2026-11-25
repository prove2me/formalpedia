-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.KTy.sort_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:37:30.429162+00:00
-- url     : https://prove2.me/submissions/3afdf8a8-24c4-40a8-adf7-13649f27db77

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.KTy
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
namespace PositivityTheory.Rg.Cz.KTy
theorem _root_.solution (l : ι → Fin n → ℤ) (hl : ∀ τ, Function.Injective (l τ)) :
    ∃ (s : ℤ) (w : ι → Equiv.Perm (Fin n)) (nu : ι → Fin n → ℕ),
      (∀ τ i, (nu τ i : ℤ) = s - l τ (w τ i) - i) ∧ ∀ τ, Monotone (nu τ) := by
  set s : ℤ := ∑ τ, ∑ k, |l τ k| with hs
  have hsl : ∀ τ k, 0 ≤ s - l τ k := by
    intro τ k
    have h1 : |l τ k| ≤ ∑ k', |l τ k'| :=
      Finset.single_le_sum (f := fun k' => |l τ k'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h2 : ∑ k', |l τ k'| ≤ s :=
      Finset.single_le_sum (f := fun τ' => ∑ k', |l τ' k'|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ τ)
    have h3 := le_abs_self (l τ k)
    linarith
  let w : ι → Equiv.Perm (Fin n) := fun τ => Tuple.sort (fun k => -l τ k)
  have hsm : ∀ τ, StrictMono (fun i => s - l τ (w τ i)) := by
    intro τ
    have h1 : Monotone ((fun k => -l τ k) ∘ w τ) := Tuple.monotone_sort _
    apply Monotone.strictMono_of_injective
    · intro a b hab
      have := h1 hab
      simp only [Function.comp_apply] at this
      linarith
    · intro a b hab
      simp only at hab
      exact (w τ).injective (hl τ (by linarith))
  have gap : ∀ τ (d : ℕ) (i j : Fin n), (j : ℕ) = i + d → s - l τ (w τ i) + d ≤ s - l τ (w τ j) := by
    intro τ d
    induction d with
    | zero =>
      intro i j h
      obtain rfl : j = i := Fin.ext (by omega)
      simp
    | succ d ih =>
      intro i j h
      have hj : (i : ℕ) + d < n := by have := j.isLt; omega
      have h1 := ih i ⟨i + d, hj⟩ rfl
      have h2 := hsm τ (show (⟨i + d, hj⟩ : Fin n) < j from by show (i : ℕ) + d < j; omega)
      simp only at h2
      push_cast
      linarith
  refine ⟨s, w, fun τ i => (s - l τ (w τ i) - i).toNat, fun τ i => ?_, fun τ a b hab => ?_⟩
  · have h1 := gap τ i ⟨0, i.pos⟩ i (by simp)
    have h2 := hsl τ (w τ ⟨0, i.pos⟩)
    simp only
    rw [Int.toNat_of_nonneg (by linarith)]
  · simp only
    have hab' : (a : ℕ) ≤ b := hab
    have h1 := gap τ ((b : ℕ) - a) a b (by omega)
    have e : (((b : ℕ) - (a : ℕ) : ℕ) : ℤ) = ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) := by omega
    apply Int.toNat_le_toNat
    linarith
end PositivityTheory.Rg.Cz.KTy
