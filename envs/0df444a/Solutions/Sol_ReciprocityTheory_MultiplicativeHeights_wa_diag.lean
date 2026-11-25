-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.wa_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:05:57.96631+00:00
-- url     : https://prove2.me/submissions/633dd1f5-863d-4c27-99f7-b22598c33d13

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_waR_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_symm
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_finrank_inf_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) :
    ∀ (n : ℕ) (W : Submodule K (Fin r → K)), finrank K W = n →
      (∀ x ∈ W, S.h x x = 0 → x = 0) →
      ∃ b : Fin n → Fin r → K, (∀ i, b i ∈ W) ∧ (∀ i, b i ≠ 0) ∧
        ∀ i j, i ≠ j → S.h (b i) (b j) = 0 := by
  intro n
  induction n with
  | zero =>
    intro W _ _
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro W hW han
    have hne : W ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hW
      omega
    obtain ⟨z, hzW, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hzz : S.h z z ≠ 0 := fun h => hz0 (han z hzW h)
    have hW' : finrank K ↥(W ⊓ LinearMap.ker (waR S z)) = n := by
      have h := wa_finrank_inf_ker W (waR S z) z hzW (by rw [waR_apply]; exact hzz)
      omega
    obtain ⟨b, hbW, hb0, hbo⟩ := ih (W ⊓ LinearMap.ker (waR S z)) hW' (fun x hx hxx => han x hx.1 hxx)
    have hk : ∀ k, S.h z (b k) = 0 := fun k => (hbW k).2
    refine ⟨Fin.cons z b, fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
    · cases i using Fin.cases with
      | zero => simpa using hzW
      | succ i => simpa using (hbW i).1
    · cases i using Fin.cases with
      | zero => simpa using hz0
      | succ i => simpa using hb0 i
    · cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using hk j
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.cons_succ, Fin.cons_zero]
          rw [wa_symm S z (b i), hk i, map_zero]
        | succ j =>
          simp only [Fin.cons_succ]
          exact hbo i j fun h => hij (by rw [h])
end ReciprocityTheory.MultiplicativeHeights
