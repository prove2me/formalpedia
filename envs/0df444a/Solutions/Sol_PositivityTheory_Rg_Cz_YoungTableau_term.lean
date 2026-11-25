-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.YoungTableau.term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:21.898576+00:00
-- url     : https://prove2.me/submissions/1abbe54e-1e49-40cb-a5f9-c477c5dc0863

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoung
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_alt_dup
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_alt_perm
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_exists_perm
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_isTab_comp
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_mem_colG
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_sg_perm
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_sg_zero
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
open PositivityTheory.Rg.Cz.YoungTableau
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Type} [DecidableEq ι]
  {Q : Type} [Fintype Q] [DecidableEq Q] {N : ℕ} {C : Type} [DecidableEq C]
namespace PositivityTheory.Rg.Cz.YoungTableau
theorem _root_.solution (tl : Fin N → ι) (col : Q ⊕ (Fin N ⊕ Fin N) → C) (b : Q ⊕ (Fin N ⊕ Fin N) → Fin n)
    (hT : IsTab col b) (h1 : ∀ p k, col (.inl p) ≠ col (.inr k)) (h2 : ∀ k k', col (.inr (.inl k)) ≠ col (.inr (.inr k')))
    (ξ : TV n M (Q ⊕ (Fin N ⊕ Fin N))) (σ : Equiv.Perm (Fin N)) :
    alt (colG col) ξ (b ∘ dbl σ) =
      ((sg (col ∘ inF Q N) (b ∘ inF Q N) ((b ∘ inF Q N) ∘ σ) * sg (col ∘ inS Q N) (b ∘ inS Q N) ((b ∘ inS Q N) ∘ σ) : ℤ) : ℂ)
        • alt (colG col) ξ b := by
  have hFtab : IsTab (col ∘ inF Q N) (b ∘ inF Q N) := by
    refine isTab_comp col b hT (inF Q N) ?_ ?_
    · intro x y hxy
      simpa [inF] using hxy
    · intro q y hq
      simp only [inF] at hq
      rcases q with q | k | k
      · exact absurd hq (h1 q _)
      · exact ⟨k, rfl⟩
      · exact absurd hq.symm (h2 y k)
  have hStab : IsTab (col ∘ inS Q N) (b ∘ inS Q N) := by
    refine isTab_comp col b hT (inS Q N) ?_ ?_
    · intro x y hxy
      simpa [inS] using hxy
    · intro q y hq
      simp only [inS] at hq
      rcases q with q | k | k
      · exact absurd hq (h1 q _)
      · exact absurd hq (h2 k y)
      · exact ⟨k, rfl⟩
  have key : ColInj col (b ∘ dbl σ) →
      (∃ π ∈ colG (col ∘ inF Q N), (b ∘ inF Q N) ∘ ⇑π = (b ∘ inF Q N) ∘ ⇑σ) ∧
      (∃ π ∈ colG (col ∘ inS Q N), (b ∘ inS Q N) ∘ ⇑π = (b ∘ inS Q N) ∘ ⇑σ) := by
    intro hc
    refine ⟨exists_perm _ _ hFtab σ ?_, exists_perm _ _ hStab σ ?_⟩
    · intro k k' hk hb'
      have := hc (inF Q N k) (inF Q N k') hk (by simpa [dbl, inF] using hb')
      simpa [inF] using this
    · intro k k' hk hb'
      have := hc (inS Q N k) (inS Q N k') hk (by simpa [dbl, inS] using hb')
      simpa [inS] using this
  have hdup : ¬ ColInj col (b ∘ dbl σ) → alt (colG col) ξ (b ∘ dbl σ) = 0 := by
    intro hc
    simp only [ColInj, not_forall] at hc
    obtain ⟨p, q, hcol, hbq, hpq⟩ := hc
    exact alt_dup col ξ _ p q hpq hcol hbq
  by_cases hF : ∃ π ∈ colG (col ∘ inF Q N), (b ∘ inF Q N) ∘ ⇑π = (b ∘ inF Q N) ∘ ⇑σ
  · by_cases hS : ∃ π ∈ colG (col ∘ inS Q N), (b ∘ inS Q N) ∘ ⇑π = (b ∘ inS Q N) ∘ ⇑σ
    · obtain ⟨πF, hπF, eF⟩ := hF
      obtain ⟨πS, hπS, eS⟩ := hS
      rw [← eF, ← eS, sg_perm _ _ hFtab.1 πF hπF, sg_perm _ _ hStab.1 πS hπS]
      rw [mem_colG] at hπF hπS
      have hπ : (Equiv.refl Q).sumCongr (πF.sumCongr πS) ∈ colG col := by
        rw [mem_colG]
        rintro (q | k | k)
        · rfl
        · simpa [inF] using hπF k
        · simpa [inS] using hπS k
      have hb : b ∘ dbl σ = b ∘ ⇑((Equiv.refl Q).sumCongr (πF.sumCongr πS)) := by
        funext p
        rcases p with q | k | k
        · rfl
        · simpa [dbl, inF] using (congrFun eF k).symm
        · simpa [dbl, inS] using (congrFun eS k).symm
      rw [hb, alt_perm col ξ b _ hπ, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_sumCongr]
      simp
    · rw [sg_zero _ _ _ hS, mul_zero, Int.cast_zero, zero_smul]
      exact hdup (fun hc => hS (key hc).2)
  · rw [sg_zero _ _ _ hF, zero_mul, Int.cast_zero, zero_smul]
    exact hdup (fun hc => hF (key hc).1)
end PositivityTheory.Rg.Cz.YoungTableau
