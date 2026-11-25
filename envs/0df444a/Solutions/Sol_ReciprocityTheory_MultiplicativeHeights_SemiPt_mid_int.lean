-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.mid_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:49:11.336344+00:00
-- url     : https://prove2.me/submissions/54205725-71e3-462d-873f-ae560360cb1a

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegN
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegQ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_formM_witt
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wPart_mid
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wPart_outer
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wVal_mid


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K) (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a)
    (Lp : Submodule (𝓞 K) (Fin r → K))
    (hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y)) :
    IsIntegralOn (midForm S m g hfix) ((Lp ⊓ cutSub K r (r - m)).map (projGe K r m)) := by
  rintro _ ⟨x, ⟨hxL, hxc⟩, rfl⟩ _ ⟨y, ⟨hyL, hyc⟩, rfl⟩
  have h := hint x hxL y hyL
  convert h using 1
  rw [formM_witt]
  simp only [HermForm.h, midForm, midG, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha := a.isLt
  show (if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then
      S.c (if m ≤ (a : ℕ) then x a else 0) * g a * (if m ≤ (a : ℕ) then y a else 0)
      else 0) = _
  by_cases hmid : m ≤ (a : ℕ) ∧ (a : ℕ) + m < r
  · have ho : ¬ ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) := by omega
    simp only [if_pos hmid, if_pos hmid.1]
    rw [wVal_mid r m g a ho, wPart_mid r m a ho]
    ring
  · rw [if_neg hmid]
    by_cases hlt : (a : ℕ) < m
    · have ho : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m := Or.inl hlt
      rw [wPart_outer r m a ho]
      have : y (Fin.rev a) = 0 := hyc _ (by rw [Fin.val_rev]; omega)
      rw [this, mul_zero, mul_zero]
    · have : x a = 0 := hxc a (by omega)
      rw [this, map_zero, zero_mul]
end ReciprocityTheory.MultiplicativeHeights.SemiPt
