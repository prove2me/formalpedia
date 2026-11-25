-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.pair_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:23:29.098988+00:00
-- url     : https://prove2.me/submissions/3d9a994d-9430-4d42-810a-43014cb9729b

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegN
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegQ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_formM_witt
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wPart_outer
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wVal_outer


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
    (g : Fin r → K) (h2m : 2 * m ≤ r) (Lp : Submodule (𝓞 K) (Fin r → K))
    (hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y))
    (j : Fin r) (hj : (j : ℕ) < m) :
    ∀ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j),
      ∀ y ∈ (Lp ⊓ cutSub K r (Fin.rev j + 1)).map (projGe K r (Fin.rev j)),
        IsIntegralElt (S.c (x j) * y (Fin.rev j)) := by
  rintro _ ⟨x, ⟨hxL, hxc⟩, rfl⟩ _ ⟨y, ⟨hyL, hyc⟩, rfl⟩
  have hrev := Fin.val_rev j
  have hj' := j.isLt
  have e1 : projGe K r j x j = x j := by
    show (if (j : ℕ) ≤ j then x j else 0) = x j
    rw [if_pos le_rfl]
  have e2 : projGe K r (Fin.rev j) y (Fin.rev j) = y (Fin.rev j) := by
    show (if ((Fin.rev j : Fin r) : ℕ) ≤ (Fin.rev j : Fin r) then y (Fin.rev j) else 0) = _
    rw [if_pos le_rfl]
  rw [e1, e2]
  have h := hint x hxL y hyL
  rw [formM_witt, Finset.sum_eq_single j] at h
  · rwa [wVal_outer r m g j (Or.inl hj), wPart_outer r m j (Or.inl hj), one_mul] at h
  · intro a _ ha
    by_cases hlt : (a : ℕ) < j
    · have hao : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m := Or.inl (by omega)
      rw [wPart_outer r m a hao]
      have : y (Fin.rev a) = 0 := hyc _ (by rw [Fin.val_rev, Fin.val_rev]; omega)
      rw [this, mul_zero, mul_zero]
    · have : x a = 0 := hxc a (by have : (a : ℕ) ≠ j := fun e => ha (Fin.ext e); omega)
      rw [this, map_zero, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'
end ReciprocityTheory.MultiplicativeHeights.SemiPt
