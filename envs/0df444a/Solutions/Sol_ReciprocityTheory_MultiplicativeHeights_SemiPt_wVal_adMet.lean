-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.wVal_adMet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:40:09.708796+00:00
-- url     : https://prove2.me/submissions/37169589-a422-4fed-b8b9-237e376abea9

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegF
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wPart_outer
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wPart_mid
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wVal_outer
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
theorem _root_.solution {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K)
    (dd : Fin r → ℝ) (h2m : 2 * m ≤ r)
    (hg : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0) (σ : K →+* ℂ)
    (hreal : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → conj (σ (g i)) = σ (g i))
    (i : Fin r) :
    σ (wVal r m g i) * (((adMet r m g dd σ (wPart r m i) : ℝ) : ℂ))⁻¹ *
      σ (wVal r m g (wPart r m i)) = ((adMet r m g dd σ i : ℝ) : ℂ) := by
  have hi := i.isLt
  by_cases h1 : (i : ℕ) < m
  · have ho : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m := Or.inl h1
    rw [wPart_outer r m i ho, wVal_outer r m g i ho,
      wVal_outer r m g (Fin.rev i) (by simp only [Fin.val_rev]; omega)]
    unfold adMet
    simp only [Fin.val_rev, Fin.rev_rev]
    rw [if_neg (show ¬ (r - ((i : ℕ) + 1) < m) by omega), if_pos (show r ≤ r - ((i : ℕ) + 1) + m by omega),
      if_pos h1]
    simp
  · by_cases h2 : r ≤ (i : ℕ) + m
    · have ho : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m := Or.inr h2
      rw [wPart_outer r m i ho, wVal_outer r m g i ho,
        wVal_outer r m g (Fin.rev i) (by simp only [Fin.val_rev]; omega)]
      unfold adMet
      simp only [Fin.val_rev]
      rw [if_pos (show r - ((i : ℕ) + 1) < m by omega), if_neg h1, if_pos h2]
      simp
    · have hm : ¬ ((i : ℕ) < m ∨ r ≤ (i : ℕ) + m) := by omega
      rw [wPart_mid r m i hm, wVal_mid r m g i hm]
      unfold adMet
      rw [if_neg h1, if_neg h2]
      have hr := hreal i (by omega) (by omega)
      have hne : σ (g i) ≠ 0 := (map_ne_zero σ).mpr (hg i (by omega) (by omega))
      have hz : ((σ (g i)).re : ℂ) = σ (g i) := Complex.conj_eq_iff_re.mp hr
      rw [← hz, Complex.norm_real, Real.norm_eq_abs]
      have hx : (σ (g i)).re ≠ 0 := by
        intro h0
        apply hne
        rw [← hz, h0, Complex.ofReal_zero]
      have habs : ((|(σ (g i)).re| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr hx
      have hsq : ((σ (g i)).re : ℂ) * (σ (g i)).re = ((|(σ (g i)).re| : ℝ) : ℂ) * |(σ (g i)).re| := by
        exact_mod_cast (abs_mul_abs_self (σ (g i)).re).symm
      calc ((σ (g i)).re : ℂ) * (↑|(σ (g i)).re|)⁻¹ * ((σ (g i)).re : ℂ)
          = (((σ (g i)).re : ℂ) * (σ (g i)).re) * (↑|(σ (g i)).re|)⁻¹ := by ring
        _ = (((|(σ (g i)).re| : ℝ) : ℂ) * |(σ (g i)).re|) * (↑|(σ (g i)).re|)⁻¹ := by rw [hsq]
        _ = ((|(σ (g i)).re| : ℝ) : ℂ) := by field_simp
end ReciprocityTheory.MultiplicativeHeights.SemiPt
