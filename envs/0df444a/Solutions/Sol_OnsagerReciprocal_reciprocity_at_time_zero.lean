-- Prove2me | solution 1 for OnsagerReciprocal.reciprocity_at_time_zero
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-10T23:44:45.450503+00:00
-- url     : https://prove2.me/submissions/e870a8b5-f533-4856-978f-4a14cdb9ef45

import Mathlib
import Definitions.Def_OnsagerReciprocal_basic
import Theorems.Thm_OnsagerReciprocal_timeCorrelation_hasDerivAt

open Matrix
set_option autoImplicit false

/-- At `t = 0`, `Ξ(0) = β ξ(0) = β x = X`, since `exp 0 = 1`. -/
private lemma meanConjugate_zero_eq {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    OnsagerReciprocal.meanConjugate β lam 0 x = OnsagerReciprocal.conjugate β x := by
  simp [OnsagerReciprocal.meanConjugate, OnsagerReciprocal.meanFluctuation,
    OnsagerReciprocal.conjugate, NormedSpace.exp_zero]

/-- If `g` has derivative `d` at `0` and vanishes on `[0, ∞)`, then `d = 0`: the one-sided
derivative within `Ici 0` is unique and equals that of the constant `0`. -/
private lemma deriv_eq_zero_of_eventually {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d 0)
    (h0 : ∀ s : ℝ, 0 ≤ s → g s = 0) : d = 0 := by
  have h1 : HasDerivWithinAt g d (Set.Ici 0) 0 := hg.hasDerivWithinAt
  have h2 : HasDerivWithinAt g 0 (Set.Ici 0) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) (Set.Ici (0 : ℝ)) (0 : ℝ)).congr
      (fun s hs => h0 s hs) (h0 0 le_rfl)
  exact (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ h1 h2

/-- Differentiate `⟨xᵢ(t)xₖ(0)⟩ = ⟨xₖ(t)xᵢ(0)⟩` (valid for `t ≥ 0`) at `t = 0` from the right. -/
theorem solution {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef)
    (hrev : ∀ t : ℝ, 0 ≤ t → ∀ i k : Fin n,
      OnsagerReciprocal.timeCorrelation β lam t i k =
        OnsagerReciprocal.timeCorrelation β lam t k i)
    (i k : Fin n) :
    ∑ l : Fin n, OnsagerReciprocal.kineticCoeff β lam i l *
        OnsagerReciprocal.fluctuationAverage β (fun x => OnsagerReciprocal.conjugate β x l * x k) =
      ∑ l : Fin n, OnsagerReciprocal.kineticCoeff β lam k l *
        OnsagerReciprocal.fluctuationAverage β (fun x => OnsagerReciprocal.conjugate β x l * x i) := by
  have hik := OnsagerReciprocal.timeCorrelation_hasDerivAt β lam hβ i k 0
  have hki := OnsagerReciprocal.timeCorrelation_hasDerivAt β lam hβ k i 0
  have hd := deriv_eq_zero_of_eventually (hik.sub hki)
    (fun s hs => sub_eq_zero.mpr (hrev s hs i k))
  simp only [meanConjugate_zero_eq] at hd
  linarith
