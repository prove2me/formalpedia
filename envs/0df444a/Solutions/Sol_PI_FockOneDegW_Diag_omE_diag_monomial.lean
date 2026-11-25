-- Prove2me | solution 1 for PI.FockOneDegW.Diag.omE_diag_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:17.797794+00:00
-- url     : https://prove2.me/submissions/38c7903d-5e94-4c5e-92c2-7d6da331cd7f

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Theorems.Thm_P2M_PI_FockOneDegW_Diag_X_mul_monomial__c9dbc2e71708

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockOneDegW PI.FockOneDegW.Diag
namespace PI.FockOneDegW.Diag
theorem _root_.solution {p q r s : ℕ} (l : Ln p q r s) (α : Ln p q r s →₀ ℕ) :
    omE l l (MvPolynomial.monomial α (1 : ℂ)) =
      ((lw l α : ℚ) : ℂ) • MvPolynomial.monomial α (1 : ℂ) := by
  unfold FockH1Action.omE
  rw [if_pos rfl]
  unfold FockH1Action.raiB FockH1Action.lowB lw
  cases hl : FockH1Action.linePos l
  · simp only [Bool.false_eq_true, ↓reduceIte, LinearMap.add_apply, Module.End.mul_apply, LinearMap.neg_apply,
      LinearMap.smul_apply, Module.End.one_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
    rw [X_mul_monomial', MvPolynomial.pderiv_monomial, add_tsub_cancel_left]
    refine MvPolynomial.ext _ _ fun β => ?_
    simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_neg, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial,
      Finsupp.add_apply, Finsupp.single_eq_same]
    by_cases hb : α = β <;> simp [hb] <;> ring
  · simp only [↓reduceIte, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.one_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
    rw [MvPolynomial.pderiv_monomial, X_mul_monomial']
    by_cases h0 : α l = 0
    · refine MvPolynomial.ext _ _ fun β => ?_
      simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, h0]
      by_cases hb : α = β <;> simp [hb]
    · have hs : Finsupp.single l 1 + (α - Finsupp.single l 1) = α := by
        ext i
        by_cases hi : i = l
        · subst hi
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
          omega
        · have hli : l ≠ i := fun h => hi h.symm
          simp [hli]
      rw [hs]
      refine MvPolynomial.ext _ _ fun β => ?_
      simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
      by_cases hb : α = β <;> simp [hb]
end PI.FockOneDegW.Diag
