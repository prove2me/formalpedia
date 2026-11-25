-- Prove2me | solution 1 for PI.FockWtDegWork.omE_diag_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:53:07.576486+00:00
-- url     : https://prove2.me/submissions/198bdacf-5e72-4839-89b1-e14c737948fd

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight
import Theorems.Thm_P2M_PI_FockWtDegWork_X_mul_monomial__8f48671e9716

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
open PI PI.FockWtDegWork
namespace PI.FockWtDegWork
theorem _root_.solution {p q r s : ℕ} (l : Ln p q r s) (α : Ln p q r s →₀ ℕ) :
    omE l l (MvPolynomial.monomial α (1 : ℂ)) =
      ((lw l α : ℚ) : ℂ) • MvPolynomial.monomial α (1 : ℂ) := by
  have hE : FockH1Action.omE l l (MvPolynomial.monomial α (1 : ℂ)) =
      FockH1Action.raiB l (FockH1Action.lowB l (MvPolynomial.monomial α 1)) + (1 / 2 : ℂ) • MvPolynomial.monomial α 1 := by
    unfold FockH1Action.omE
    rw [if_pos rfl] <;> rfl
  have hm : ∀ c : ℂ, MvPolynomial.monomial α c = c • MvPolynomial.monomial α (1 : ℂ) := fun c => by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hpd : ∀ (m : FockH1Action.Ln p q r s →₀ ℕ) (c : ℂ), MvPolynomial.pderiv l (MvPolynomial.monomial m c) =
      MvPolynomial.monomial (m - Finsupp.single l 1) (c * (m l : ℂ)) := fun m c =>
    MvPolynomial.pderiv_monomial
  rw [hE]
  cases hl : FockH1Action.linePos l
  · have hc : ¬ (FockH1Action.linePos l = true) := by simp [hl]
    have h1 : FockH1Action.lowB l (MvPolynomial.monomial α (1 : ℂ)) = MvPolynomial.X l * MvPolynomial.monomial α 1 := by
      rw [FockH1Action.lowB, if_neg hc] <;> rfl
    have h2 : ∀ x, FockH1Action.raiB l x = -MvPolynomial.pderiv l x := fun x => by
      rw [FockH1Action.raiB, if_neg hc] <;> rfl
    have hw : ((lw l α : ℚ) : ℂ) = -(α l : ℂ) - 1 / 2 := by
      rw [lw, if_neg hc]; push_cast; ring
    have hs : Finsupp.single l 1 + α - Finsupp.single l 1 = α := by
      first
        | exact add_tsub_cancel_left _ _
        | (ext k; simp)
    have hv : (((Finsupp.single l 1 + α : FockH1Action.Ln p q r s →₀ ℕ) l : ℕ) : ℂ) = (α l : ℂ) + 1 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_same]; push_cast; ring
    rw [h1, h2, X_mul_monomial', hpd, hs, hv, one_mul, hm ((α l : ℂ) + 1), ← neg_smul,
      ← add_smul, hw]
    congr 1
    ring
  · have h1 : FockH1Action.lowB l (MvPolynomial.monomial α (1 : ℂ)) =
        MvPolynomial.pderiv l (MvPolynomial.monomial α 1) := by
      rw [FockH1Action.lowB, if_pos hl] <;> rfl
    have h2 : ∀ x, FockH1Action.raiB l x = MvPolynomial.X l * x := fun x => by
      rw [FockH1Action.raiB, if_pos hl] <;> rfl
    have hw : ((lw l α : ℚ) : ℂ) = (α l : ℂ) + 1 / 2 := by
      rw [lw, if_pos hl]; push_cast; ring
    have key : MvPolynomial.X l * MvPolynomial.monomial (α - Finsupp.single l 1) (1 * (α l : ℂ)) =
        (α l : ℂ) • MvPolynomial.monomial α 1 := by
      rw [one_mul]
      by_cases h0 : α l = 0
      · simp [h0]
      · have hs : Finsupp.single l 1 + (α - Finsupp.single l 1) = α := by
          first
            | exact add_tsub_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h0))
            | (ext k
               simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
               split_ifs with hk <;> (try subst hk) <;> omega)
        rw [X_mul_monomial', hs, hm (α l : ℂ)]
    rw [h2, h1, hpd, key, hw, add_smul]
end PI.FockWtDegWork
