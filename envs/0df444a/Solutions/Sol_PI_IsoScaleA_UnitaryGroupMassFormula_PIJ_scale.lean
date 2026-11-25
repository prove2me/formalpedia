-- Prove2me | solution 1 for PI.IsoScaleA.UnitaryGroupMassFormula.PIJ_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:37.522858+00:00
-- url     : https://prove2.me/submissions/c8d110f2-4ea1-4b7c-a8ed-d52770190812

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoScaleA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryScaleCount_CardEqSumColLen
import Theorems.Thm_PI_IsoScaleA_UnitaryGroupMassFormula_card_eq_sum_colLen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoScaleA PI.IsoScaleA.UnitaryGroupMassFormula
open PI.IsoScaleA
namespace PI.IsoScaleA.UnitaryGroupMassFormula
theorem _root_.solution {Lt T : Type} [Fintype Lt] (tp : Lt → T) {N N' : ℕ} (nu : Lt → YoungDiagram)
    (c s : T → ℂ) (I : ColChoice N' nu) (J : ColChoice N nu) :
    PIJ tp nu (fun τ => c τ * s τ) I J =
      MvPolynomial.C (∏ z : Lt, c (tp z) ^ (nu z).card) * PIJ tp nu s I J := by
  unfold PIJ
  have hdet : ∀ z (cc : Fin ((nu z).rowLen 0)),
      Matrix.det (Matrix.of fun i k : Fin ((nu z).colLen cc) =>
        MvPolynomial.C (c (tp z) * s (tp z)) * MvPolynomial.X ((tp z, I z cc i, J z cc k) : Idx T N N')) =
      MvPolynomial.C (c (tp z)) ^ (nu z).colLen cc *
        Matrix.det (Matrix.of fun i k : Fin ((nu z).colLen cc) =>
          MvPolynomial.C (s (tp z)) * MvPolynomial.X ((tp z, I z cc i, J z cc k) : Idx T N N')) := by
    intro z cc
    have : (Matrix.of fun i k : Fin ((nu z).colLen cc) =>
        MvPolynomial.C (c (tp z) * s (tp z)) * MvPolynomial.X ((tp z, I z cc i, J z cc k) : Idx T N N')) =
        (MvPolynomial.C (c (tp z)) : MvPolynomial (Idx T N N') ℂ) • (Matrix.of fun i k : Fin ((nu z).colLen cc) =>
          MvPolynomial.C (s (tp z)) * MvPolynomial.X ((tp z, I z cc i, J z cc k) : Idx T N N')) := by
      ext i k
      simp [MvPolynomial.C_mul, mul_assoc]
    rw [this, Matrix.det_smul, Fintype.card_fin]
  simp_rw [hdet, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← card_eq_sum_colLen,
    map_prod, map_pow]
end PI.IsoScaleA.UnitaryGroupMassFormula
