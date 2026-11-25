-- Prove2me | solution 1 for PI.DvRows.val_det_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:36:44.758996+00:00
-- url     : https://prove2.me/submissions/1bcb8051-1796-4b49-bc46-969b236131ac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_ValLeOneOfMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows
theorem _root_.solution {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin d) (Fin d) K) (c : K)
    (hM : ∀ i j, w.valuation K (M i j) * w.valuation K c ≤ 1) :
    w.valuation K M.det * (w.valuation K c) ^ d ≤ 1 := by
  have key : w.valuation K (c • M).det ≤ 1 := by
    rw [Matrix.det_apply]
    refine Valuation.map_sum_le _ (fun σ _ => ?_)
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul, map_prod]
      refine Finset.prod_le_one' (fun i _ => ?_)
      rw [Matrix.smul_apply, smul_eq_mul, map_mul, mul_comm]
      exact hM _ _
    · rw [hs, Units.neg_smul, one_smul, Valuation.map_neg, map_prod]
      refine Finset.prod_le_one' (fun i _ => ?_)
      rw [Matrix.smul_apply, smul_eq_mul, map_mul, mul_comm]
      exact hM _ _
  rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow] at key
  rwa [mul_comm]
end PI.DvRows
