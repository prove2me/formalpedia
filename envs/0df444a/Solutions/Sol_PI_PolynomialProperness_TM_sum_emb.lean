-- Prove2me | solution 1 for PI.PolynomialProperness.TM.sum_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:34:55.24287+00:00
-- url     : https://prove2.me/submissions/b2d262cd-3a40-4fe4-b9ff-426f62081b7f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.TM
namespace PI.PolynomialProperness.TM
theorem _root_.solution {N n : ℕ} (e : Fin n ↪ Fin N) (f : Fin N → ℂ) (hf : ∀ i, (∀ t, e t ≠ i) → f i = 0) :
    ∑ i, f i = ∑ t, f (e t) := by
  rw [← Finset.sum_map Finset.univ e f]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  apply hf
  intro t ht
  apply hi
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  exact ⟨t, ht⟩
end PI.PolynomialProperness.TM
