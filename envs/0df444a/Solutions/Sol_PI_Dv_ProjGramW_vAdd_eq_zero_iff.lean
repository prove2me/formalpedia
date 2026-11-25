-- Prove2me | solution 1 for PI.Dv.ProjGramW.vAdd_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:35:31.246496+00:00
-- url     : https://prove2.me/submissions/ce750a49-afd3-4f7c-abb9-03d52e548a06

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs0 : s ≠ 0) :
    vAdd w (algebraMap (𝓞 K) K s) = 0 ↔ s ∉ w.asIdeal := by
  unfold Formalism.BasicNotions.vAdd
  have hne : w.valuation K (algebraMap (𝓞 K) K s) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hs0
  have hle : w.valuation K (algebraMap (𝓞 K) K s) ≤ 1 := w.valuation_le_one s
  rw [neg_eq_zero, ← (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) w s).not, not_lt]
  constructor
  · intro h
    rw [← WithZero.exp_log hne, h, WithZero.exp_zero]
  · intro h
    rw [le_antisymm hle h, WithZero.log_one]
end PI.Dv.ProjGramW
