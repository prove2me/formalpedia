-- Prove2me | solution 1 for PI.KLW.NO.hf_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:55:47.983112+00:00
-- url     : https://prove2.me/submissions/c4e3e755-6ef7-4144-a0cf-458aeaac0671

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.NO
namespace PI.KLW.NO
theorem _root_.solution {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (a b : K) (e v : ι → K) :
    hf c (a • e - b • v) (a • e - b • v) = a * c a * hf c e e - a * c b * hf c e v
      - b * c a * hf c v e + b * c b * hf c v v := by
  have h : ∀ i, (a * e i - b * v i) * c (a * e i - b * v i) = a * c a * (e i * c (e i))
      - a * c b * (e i * c (v i)) - b * c a * (v i * c (e i)) + b * c b * (v i * c (v i)) := by
    intro i; simp only [map_sub, map_mul]; ring
  simp only [hf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
end PI.KLW.NO
