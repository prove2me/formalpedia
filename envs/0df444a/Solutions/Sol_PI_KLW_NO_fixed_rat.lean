-- Prove2me | solution 1 for PI.KLW.NO.fixed_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:33.582412+00:00
-- url     : https://prove2.me/submissions/7cfca266-b0ca-4526-9014-d32292e46f65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] (c : K →+* K) (hK : Module.finrank ℚ K = 2)
    (hne : ∃ z, c z ≠ z) {x : K} (hx : c x = x) : ∃ q : ℚ, x = (q : K) := by
  by_contra hq
  push Not at hq
  have hli : LinearIndependent ℚ ![(1 : K), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hq (-s / t)
      rw [Rat.smul_def, Rat.smul_def] at hst
      have ht' : (t : K) ≠ 0 := by exact_mod_cast ht
      push_cast
      field_simp
      linear_combination hst
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK])
  obtain ⟨z, hz⟩ := hne
  apply hz
  rw [← b.sum_repr z]
  simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Rat.smul_def, map_add, map_mul, map_ratCast, map_one, hx]
end PI.KLW.NO
