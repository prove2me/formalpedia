-- Prove2me | solution 1 for PI.LocalEndW.henselRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:05.477193+00:00
-- url     : https://prove2.me/submissions/896da418-6447-4c7e-b868-d70599edabb7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_HenselRoot
import Theorems.Thm_PI_LocalEndW_isAdicComplete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Filter Topology
open PI PI.LocalEndW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocalEndW
theorem _root_.solution : HenselRoot := by
  intro F _ _ v ℓ u hℓ hu
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  have hϖ1 : ‖(ϖ : v.adicCompletion F)‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff]
    have hnu : ¬ IsUnit ϖ := hϖ.not_isUnit
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hnu
    exact lt_of_le_of_ne ϖ.2 hnu
  have := isAdicComplete v ϖ hϖ.ne_zero hϖ1
  have hu1 : Valued.v u ≤ 1 := by
    have hsplit : u = (u - 1) + 1 := by ring
    rw [hsplit]
    exact (Valuation.map_add _ _ _).trans (max_le hu.le (by simp))
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    simp at hℓ
  have hev : ((X ^ ℓ - C (⟨u, hu1⟩ : v.adicCompletionIntegers F))).eval 1 ∈ Ideal.span {ϖ} := by
    simp only [eval_sub, eval_pow, eval_X, one_pow, eval_C]
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    intro h
    have h' : Valued.v (u - 1) = 1 := by
      rw [← Valuation.map_neg]
      simpa using h
    exact hu.ne h'
  have hdu : IsUnit (Ideal.Quotient.mk (Ideal.span {ϖ}) ((derivative (X ^ ℓ - C (⟨u, hu1⟩ : v.adicCompletionIntegers F))).eval 1)) := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C,
      eval_pow, eval_X, one_pow, mul_one]
    apply IsUnit.map
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    simpa using hℓ
  obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian (I := Ideal.span {ϖ})
    (X ^ ℓ - C (⟨u, hu1⟩ : v.adicCompletionIntegers F)) (monic_X_pow_sub_C _ hℓ0) 1 hev hdu
  refine ⟨a, ?_⟩
  have ha' : a ^ ℓ = (⟨u, hu1⟩ : v.adicCompletionIntegers F) := by
    simpa [Polynomial.IsRoot, sub_eq_zero] using ha
  simpa using congrArg Subtype.val ha'
end PI.LocalEndW
