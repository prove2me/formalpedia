-- Prove2me | solution 1 for PI.AlgValsFin.W.finprod_norm_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:14.593773+00:00
-- url     : https://prove2.me/submissions/9cc42a34-83af-46f9-91ca-58ef68402635

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_FinprodNormEmbedding
import Theorems.Thm_PI_AlgValsFin_W_valuation_eq_exp
import Theorems.Thm_PI_AlgValsFin_W_toNNReal_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution (k : Lˣ) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (hT : ∀ v, v ∉ T → ordF v k = 0) :
    ∏ᶠ w : FinitePlace L, w (k : L) =
      ∏ v ∈ T, (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ordF v k)⁻¹ := by
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  have hval : ∀ v : HeightOneSpectrum (𝓞 L),
      (FinitePlace.equivHeightOneSpectrum.symm v) (k : L) = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ordF v k)⁻¹ := by
    intro v
    have e1 : (FinitePlace.equivHeightOneSpectrum.symm v) (k : L) =
        NumberField.HeightOneSpectrum.adicAbv L v (k : L) := by
      first
        | (show (FinitePlace.mk v) (k : L) = _
           rw [FinitePlace.mk_apply, FinitePlace.norm_embedding])
        | (rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.mk_apply, FinitePlace.norm_embedding])
        | (simp only [FinitePlace.equivHeightOneSpectrum, Equiv.coe_fn_symm_mk]
           rw [← FinitePlace.mk_apply, FinitePlace.norm_embedding])
    rw [e1, NumberField.HeightOneSpectrum.adicAbv_def, valuation_eq_exp, toNNReal_exp]
    push_cast
    rw [zpow_neg]
  rw [finprod_congr hval]
  apply finprod_eq_prod_of_mulSupport_subset
  intro v hv
  by_contra hT'
  exact hv (by simp [hT v hT'])
end PI.AlgValsFin.W
