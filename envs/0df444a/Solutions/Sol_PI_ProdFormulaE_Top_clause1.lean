-- Prove2me | solution 1 for PI.ProdFormulaE.Top.clause1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:11.142649+00:00
-- url     : https://prove2.me/submissions/83b4bc65-94b8-40b6-8d88-631572a74ff5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_BasisEApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_DenEqOneOfForallPadicNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ProdFormulaEOf
import Theorems.Thm_PI_ProdFormulaE_Top_modK_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField MeasureTheory ValuativeRel Formalism.MainNotions.S.Loc
open PI PI.ProdFormulaE PI.ProdFormulaE.Top
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}
namespace PI.ProdFormulaE.Top
theorem _root_.solution (hH : St.HaarAlg) (hN : St.NormLoc) (h2 : Module.finrank F E = 2)
    (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p)
    (M : ∀ p, Model (L p).Fp (L p).Ep) (hM : ∀ p, (M p).OK) (x : E) (hx : x ≠ 0) :
    (Function.mulSupport fun p => (M p).modK ((L p).ιE x)).Finite ∧
      ∏ᶠ p, (M p).modK ((L p).ιE x) = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹ := by
  have hz : Algebra.norm F x ≠ 0 := Algebra.norm_ne_zero_iff.2 hx
  have he : (fun p => (M p).modK ((L p).ιE x)) =
      (fun w : FinitePlace F => w (Algebra.norm F x)) ∘ FinitePlace.equivHeightOneSpectrum.symm := by
    funext p
    rw [modK_eq hH hN h2 (L p) (M p) (hM p) hx]
    rfl
  rw [he]
  refine ⟨?_, ?_⟩
  · rw [Function.mulSupport_comp_eq_preimage]
    exact (FinitePlace.hasFiniteMulSupport hz).preimage
      (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn)
  · rw [Function.comp_def, finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
      (f := fun w : FinitePlace F => w (Algebra.norm F x)),
      FinitePlace.prod_eq_inv_abs_norm hz, Algebra.norm_norm, Rat.cast_inv, Rat.cast_abs]
end PI.ProdFormulaE.Top
