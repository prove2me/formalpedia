-- Prove2me | solution 1 for PI.ProdFormulaE.modF_iota
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:18:36.712677+00:00
-- url     : https://prove2.me/submissions/bd5a41c5-8e2c-46d0-a85f-ab4c2b872fa8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ModFIotaFinitePlace
import Theorems.Thm_PI_ProdFormulaE_modF_iota_int
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_ProdFormulaE_modF_div
import Theorems.Thm_PI_ProdFormulaE_modF_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel IsDedekindDomain NumberField
open PI PI.ProdFormulaE
variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (ι : F →+* K)
namespace PI.ProdFormulaE
theorem _root_.solution (hI : IndexFormula) (hC : CardStep) (hd : DenseRange ι)
    (hv : ∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) (z : F) :
    modF K (ι z) = HeightOneSpectrum.adicAbv F p z := by
  by_cases hz : z = 0
  · simp [hz, modF_zero]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hz
  rw [map_div₀, modF_div, map_div₀]
  have e1 := modF_iota_int p ι hI hC hd hv a ha0
  have e2 := modF_iota_int p ι hI hC hd hv b hb0
  simp only [RingOfIntegers.coe_eq_algebraMap] at e1 e2 ⊢
  rw [e1, e2]
end PI.ProdFormulaE
