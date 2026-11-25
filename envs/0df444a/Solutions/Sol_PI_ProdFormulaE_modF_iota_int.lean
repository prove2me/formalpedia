-- Prove2me | solution 1 for PI.ProdFormulaE.modF_iota_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:12:03.856981+00:00
-- url     : https://prove2.me/submissions/6ebacd7f-3d4a-4923-9304-dc76f1a70ac4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ModFIotaFinitePlace
import Theorems.Thm_PI_ProdFormulaE_iota_mem_integer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel IsDedekindDomain NumberField
open PI PI.ProdFormulaE
variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (ι : F →+* K)
namespace PI.ProdFormulaE
theorem _root_.solution (hI : IndexFormula) (hC : CardStep) (hd : DenseRange ι)
    (hv : ∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) (a : 𝓞 F) (ha : a ≠ 0) :
    modF K (ι (a : F)) = HeightOneSpectrum.adicAbv F p (a : F) := by
  set t : 𝒪[K] := ⟨ι (a : F), iota_mem_integer p ι hv a⟩ with ht
  have ht0 : t ≠ 0 := by
    intro h
    have : ι (a : F) = 0 := congrArg Subtype.val h
    rw [map_eq_zero_iff ι ι.injective] at this
    exact ha (by exact_mod_cast this)
  have h1 := hI K t ht0
  rw [hC F p K ι hd hv a ha t rfl] at h1
  have h3 := HeightOneSpectrum.embedding_mul_absNorm (K := F) p ha
  rw [FinitePlace.norm_embedding] at h3
  have hN : ((Ideal.absNorm (p.maxPowDividing (Ideal.span {a})) : ℕ) : ℝ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
  exact mul_right_cancel₀ hN (h1.trans h3.symm)
end PI.ProdFormulaE
