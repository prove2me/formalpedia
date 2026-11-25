-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.psi_exp_isPositive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:21.923089+00:00
-- url     : https://prove2.me/submissions/d52258e8-f407-46d9-9219-7f919b8c8d14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_KinstSecondCountable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_PsiPos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_psiPos_integral_isPositive
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_psiPos_posDef_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_exp_noncompactPart_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_phiM_posDef


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (μ : Fin n → ℤ) (hμ : S7.IsMu lam μ)
    (hform : ∀ X, inP ε X → Ψ (NormedSpace.exp X) =
      ((Module.finrank ℂ T.V : ℂ) / ((S7.muK ε Set.univ).toReal : ℂ)) •
        ∫ k, S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k)⁻¹ • (T.op k * S7.projW T * T.op k⁻¹)
          ∂(S7.muK ε)) :
    ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive := by
  intro X hX
  have hpd : ∀ k : S7.KG ε, (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k)⁻¹.PosDef :=
    fun k => (psiPos_posDef_conj k (S7.exp_noncompactPart_posDef hX)).inv
  let g : S7.KG ε → ℝ := fun k => (S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k)⁻¹).re
  have hphi : ∀ k, S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k)⁻¹ = ((g k : ℝ) : ℂ) := by
    intro k
    apply Complex.ext
    · simp [g]
    · simp [g, (S7.phiM_posDef μ (hpd k)).2]
  have hc : (0 : ℝ) ≤ (Module.finrank ℂ T.V : ℝ) / (S7.muK ε Set.univ).toReal :=
    div_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
  have hcc : ((Module.finrank ℂ T.V : ℂ) / ((S7.muK ε Set.univ).toReal : ℂ)) =
      ((((Module.finrank ℂ T.V : ℝ) / (S7.muK ε Set.univ).toReal : ℝ)) : ℂ) := by
    push_cast
    rfl
  rw [hform X hX, hcc]
  simp_rw [hphi]
  exact psiPos_integral_isPositive T hc g (fun k => (S7.phiM_posDef μ (hpd k)).1.le)
end ReciprocityTheory.ChartRestriction.DS
