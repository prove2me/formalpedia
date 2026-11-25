-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CapPs.Fint_opH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:38:34.105863+00:00
-- url     : https://prove2.me/submissions/48d22f01-eec9-406f-ae60-70d907eee9fc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ProdOfFnSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ChainHSlice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_int_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CapPs
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
local notation "𝕄" => Matrix (Fin n) (Fin n) ℂ
local notation "𝕋" => Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ} [CompactSpace (KG ε)]
namespace ReciprocityTheory.ChartRestriction.DS.S7.CapPs
theorem _root_.solution (T : KType ε Λ) {g₁ g₂ : 𝕋 → ℂ} (h₁ : ContDiffOn ℂ ∞ g₁ (GPs.Wset n))
    (h₂ : ContDiffOn ℂ ∞ g₂ (GPs.Wset n)) (c : ℂ) {x : 𝕄} (hx : x ∈ Ps1.Uset ε) :
    GPs.Fint T (fun p => c • g₁ p + g₂ p) x = c • GPs.Fint T g₁ x + GPs.Fint T g₂ x := by
  unfold GPs.Fint
  have : ∫ k, (c • g₁ (GPs.emb x k) + g₂ (GPs.emb x k)) • GPs.Pk T k ∂(muK ε) =
      c • ∫ k, g₁ (GPs.emb x k) • GPs.Pk T k ∂(muK ε) + ∫ k, g₂ (GPs.emb x k) • GPs.Pk T k ∂(muK ε) := by
    simp only [add_smul, smul_eq_mul, mul_smul]
    have e := integral_add ((GPs.int_int T h₁ hx).smul c) (GPs.int_int T h₂ hx)
    simp only [Pi.smul_apply] at e
    rw [e, integral_smul]
  rw [this, smul_add, smul_comm (GPs.cK T) c]
end ReciprocityTheory.ChartRestriction.DS.S7.CapPs
