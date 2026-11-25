-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.fac_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:12:41.549801+00:00
-- url     : https://prove2.me/submissions/a748b13f-1763-4040-9daa-9b62edf9702f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFacSlash
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_pt_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_AA_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_DD_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {t t' : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) (ht' : 0 < t'.1 ∧ 0 < t'.2.2)
    (γ γ' : SL(2, ℤ))
    (h : Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') (τ : ℍ) :
    fac t (γ • τ) = denom γ τ ^ 24 * ((t.2.2 : ℂ) / t'.2.2) ^ 12 * fac t' τ := by
  obtain ⟨h1, h2⟩ := pt_smul ht ht' γ γ' h τ
  have he' : ((t'.2.2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast ht'.2.ne'
  have hd : denom γ' (pt t'.1 t'.2.1 t'.2.2 τ) = (t.2.2 : ℂ) / t'.2.2 * denom γ τ := by
    rw [div_mul_eq_mul_div, eq_div_iff he']
    exact h2
  simp only [fac]
  rw [h1, AA_smul, DD_smul, AA_smul, DD_smul, hd]
  ring
end ReciprocityTheory.ChartRestriction.L1
