-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.lint_Bset_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:06.181861+00:00
-- url     : https://prove2.me/submissions/734c0967-fd83-45c3-9deb-93e0a71ecb32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_psi_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_measurableSet_Bset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_integrable_gprod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_ae_good

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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution {p q : ι} (hpq : p ≠ q) {k : ℕ} (hk : Fintype.card ι = k + 1) (hk1 : 1 ≤ k)
    {s : ℝ} (hs : 0 ≤ s) (hsk : s < k) : ∫⁻ x in Bset q, PsiF p q s x < ∞ := by
  have hk0 : (0 : ℝ) < k := by
    have hk0' : 0 < k := by omega
    exact_mod_cast hk0'
  have hβ : s / k < 1 := by
    rw [div_lt_one hk0]
    exact hsk
  have hG := integrable_gprod p q hβ
  have hae : ∀ᵐ x : ι → ℂ, x ∈ Bset q →
      PsiF p q s x ≤ ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) := by
    filter_upwards [ae_good] with x hg hx
    exact psi_le hpq hk hk1 hs hx hg
  have h1 : ∫⁻ x in Bset q, PsiF p q s x ≤
      ∫⁻ x in Bset q, ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) :=
    lintegral_mono_ae ((ae_restrict_iff' (measurableSet_Bset q)).2 hae)
  have h2 : ∫⁻ x in Bset q, ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) ≤
      ∫⁻ x : ι → ℂ, ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) :=
    setLIntegral_le_lintegral _ _
  have h3 : ∫⁻ x : ι → ℂ, ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) < ∞ := by
    first
    | exact Integrable.lintegral_lt_top hG
    | exact HasFiniteIntegral.lintegral_lt_top hG.2
  exact lt_of_le_of_lt (h1.trans h2) h3
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
