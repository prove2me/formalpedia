-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.v_densHypAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:41.314801+00:00
-- url     : https://prove2.me/submissions/72c723b4-0980-45c8-8df4-49e79cf877e5

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HasCompactSupportCompHypInclAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessCRestrict_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (i : Fin (n + 1)) {U : Set (Fin (n + 1) → ℂ)}
    {v : (Fin (n + 1) → ℂ) → ℝ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hp : PoincareLelongData U v φ)
    (w : Fin n → ℂ) :
    v (hypInclAt i w) * densHypAt i φ w =
      ((n.factorial : ℝ) * (2 / Real.pi) ^ n) * hDens i v φ (hypInclAt i w) := by
  obtain ⟨hU, hv, hvc, hvU, hφ⟩ := hp
  by_cases hw : hypInclAt i w ∈ U
  · have hr : ∀ k, hessC (φ k ∘ hypInclAt i) w =
        (hessC (φ k) (hypInclAt i w)).submatrix i.succAbove i.succAbove := fun k =>
      hessCRestrict_thm n (φ k) U i hU (by exact_mod_cast contDiffOn_infty.1 (hφ k) 2) w hw
    simp only [densHypAt, maDens, hr]
    simp only [hDens, minorDens]
    ring
  · have h0 : v (hypInclAt i w) = 0 := image_eq_zero_of_notMem_tsupport fun h => hw (hvU h)
    simp [hDens, h0]
end ReciprocityTheory.AnForm.A
