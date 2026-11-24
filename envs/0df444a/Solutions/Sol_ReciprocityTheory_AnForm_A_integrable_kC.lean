-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.integrable_kC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:33.099157+00:00
-- url     : https://prove2.me/submissions/ef90de14-8701-445e-8416-2ba83f609cda

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_hasCompactSupport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set Real
open scoped ContDiff
noncomputable section
variable {D : ℕ}
variable (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) {Φ : (Fin D → ℂ) → ℝ} (hΦ : Integrable Φ)
    (z : Fin D → ℂ) : Integrable fun y => ρ.scaled ε y * Φ (z - y) := by
  obtain ⟨M, hM⟩ := (scaled_contDiff ρ ε).continuous.bounded_above_of_compact_support
    (scaled_hasCompactSupport ρ hε)
  exact (hΦ.comp_sub_left z).bdd_mul (scaled_contDiff ρ ε).continuous.aestronglyMeasurable
    (Eventually.of_forall hM)
end ReciprocityTheory.AnForm.A
