-- Prove2me | solution 1 for PI.RhsWLim.W.RI.rhsWInv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:36.400414+00:00
-- url     : https://prove2.me/submissions/f73fa5ab-1a60-4446-94fd-f8334fc15f66

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Theorems.Thm_PI_RhsWLim_W_RI_orbV_cont
import Theorems.Thm_PI_RhsWLim_W_RI_rmulM_cont
import Theorems.Thm_PI_RhsWLim_W_RI_nu_conc
import Theorems.Thm_PI_RhsWLim_W_HU_amb_closed
import Theorems.Thm_PI_RhsWLim_W_HU_lmulM_cont
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_nu_sigmaFinite
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_repr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace PI.RhsWLim.W.RI
theorem _root_.solution (hD : DescUniq) (hR : RInvNu) (hO : OrbInv) : RhsWInv := by
  intro k r z z' μW μW' a a' μsec hd s hs φ hφ
  have := hd.haarW.1
  have := hd.haarW'.1
  have hσ : SigmaFinite (nuR k r z z' μW μW' μsec) := nu_sigmaFinite hd
  have hl : Measurable (lmulM s : Mt k r → Mt k r) := (HU.lmulM_cont s).measurable
  have hσ1 : SigmaFinite ((nuR k r z z' μW μW' μsec).map (lmulM s)) :=
    (lmulE s (HU.uwb_unit hs)).sigmaFinite_map
  have hC1 : ((nuR k r z z' μW μW' μsec).map (lmulM s)) {x | Matrix.of x ∉ UWb k r} = 0 := by
    rw [Measure.map_apply hl (s := {x : Mt k r | Matrix.of x ∉ UWb k r})
      HU.amb_closed.isOpen_compl.measurableSet]
    refine measure_mono_null (fun x (hx : Matrix.of (lmulM s x) ∉ UWb k r) (hx' : Matrix.of x ∈ UWb k r) =>
      hx (HU.uwb_mul hs hx')) (nu_conc hd)
  have hR1 : ∀ b ∈ UWset k r z', ((nuR k r z z' μW μW' μsec).map (lmulM s)).map (rmulM b) =
      (nuR k r z z' μW μW' μsec).map (lmulM s) := by
    intro b hb
    have hr : Measurable (rmulM b : Mt k r → Mt k r) := (rmulM_cont b).measurable
    have e : rmulM b ∘ lmulM s = lmulM s ∘ rmulM b := by
      funext x
      show (s * Matrix.of x * b : Mat k r) = s * (Matrix.of x * b)
      exact Matrix.mul_assoc _ _ _
    rw [Measure.map_map hr hl, e, ← Measure.map_map hl hr, hR k r z z' μW μW' a a' μsec hd b hb]
  have hO1 : ((nuR k r z z' μW μW' μsec).map (lmulM s)).map (orbV k r z') =
      (nuR k r z z' μW μW' μsec).map (orbV k r z') := by
    have ho : Measurable (orbV k r z') := (orbV_cont z').measurable
    ext A hA
    rw [Measure.map_map ho hl, Measure.map_apply (ho.comp hl) hA, Measure.map_apply ho hA,
      ← lintegral_indicator_one ((ho.comp hl) hA), ← lintegral_indicator_one (ho hA)]
    have e1 : ((orbV k r z' ∘ lmulM s) ⁻¹' A).indicator (1 : Mt k r → ℝ≥0∞) =
        fun x => A.indicator 1 (s *ᵥ orbV k r z' x) := by
      funext x
      show ((orbV k r z' ∘ lmulM s) ⁻¹' A).indicator 1 x = A.indicator 1 (s *ᵥ (Matrix.of x *ᵥ z'))
      rw [Matrix.mulVec_mulVec]
      rfl
    have e2 : (orbV k r z' ⁻¹' A).indicator (1 : Mt k r → ℝ≥0∞) = fun x => A.indicator 1 (orbV k r z' x) := by
      funext x
      rfl
    have hF : Measurable (A.indicator (1 : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞)) := measurable_one.indicator hA
    rw [e1, e2, ← repr hd (fun x => A.indicator 1 (s *ᵥ orbV k r z' x))
        (hF.comp ((continuous_const.matrix_mulVec continuous_id).measurable.comp ho)),
      ← repr hd (fun x => A.indicator 1 (orbV k r z' x)) (hF.comp ho), hO k r z z' μW μW' a a' μsec hd s hs _ hF]
  have key := hD k r z' μW' hd.haarW' (by rw [hd.massW']; exact ENNReal.ofReal_ne_top) _ _ hσ1 hσ hC1
    (nu_conc hd) hR1 (hR k r z z' μW μW' a a' μsec hd) hO1
  rw [repr hd (fun x => φ (lmulM s x)) (hφ.comp hl), repr hd _ hφ, ← lintegral_map hφ hl, key]
end PI.RhsWLim.W.RI
