-- Prove2me | solution 1 for PI.AprimeInfA.lintegral_mul_right_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:10.235327+00:00
-- url     : https://prove2.me/submissions/5c843e87-4e57-4f1f-a5f3-f600c4ac82e2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Theorems.Thm_PI_AprimeInfA_map_mul_right_eq
import Theorems.Thm_PI_AprimeInfA_modChar_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfA
open MeasureTheory Topology TopologicalSpace Set
open scoped ENNReal NNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.AprimeInfA
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G)
    (ν : Measure H) [ν.IsMulLeftInvariant] (h0 : ν univ ≠ 0) (hfin : ν univ ≠ ∞) (k : H)
    {f : G → ℝ≥0∞} (hf : Measurable f) : ∫⁻ g, f (g * k) ∂μ = ∫⁻ g, f g ∂μ := by

  rw [show (∫⁻ g, f (g * k) ∂μ) = ∫⁻ g, f g ∂(μ.map (· * (k : G))) from
    (lintegral_map hf (measurable_mul_const _)).symm, map_mul_right_eq μ (k : G),
    modChar_eq_one H ν h0 hfin k, one_smul]
end PI.AprimeInfA
