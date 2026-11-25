-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_exists_omegaLeb_bcdf9b3adbe0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:41:55.881049+00:00
-- url     : https://prove2.me/submissions/db15325a-0491-4f3d-8fc4-bd748378e9d0

import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsOmegaLeb
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_psiE_coe_5c9cc3374899

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Filter Topology Set Matrix Formalism.UG.P
open scoped ENNReal NNReal
variable (P Q : ℕ)
local notation "J" => Formalism.UG.Jpq P Q
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution : ∃ lam : Measure (lieU P Q), IsOmegaLeb lam := by
  let lam0 : Measure (lieU P Q) := Measure.addHaar
  let m := (lam0.prod lam0).map (psiE P Q)
  have hm : m.IsAddHaarMeasure := inferInstance
  have hs := Measure.isAddLeftInvariant_eq_smul m volume
  set s := Measure.addHaarScalarFactor m volume with hsdef
  have hs0 : 0 < s := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure m volume
  let t : ℝ≥0 := (NNReal.sqrt s)⁻¹
  have ht0 : t ≠ 0 := inv_ne_zero (NNReal.sqrt_pos.mpr hs0).ne'
  have hts : t * t * s = 1 := by
    have h1 : NNReal.sqrt s * NNReal.sqrt s = s := NNReal.mul_self_sqrt s
    have h2 : NNReal.sqrt s ≠ 0 := (NNReal.sqrt_pos.mpr hs0).ne'
    calc (NNReal.sqrt s)⁻¹ * (NNReal.sqrt s)⁻¹ * s
        = (NNReal.sqrt s)⁻¹ * (NNReal.sqrt s)⁻¹ * (NNReal.sqrt s * NNReal.sqrt s) := by rw [h1]
      _ = 1 := by field_simp
  have hl : (t • lam0).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul lam0 ht0
  refine ⟨t • lam0, hl, ?_⟩
  rw [← psiE_coe]
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.map_smul, Measure.map_smul]
  show t • t • m = volume
  rw [hs, smul_smul, smul_smul, hts, one_smul]
end Formalism.BasicNotions.Examples₂.CD
