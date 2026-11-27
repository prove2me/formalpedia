-- Prove2me | solution 1 for PI.IwaMeasEx.MF.haar_map_eq_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:15:28.804863+00:00
-- url     : https://prove2.me/submissions/0b66fbf8-5ae0-4cce-b0da-d49e4f335947

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IwasawaMeasureExistence_MeasureEqRelIndexMul
import Theorems.Thm_PI_IwaMeasEx_MF_measure_eq_relIndex_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IwaMeasEx PI.IwaMeasEx.MF
open MeasureTheory Measure Set
open scoped ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
namespace PI.IwaMeasEx.MF
theorem _root_.solution (φ : G ≃ₜ* G) (U : Subgroup G) (hUo : IsOpen (U : Set G))
    (hUc : IsCompact (U : Set G))
    (h1 : (U ⊓ U.comap φ.toMulEquiv.toMonoidHom).relIndex U ≠ 0)
    (h2 : (U ⊓ U.comap φ.toMulEquiv.toMonoidHom).relIndex (U.comap φ.toMulEquiv.toMonoidHom) ≠ 0) :
    (haar : Measure G).map φ = ENNReal.ofReal
      (((U ⊓ U.comap φ.toMulEquiv.toMonoidHom).relIndex (U.comap φ.toMulEquiv.toMonoidHom) : ℝ) /
        ((U ⊓ U.comap φ.toMulEquiv.toMonoidHom).relIndex U : ℝ)) • (haar : Measure G) := by
  classical
  have hφm : Measurable φ := φ.continuous.measurable
  have hW'set : ((U.comap φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G) = φ ⁻¹' (U : Set G) := by
    first
      | rfl
      | (ext x; rfl)
      | (ext x; simp)
  have hUm : MeasurableSet (U : Set G) := hUo.measurableSet
  have hW'o : IsOpen ((U.comap φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G) := by
    rw [hW'set]; exact hUo.preimage φ.continuous
  have hVo : IsOpen ((U ⊓ U.comap φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hUo.inter hW'o
  have eU := measure_eq_relIndex_mul (haar : Measure G) (U := U)
    (W := U ⊓ U.comap φ.toMulEquiv.toMonoidHom) inf_le_left hUm hVo.measurableSet h1
  have eW := measure_eq_relIndex_mul (haar : Measure G)
    (U := U.comap φ.toMulEquiv.toMonoidHom) (W := U ⊓ U.comap φ.toMulEquiv.toMonoidHom)
    inf_le_right hW'o.measurableSet hVo.measurableSet h2
  have hV0 : (haar : Measure G) ((U ⊓ U.comap φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G) ≠ 0 :=
    hVo.measure_ne_zero _ ⟨1, Subgroup.one_mem _⟩
  have hVtop : (haar : Measure G) ((U ⊓ U.comap φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G) ≠ ∞ :=
    ((measure_mono (SetLike.coe_subset_coe.mpr
      (inf_le_left : U ⊓ U.comap φ.toMulEquiv.toMonoidHom ≤ U))).trans_lt hUc.measure_lt_top).ne
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, (haar : Measure G).map φ = c • (haar : Measure G) := by
    haveI hreg : Regular (haar : Measure G) := by
      first
        | infer_instance
        | exact regular_haarMeasure
    haveI : IsHaarMeasure ((haar : Measure G).map φ) := by
      first
        | infer_instance
        | exact ContinuousMulEquiv.isHaarMeasure_map (haar : Measure G) φ
        | exact φ.isHaarMeasure_map (haar : Measure G)
        | exact isHaarMeasure_map (haar : Measure G) φ.toMulEquiv.toMonoidHom φ.continuous
            φ.surjective φ.toHomeomorph.isClosedEmbedding.tendsto_cocompact
    haveI : Regular ((haar : Measure G).map φ) := by
      first
        | infer_instance
        | exact Regular.map (μ := (haar : Measure G)) φ.toHomeomorph
        | exact hreg.map φ.toHomeomorph
    first
      | exact ⟨_, (isMulLeftInvariant_eq_smul_of_regular ((haar : Measure G).map φ)
          (haar : Measure G)).trans (ENNReal.smul_def _ _)⟩
      | exact ⟨_, (isMulLeftInvariant_eq_smul_of_regular ((haar : Measure G).map φ)
          (haar : Measure G)).trans rfl⟩
      | exact ⟨_, haarMeasure_unique ((haar : Measure G).map φ) _⟩
      | exact ⟨_, (isMulLeftInvariant_eq_smul_of_regular ((haar : Measure G).map φ)
          (haar : Measure G)).trans (by ext s _; simp)⟩
  have hνU : (haar : Measure G).map φ (U : Set G) = (c • (haar : Measure G)) (U : Set G) := by
    rw [hc]
  rw [Measure.map_apply hφm hUm, ← hW'set, Measure.smul_apply, smul_eq_mul, eU, eW,
    ← mul_assoc] at hνU
  have hca : c * ((U ⊓ U.comap φ.toMulEquiv.toMonoidHom).relIndex U : ℝ≥0∞) =
      ((U ⊓ U.comap φ.toMulEquiv.toMonoidHom).relIndex (U.comap φ.toMulEquiv.toMonoidHom) : ℝ≥0∞) := by
    first
      | exact ((ENNReal.mul_eq_mul_right hV0 hVtop).mp hνU).symm
      | exact ((ENNReal.mul_left_inj hV0 hVtop).mp hνU).symm
      | (have h' := congrArg (· / (haar : Measure G)
            ((U ⊓ U.comap φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G)) hνU
         simp only [ENNReal.mul_div_cancel_right hV0 hVtop] at h'
         exact h'.symm)
  rw [hc]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h1)), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, ENNReal.eq_div_iff (by exact_mod_cast h1) (by simp), mul_comm]
  exact hca
end PI.IwaMeasEx.MF
