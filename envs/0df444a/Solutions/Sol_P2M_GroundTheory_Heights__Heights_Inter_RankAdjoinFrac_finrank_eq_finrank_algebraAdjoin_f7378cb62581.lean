-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_finrank_eq_finrank_algebraAdjoin_f7378cb62581
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:52:51.934961+00:00
-- url     : https://prove2.me/submissions/372c5ad4-1c71-4826-bc14-a0bc8069c56a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankAdjoinFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRankAdjoinFrac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_exists_mul_mem_of_mem_123d02d0699d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Module IntermediateField IntermediateField.algebraAdjoinAdjoin
open GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac
namespace GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac
theorem _root_.solution {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S T : Set Ω}
    (h : S ⊆ T) :
    letI := adjoinInclAlgebra F h
    finrank (Algebra.adjoin F S) (Algebra.adjoin F T) =
      finrank (IntermediateField.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T) := by
  let _ := adjoinInclAlgebra F h
  let _ : Algebra (Algebra.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T) :=
    ((algebraMap (IntermediateField.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T)).comp
      (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S))).toAlgebra
  have : IsScalarTower (Algebra.adjoin F S) (IntermediateField.adjoin F S)
      (Algebra.adjoin (IntermediateField.adjoin F S) T) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hle : Algebra.adjoin F T ≤ (Algebra.adjoin (IntermediateField.adjoin F S) T).restrictScalars F :=
    Algebra.adjoin_le (Algebra.subset_adjoin (R := IntermediateField.adjoin F S))
  let f : Algebra.adjoin F T →ₗ[Algebra.adjoin F S] Algebra.adjoin (IntermediateField.adjoin F S) T :=
    { toFun := fun m => ⟨m.1, hle m.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        apply Subtype.ext
        simp only [Algebra.smul_def, RingHom.id_apply, Subalgebra.coe_mul, RingHom.algebraMap_toAlgebra,
          RingHom.comp_apply, Subalgebra.coe_algebraMap, IntermediateField.algebraMap_apply,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_inclusion] }
  have : IsLocalizedModule (nonZeroDivisors (Algebra.adjoin F S)) f := by
    refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} hx => ?_⟩
    · rw [Module.End.isUnit_iff]
      have hx0 : algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (Algebra.adjoin F S) (IntermediateField.adjoin F S))).mpr
          (nonZeroDivisors.coe_ne_zero x)
      refine ⟨fun u v huv => ?_, fun v => ?_⟩
      · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
          ← algebraMap_smul (IntermediateField.adjoin F S) (x : Algebra.adjoin F S) u,
          ← algebraMap_smul (IntermediateField.adjoin F S) (x : Algebra.adjoin F S) v] at huv
        calc u = (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x)⁻¹ •
              (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x • u) := by
                rw [smul_smul, inv_mul_cancel₀ hx0, one_smul]
          _ = v := by rw [huv, smul_smul, inv_mul_cancel₀ hx0, one_smul]
      · refine ⟨(algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x)⁻¹ • v, ?_⟩
        rw [Module.algebraMap_end_apply, ← algebraMap_smul (IntermediateField.adjoin F S), smul_smul,
          mul_inv_cancel₀ hx0, one_smul]
    · obtain ⟨a, ha, ha0, hay⟩ := exists_mul_mem_of_mem h y.2
      refine ⟨(⟨a * y, hay⟩, ⟨⟨a, ha⟩, mem_nonZeroDivisors_of_ne_zero ?_⟩), ?_⟩
      · exact fun h0 => ha0 (congrArg Subtype.val h0)
      · apply Subtype.ext
        simp only [Submonoid.smul_def, Algebra.smul_def, Subalgebra.coe_mul, RingHom.algebraMap_toAlgebra,
          RingHom.comp_apply, Subalgebra.coe_algebraMap, IntermediateField.algebraMap_apply]
        rfl
    · refine ⟨1, ?_⟩
      rw [one_smul, one_smul]
      exact Subtype.ext (congrArg (fun z : Algebra.adjoin (IntermediateField.adjoin F S) T => (z : Ω)) hx)
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (Algebra.adjoin F S)) f le_rfl,
    IsLocalization.finrank_eq (IntermediateField.adjoin F S) (nonZeroDivisors (Algebra.adjoin F S)) le_rfl]
end GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac
