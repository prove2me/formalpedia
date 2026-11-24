-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_KrullAkizukiQuotientLength_proof_f94e993eb61d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:57.842812+00:00
-- url     : https://prove2.me/submissions/4dde1a75-ba4f-46ca-9044-b1930539ff58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsKrullAkizuki
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PKrullAkizukiQuotientLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
namespace GroundTheory.Heights₂.Heights.Model
namespace KrullAkizukiQuotientLength
theorem _root_.solution (h : TorsionFreeQuotientLength.Statement) :
    KrullAkizukiQuotientLength.Statement := by
  intro R _ _ _ hdim K _ _ _ L _ _ _ _ _ S b hb

  have hinj : Function.Injective (algebraMap R S) := by
    intro x y hxy
    have h1 : algebraMap R L x = algebraMap R L y := by
      simpa using congrArg (fun s : S => (s : L)) hxy
    rw [IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R K L] at h1
    exact IsFractionRing.injective R K ((algebraMap K L).injective h1)
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have : Module.IsTorsionFree R S := inferInstance

  have hrankL : Module.rank R L = Module.rank K L :=
    (IsLocalization.rank_eq K (nonZeroDivisors R) le_rfl).symm
  have hlt : Module.rank R S < Cardinal.aleph0 :=
    lt_of_le_of_lt (by rw [← hrankL]; exact Submodule.rank_le (Subalgebra.toSubmodule S))
      (Module.rank_lt_aleph0 K L)
  obtain ⟨r, hr⟩ := Cardinal.lt_aleph0.mp hlt

  have hdim0 : Ring.KrullDimLE 0 (R ⧸ Ideal.span {b}) := by
    rw [Ring.krullDimLE_iff]
    have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hb)
    rw [hdim] at h2
    generalize ringKrullDim (R ⧸ Ideal.span {b}) = d at h2 ⊢
    cases d with
    | bot => exact bot_le
    | coe n =>
      have h3 : n + 1 ≤ 1 := by exact_mod_cast h2
      induction n using ENat.recTopCoe with
      | top => simp at h3
      | coe k =>
        have hk : k + 1 ≤ 1 := by exact_mod_cast h3
        obtain rfl : k = 0 := by omega
        simp
  have : IsArtinianRing (R ⧸ Ideal.span {b}) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  have hRlen : Module.length R (R ⧸ Ideal.span {b}) ≠ ⊤ := by
    rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
    exact ⟨inferInstance, isArtinian_of_surjective_algebraMap
      (Ideal.Quotient.mk_surjective (I := Ideal.span {b}))⟩

  have hle := h R hdim S r hr b hb
  have hfin : IsFiniteLength R (S ⧸ (Ideal.span {b} • ⊤ : Submodule R S)) :=
    Module.length_ne_top_iff.mp
      (ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.natCast_ne_top r) hRlen) hle)

  have heq : (Ideal.span {b} • ⊤ : Submodule R S) =
      (Ideal.span {algebraMap R S b}).restrictScalars R := by
    ext x
    simp only [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_top, true_and, Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
      Algebra.smul_def, mul_comm]
  rw [heq] at hfin
  exact hfin.of_surjective (f := (Submodule.Quotient.restrictScalarsEquiv R _).toLinearMap)
    (Submodule.Quotient.restrictScalarsEquiv R _).surjective
end KrullAkizukiQuotientLength
end GroundTheory.Heights₂.Heights.Model
