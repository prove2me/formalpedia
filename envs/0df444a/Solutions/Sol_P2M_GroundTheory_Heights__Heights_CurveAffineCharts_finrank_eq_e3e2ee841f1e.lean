-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveAffineCharts_finrank_eq_e3e2ee841f1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:13.351791+00:00
-- url     : https://prove2.me/submissions/85673545-3be6-43ba-8101-60df1128bec7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_finite_1e9464aa5696
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_blockFnField_of_mem_curveRing_a2838448c32a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_nat_mul_mem_curveRing_f13620c227e3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.CurveAffineCharts
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
namespace GroundTheory.Heights₂.Heights.CurveAffineCharts
theorem _root_.solution [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1) :
    Module.finrank ℤ (curveRing y) = Module.finrank ℚ (blockFnField y) := by
  have := finite y hy
  let b := Module.finBasis ℤ (curveRing y)
  let ι : curveRing y →ₗ[ℤ] K' := (curveRing y).subtype.toAddMonoidHom.toIntLinearMap
  have hliZ : LinearIndependent ℤ (ι ∘ b) :=
    b.linearIndependent.map' ι (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliQ : LinearIndependent ℚ (ι ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  have hspan : Submodule.span ℚ (Set.range (ι ∘ b)) =
      Subalgebra.toSubmodule (blockFnField y).toSubalgebra := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact mem_blockFnField_of_mem_curveRing y hy (b i).2
    · intro x hx
      obtain ⟨n, hn, hnx⟩ := exists_nat_mul_mem_curveRing y hx
      have h1 : (⟨_, hnx⟩ : curveRing y) ∈ Submodule.span ℤ (Set.range b) := by
        rw [b.span_eq]; trivial
      have h2 : (n : K') * x ∈ Submodule.span ℤ (Set.range (ι ∘ b)) := by
        rw [Set.range_comp, ← Submodule.map_span]
        exact Submodule.mem_map_of_mem h1
      have h3 : (n : K') * x ∈ Submodule.span ℚ (Set.range (ι ∘ b)) :=
        Submodule.span_le_restrictScalars ℤ ℚ _ h2
      have h4 : x = (n : ℚ)⁻¹ • ((n : K') * x) := by
        rw [Algebra.smul_def, ← mul_assoc, map_inv₀, map_natCast,
          inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]
      rw [h4]
      exact Submodule.smul_mem _ _ h3
  rw [← IntermediateField.finrank_eq_finrank_subalgebra, ← Subalgebra.finrank_toSubmodule, ← hspan,
    finrank_span_eq_card hliQ, Fintype.card_fin]
end GroundTheory.Heights₂.Heights.CurveAffineCharts
