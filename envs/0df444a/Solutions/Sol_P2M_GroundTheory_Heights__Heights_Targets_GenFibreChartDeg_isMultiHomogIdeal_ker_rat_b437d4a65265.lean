-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_GenFibreChartDeg_isMultiHomogIdeal_ker_rat_b437d4a65265
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:21:25.097566+00:00
-- url     : https://prove2.me/submissions/2d57c4a7-f325-44b8-93d5-cf48bb21c4d4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GenFibreChartDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StAdjoinIndepRelfinrank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFinrankAdjoinRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGenFibreChartDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_int_mul_eq_qmap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Targets
namespace GenFibreChartDeg
theorem _root_.solution {K' : Type} {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {Ω : Type} [Field Ω] [CharZero Ω] (x' : (Σ k', ι' k') → Ω)
    (h : IsMultiHomogIdeal (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω))) :
    IsMultiHomogIdeal (RingHom.ker (aeval x' : MRingOver ℚ ι' →ₐ[ℚ] Ω)) := by
  have hmap : ∀ g : MRing ι', aeval x' (qmap g) = aeval x' g := fun g => by
    rw [qmap, ← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
  have hker : RingHom.ker (aeval x' : MRingOver ℚ ι' →ₐ[ℚ] Ω) =
      (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω)).map qmap := by
    apply le_antisymm
    · intro f hf
      obtain ⟨N, hN, g, hg⟩ := exists_int_mul_eq_qmap f
      have hg0 : g ∈ RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω) := by
        rw [RingHom.mem_ker, ← hmap, ← hg, map_mul, RingHom.mem_ker.mp hf, mul_zero]
      have hmem : (N : MRingOver ℚ ι') * f ∈ (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω)).map qmap := by
        rw [hg]
        exact Ideal.mem_map_of_mem _ hg0
      have hu : IsUnit (N : MRingOver ℚ ι') := by
        rw [show (N : MRingOver ℚ ι') = C (N : ℚ) by simp]
        exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast hN)).map C
      have h2 := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : MRingOver ℚ ι') hmem
      rwa [← mul_assoc, hu.val_inv_mul, one_mul] at h2
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, hmap]
      exact RingHom.mem_ker.mp hg
  rw [hker]
  obtain ⟨T, hT, hTe⟩ := h
  refine ⟨qmap '' T, ?_, by rw [hTe, Ideal.map_span]⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hT f hf
  exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ f hm) k⟩
end GenFibreChartDeg
end GroundTheory.Heights₂.Heights.Targets
