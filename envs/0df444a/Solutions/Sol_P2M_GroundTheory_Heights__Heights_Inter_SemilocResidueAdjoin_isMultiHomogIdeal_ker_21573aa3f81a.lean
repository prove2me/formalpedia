-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueAdjoin_isMultiHomogIdeal_ker_21573aa3f81a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:16:24.197911+00:00
-- url     : https://prove2.me/submissions/62b65cd2-8966-4f04-b67e-2108dd7c5672

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocResidueAdjoin
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueAdjoin_isMultiHomogIdeal_map_ef06bc88f37f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueAdjoin_exists_int_mul_6d11b6fac758
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_isMultiHomogIdeal_map_81a0ea2d0932


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Inter
namespace SemilocResidueAdjoin
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (hF : ∀ c : F, ∃ a b : ℤ, (b : F) ≠ 0 ∧ c = a / b)
    (x : (Σ k, ι k) → Ω) (hmh : IsMultiHomogIdeal (RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω))) :
    IsMultiHomogIdeal (RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω)) := by
  have e : ∀ g : MRing ι, aeval x (MvPolynomial.map (Int.castRingHom F) g) = aeval x g := fun g => by
    rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
  suffices h : RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω) =
      (RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω)).map (MvPolynomial.map (Int.castRingHom F)) by
    rw [h]
    exact SemilocResidueAdjoin.isMultiHomogIdeal_map _ hmh
  refine le_antisymm (fun f hf => ?_) (Ideal.map_le_iff_le_comap.2 fun g hg => ?_)
  · obtain ⟨g, d, hd, hg⟩ := SemilocResidueAdjoin.exists_int_mul hF f
    have hg0 : g ∈ RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) := by
      rw [RingHom.mem_ker, ← e, ← hg, map_mul, (RingHom.mem_ker).1 hf, mul_zero]
    have hf' : f = C (d : F)⁻¹ * MvPolynomial.map (Int.castRingHom F) g := by
      rw [← hg, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hd, C_1, one_mul]
    rw [hf']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hg0)
  · rw [Ideal.mem_comap, RingHom.mem_ker, e]
    exact hg
end SemilocResidueAdjoin
end GroundTheory.Heights₂.Heights.Inter
