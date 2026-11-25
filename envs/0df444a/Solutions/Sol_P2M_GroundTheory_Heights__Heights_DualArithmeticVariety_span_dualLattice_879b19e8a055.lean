-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_span_dualLattice_879b19e8a055
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:01:05.016319+00:00
-- url     : https://prove2.me/submissions/24cb4f87-1aee-4d24-aeb8-0821f5be773e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualArithmeticVariety
variable {K : Type} [Field K]
variable [NumberField K] {i : ℕ}
namespace GroundTheory.Heights₂.Heights.DualArithmeticVariety
theorem _root_.solution (F : HermLattice K i) :
    Submodule.span K (dualLattice F : Set (Fin i → K)) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.mpr fun v => ?_
  obtain ⟨S, hS⟩ := F.fg
  obtain ⟨N, hN, hint⟩ := exists_integral_multiples ℤ ℚ (S.image fun g => v ⬝ᵥ g)
  have hmem : (N : K) • v ∈ dualLattice F := by
    intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      have hg' := hint _ (Finset.mem_image_of_mem _ hg)
      rw [smul_dotProduct, Int.cast_smul_eq_zsmul]
      exact RingHom.mem_range.mpr ((IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp hg')
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨c, hc⟩ := hy
      exact ⟨a + c, by rw [dotProduct_add, map_add, ha, hc]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨r * a, ?_⟩
      rw [dotProduct_smul, map_mul, ha]
      rfl
  have hN' : (N : K) ≠ 0 := Int.cast_ne_zero.mpr hN
  have := Submodule.smul_mem (Submodule.span K (dualLattice F : Set (Fin i → K))) (N : K)⁻¹
    (Submodule.subset_span hmem)
  rwa [inv_smul_smul₀ hN'] at this
end GroundTheory.Heights₂.Heights.DualArithmeticVariety
