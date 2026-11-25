-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_int_smul_mem_4c8901af79bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:21:17.766187+00:00
-- url     : https://prove2.me/submissions/1c6c9d21-8d5e-4800-a96d-c519d7f23a33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField DualArithmeticVariety
noncomputable section
open GroundTheory.Heights₂.Heights.StandardModelDualRank
variable {K : Type} [Field K] {i : ℕ}
variable [NumberField K]
namespace GroundTheory.Heights₂.Heights.StandardModelDualRank
theorem _root_.solution (F : HermLattice K i) (v : Fin i → K) :
    ∃ N : ℤ, N ≠ 0 ∧ (N : K) • v ∈ dualLattice F := by
  classical
  obtain ⟨S, hS⟩ := F.fg
  obtain ⟨N, hN, hint⟩ := exists_integral_multiples ℤ ℚ (S.image fun g => v ⬝ᵥ g)
  refine ⟨N, hN, fun x hx => ?_⟩
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
end GroundTheory.Heights₂.Heights.StandardModelDualRank
