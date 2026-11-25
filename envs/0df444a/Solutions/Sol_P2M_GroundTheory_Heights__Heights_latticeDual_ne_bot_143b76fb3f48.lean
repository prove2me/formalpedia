-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_latticeDual_ne_bot_143b76fb3f48
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:41:32.506288+00:00
-- url     : https://prove2.me/submissions/a19618e2-387b-4a36-bae7-4661d0c67368

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PDualBasisExists

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
open NumberField Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {r : ℕ} (F : HermLattice K (r + 1)) :
    ∃ ψ ∈ latticeDual F.lattice, ψ ≠ 0 := by
  classical
  obtain ⟨s, hs⟩ := F.fg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (s.image fun v ↦ v 0)
  have hbne : algebraMap (𝓞 K) K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  refine ⟨Pi.single 0 (algebraMap (𝓞 K) K b), ?_, fun h ↦ hbne (by simpa using congrFun h 0)⟩
  intro v hv
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hb (x 0) (Finset.mem_image_of_mem _ hx)
    refine ⟨a, ?_⟩
    rw [ha, Algebra.smul_def]
    simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨a + c, by rw [map_add, ha, hc, dotProduct_add]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [map_mul, ha, dotProduct_smul, Algebra.smul_def]⟩
end GroundTheory.Heights₂.Heights
