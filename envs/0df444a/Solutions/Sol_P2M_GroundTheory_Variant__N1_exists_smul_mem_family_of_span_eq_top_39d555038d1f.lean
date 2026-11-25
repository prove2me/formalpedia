-- Prove2me | solution 1 for P2M_GroundTheory_Variant__N1_exists_smul_mem_family_of_span_eq_top_39d555038d1f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:41.66709+00:00
-- url     : https://prove2.me/submissions/1b4514ef-a100-4f26-8904-8f3faabfe34f

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsSmulMemFamilyOfSpanEqTop
import Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_smul_mem_of_span_eq_top_4736e841ecc6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1
open NumberField
namespace GroundTheory.Variant₂.N1
theorem _root_.solution {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (RingOfIntegers K) (Fin N → K))
    (hM : Submodule.span K (M : Set (Fin N → K)) = ⊤)
    {ι : Type*} [Fintype ι] (v : ι → Fin N → K) :
    ∃ t : RingOfIntegers K, t ≠ 0 ∧ ∀ i, algebraMap (RingOfIntegers K) K t • v i ∈ M := by
  classical
  choose s hs hsv using fun i => exists_smul_mem_of_span_eq_top M hM (v i)
  refine ⟨∏ i, s i, Finset.prod_ne_zero_iff.mpr fun i _ => hs i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i), mul_comm, map_mul, mul_smul,
    algebraMap_smul]
  exact M.smul_mem _ (hsv i)
end GroundTheory.Variant₂.N1
