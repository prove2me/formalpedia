-- Prove2me | solution 1 for P2M_GroundTheory_Variant__N1_exists_smul_mem_of_span_eq_top_4736e841ecc6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:45:57.185794+00:00
-- url     : https://prove2.me/submissions/0c218b6e-bcb6-445e-a16b-0e8bac7aad77

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsSmulMemFamilyOfSpanEqTop

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
    (hM : Submodule.span K (M : Set (Fin N → K)) = ⊤) (x : Fin N → K) :
    ∃ t : RingOfIntegers K, t ≠ 0 ∧ algebraMap (RingOfIntegers K) K t • x ∈ M := by
  have hx : x ∈ Submodule.span K (M : Set (Fin N → K)) := by rw [hM]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have h1 : algebraMap (RingOfIntegers K) K (s * t) • y
        = t • (algebraMap (RingOfIntegers K) K s • y) := by
      rw [map_mul, mul_comm, mul_smul, algebraMap_smul]
    have h2 : algebraMap (RingOfIntegers K) K (s * t) • z
        = s • (algebraMap (RingOfIntegers K) K t • z) := by
      rw [map_mul, mul_smul, algebraMap_smul]
    rw [smul_add, h1, h2]
    exact M.add_mem (M.smul_mem t hsy) (M.smul_mem s htz)
  | smul c y _ hy =>
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers K)) c
    simp only at hab
    refine ⟨(b : RingOfIntegers K) * t, mul_ne_zero (nonZeroDivisors.coe_ne_zero b) ht, ?_⟩
    have key : algebraMap (RingOfIntegers K) K ((b : RingOfIntegers K) * t) • (c • y)
        = a • (algebraMap (RingOfIntegers K) K t • y) := by
      rw [← algebraMap_smul K a (algebraMap (RingOfIntegers K) K t • y), smul_smul, smul_smul,
        ← hab, map_mul]
      congr 1
      ring
    rw [key]
    exact M.smul_mem a hty
end GroundTheory.Variant₂.N1
