-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_decompose_map_2289620b9997
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:30.936573+00:00
-- url     : https://prove2.me/submissions/8b4cb241-52e5-4f6c-8dd2-88a6b1521f6a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDegLocExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.DegLocExact
namespace GroundTheory.Heights₂.Heights.Kleiman.DegLocExact
theorem _root_.solution {ι R A B : Type*} [DecidableEq ι] [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ] (φ : A → B) (h0 : φ 0 = 0)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hφ : ∀ i a, a ∈ 𝒜 i → φ a ∈ ℬ i) (a : A) (k : ι) :
    φ (DirectSum.decompose 𝒜 a k) = DirectSum.decompose ℬ (φ a) k := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp [h0]
  | @homogeneous i m =>
    obtain ⟨m, hm⟩ := m
    by_cases hik : i = k
    · subst hik
      rw [DirectSum.decompose_of_mem_same (ℳ := 𝒜) hm,
        DirectSum.decompose_of_mem_same (ℳ := ℬ) (hφ _ _ hm)]
    · rw [DirectSum.decompose_of_mem_ne (ℳ := 𝒜) hm hik,
        DirectSum.decompose_of_mem_ne (ℳ := ℬ) (hφ _ _ hm) hik, h0]
  | add m m' hm hm' => simp [hadd, DirectSum.decompose_add, hm, hm']
end GroundTheory.Heights₂.Heights.Kleiman.DegLocExact
