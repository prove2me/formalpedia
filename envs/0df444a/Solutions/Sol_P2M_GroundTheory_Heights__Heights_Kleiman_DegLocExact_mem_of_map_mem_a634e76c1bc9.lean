-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_mem_of_map_mem_a634e76c1bc9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:01:14.895832+00:00
-- url     : https://prove2.me/submissions/faa3b7cb-b049-449b-97c8-47f5e17d3d1e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDegLocExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_decompose_map_2289620b9997

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
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hφ : ∀ i a, a ∈ 𝒜 i → φ a ∈ ℬ i)
    (hinj : Function.Injective φ) {a : A} {k : ι} (ha : φ a ∈ ℬ k) : a ∈ 𝒜 k := by
  have h := decompose_map 𝒜 ℬ φ h0 hadd hφ a k
  rw [DirectSum.decompose_of_mem_same (ℳ := ℬ) ha] at h
  rw [← hinj h]
  exact SetLike.coe_mem _
end GroundTheory.Heights₂.Heights.Kleiman.DegLocExact
