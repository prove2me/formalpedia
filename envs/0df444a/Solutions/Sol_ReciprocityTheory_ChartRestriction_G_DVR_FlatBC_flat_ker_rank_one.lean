-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.flat_ker_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:52:19.152269+00:00
-- url     : https://prove2.me/submissions/16efda0f-3798-43d1-9fab-d4a986a78547

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
namespace ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
theorem _root_.solution (δ : M →ₗ[R] N) (θ : M) (hker : ∀ m, δ m = 0 ↔ ∃ r : R, m = r • θ)
    (hfree : ∀ r : R, r • θ = 0 → r = 0) (t : S ⊗[R] M) (ht : δ.lTensor S t = 0) :
    ∃! a : S, t = a ⊗ₜ[R] θ := by
  let ι : R →ₗ[R] M := LinearMap.toSpanSingleton R M θ
  have hex : Function.Exact ι δ := by
    intro m
    constructor
    · intro h
      obtain ⟨r, rfl⟩ := (hker m).1 h
      exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩
      exact (hker _).2 ⟨r, rfl⟩
  have hinj : Function.Injective ι := fun r r' h => by
    have : (r - r') • θ = 0 := by rw [sub_smul]; exact sub_eq_zero.2 h
    exact sub_eq_zero.1 (hfree _ this)
  have hexS : Function.Exact (ι.lTensor S) (δ.lTensor S) := Module.Flat.lTensor_exact S hex
  have hinjS : Function.Injective (ι.lTensor S) := Module.Flat.lTensor_preserves_injective_linearMap ι hinj
  obtain ⟨x, hx⟩ := (hexS t).1 ht
  have key : ∀ a : S, ι.lTensor S (a ⊗ₜ[R] (1 : R)) = a ⊗ₜ[R] θ := fun a => by
    simp [ι, LinearMap.lTensor_tmul]
  have hxa : x = (TensorProduct.rid R S x) ⊗ₜ[R] (1 : R) := by
    conv_lhs => rw [← (TensorProduct.rid R S).symm_apply_apply x]
    rfl
  refine ⟨TensorProduct.rid R S x, ?_, fun a ha => ?_⟩
  · show t = _
    rw [← hx, ← key]; exact congrArg _ hxa
  · have h1 : ι.lTensor S (a ⊗ₜ[R] (1 : R)) = ι.lTensor S x := by rw [key, hx, ha]
    have h2 := congrArg (TensorProduct.rid R S) (hinjS h1)
    simpa using h2
end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
