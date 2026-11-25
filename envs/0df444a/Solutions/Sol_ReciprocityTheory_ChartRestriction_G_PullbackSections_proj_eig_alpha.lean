-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_eig_alpha
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:33:53.735433+00:00
-- url     : https://prove2.me/submissions/7db5c13d-0788-4226-a4a1-62c5b3d141c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_LieBridgeB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_X_sub_mul_lagr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open Polynomial
variable {K S M O ι : Type} [Field K] [CharZero K] [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M]
  [CommRing O] [Fintype ι] [DecidableEq ι] (ρ : O →+* Module.End S M) (χ : ι → O →+* K) (α : O)
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (hα : Function.Injective fun τ => χ τ α) (f : ℤ[X]) (hf : aeval α f = 0)
    (hfs : f.map (Int.castRingHom K) = ∏ τ, (X - C (χ τ α))) (τ : ι) (m : M) :
    ρ α (proj ρ χ α τ m) = algebraMap K S (χ τ α) • proj ρ χ α τ m := by
  have hk := congrArg (Polynomial.map (algebraMap K S)) (X_sub_mul_lagr (fun τ => χ τ α) hα τ)
  rw [← hfs] at hk
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_C, Polynomial.map_map] at hk
  have hz : aeval (ρ α) (f.map ((algebraMap K S).comp (Int.castRingHom K))) = 0 := by
    rw [show (algebraMap K S).comp (Int.castRingHom K) = algebraMap ℤ S from RingHom.ext_int _ _,
      aeval_map_algebraMap]
    have e : aeval (ρ α) f = ρ (aeval α f) := aeval_algHom_apply ρ.toIntAlgHom α f
    rw [e, hf, map_zero]
  have h1 := congrArg (aeval (ρ α)) hk
  rw [map_mul, map_mul, hz, mul_zero, map_sub, aeval_X, aeval_C] at h1
  have h2 := congrArg (fun g : Module.End S M => g m) h1
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply,
    LinearMap.zero_apply] at h2
  unfold proj
  exact sub_eq_zero.mp h2
end ReciprocityTheory.ChartRestriction.G.PullbackSections
