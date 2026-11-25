-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.eig_of_alpha
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:32:43.79+00:00
-- url     : https://prove2.me/submissions/546890a8-95cb-4a76-bf51-f1c0a27f1057

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_LieBridgeB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_aeval_eig

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
theorem _root_.solution (hN : ∀ a : O, ∃ (N : ℤ) (g : ℤ[X]), N ≠ 0 ∧ (N : O) * a = aeval α g) (τ : ι) {m : M}
    (hm : ρ α m = algebraMap K S (χ τ α) • m) : IsEigV ρ (χ τ) m := by
  intro a
  obtain ⟨N, g, hN0, hg⟩ := hN a
  have h1 := aeval_eig (ρ α) hm g
  have hL : aeval (ρ α) g = ρ (aeval α g) := aeval_algHom_apply ρ.toIntAlgHom α g
  have hR : aeval (algebraMap K S (χ τ α)) g = algebraMap K S (χ τ (aeval α g)) :=
    aeval_algHom_apply ((algebraMap K S).comp (χ τ)).toIntAlgHom α g
  rw [hL, hR, ← hg, map_mul, map_mul, map_intCast, map_intCast, map_mul, map_intCast,
    Module.End.mul_apply, mul_smul] at h1
  have hNK : (N : K) ≠ 0 := Int.cast_ne_zero.mpr hN0

  have cancel : ∀ y : M, algebraMap K S ((N : K)⁻¹) • ((N : S) • y) = y := by
    intro y
    rw [smul_smul, ← map_intCast (algebraMap K S) N, ← map_mul, inv_mul_cancel₀ hNK, map_one, one_smul]
  have hE : ((N : Module.End S M) (ρ a m)) = (N : S) • ρ a m := by
    rw [Int.cast_smul_eq_zsmul S N (ρ a m)]
    simp
  rw [hE] at h1
  rw [← cancel (ρ a m), h1, cancel]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
