-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_int_smul_mem_latticeDual_7ca10bc0ad16
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:49.206121+00:00
-- url     : https://prove2.me/submissions/0254921b-d9d1-4e41-b60d-93652dc04542

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints

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
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) (hL : L.FG)
    (v : Fin m → K) : ∃ D : ℤ, D ≠ 0 ∧ D • v ∈ latticeDual L := by
  classical
  obtain ⟨S, hS⟩ := hL
  have hint : ∀ k : ℤ, IsIntegral ℤ (k : K) := fun k ↦ by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K k))
  have h1 : ∀ s : Fin m → K, ∃ D : ℤ, D ≠ 0 ∧ IsIntegral ℤ ((D : K) * (v ⬝ᵥ s)) := by
    intro s
    have halg : IsAlgebraic ℤ (v ⬝ᵥ s) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic _)
    obtain ⟨D, hD, hD'⟩ := halg.exists_integral_multiple
    exact ⟨D, hD, by rwa [zsmul_eq_mul] at hD'⟩
  choose D hD0 hDint using h1
  refine ⟨∏ s ∈ S, D s, Finset.prod_ne_zero_iff.mpr fun s _ ↦ hD0 s, ?_⟩
  intro u hu
  rw [← hS] at hu
  rw [Set.mem_range, ← IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 K)]
  induction hu using Submodule.span_induction with
  | mem x hx =>
    rw [smul_dotProduct, zsmul_eq_mul, ← Finset.mul_prod_erase S D hx, Int.cast_mul,
      mul_comm (D x : K), mul_assoc]
    exact (hint _).mul (hDint x)
  | zero => simpa using (isIntegral_zero : IsIntegral ℤ (0 : K))
  | add x y _ _ hx hy => rw [dotProduct_add]; exact hx.add hy
  | smul c x _ hx =>
    rw [dotProduct_smul, Algebra.smul_def]
    exact ((IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 K)).mpr ⟨c, rfl⟩).mul hx
end GroundTheory.Heights₂.Heights
