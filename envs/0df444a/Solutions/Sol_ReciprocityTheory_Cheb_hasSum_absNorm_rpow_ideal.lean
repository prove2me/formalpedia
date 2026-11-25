-- Prove2me | solution 1 for ReciprocityTheory.Cheb.hasSum_absNorm_rpow_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:43:13.330214+00:00
-- url     : https://prove2.me/submissions/20b9cbd3-60a8-4174-b1f6-42e6e82b59ec

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Theorems.Thm_ReciprocityTheory_Cheb_summable_absNorm_rpow_ideal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    HasSum (fun a : Ideal (𝓞 E) => ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s)) (idealZetaR E s) := by
  have hsum := (summable_absNorm_rpow_ideal E hs).hasSum
  have h1 := ((Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 E) → ℕ)).hasSum_iff).mpr hsum
  have h2 := h1.sigma (g := fun n : ℕ =>
      (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)) (fun n ↦ by
    have : Finite {I : Ideal (𝓞 E) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 E) n).to_subtype
    have hc : ∀ c : {I : Ideal (𝓞 E) // Ideal.absNorm I = n},
        ((Ideal.absNorm (Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 E) → ℕ) ⟨n, c⟩) : ℕ) : ℝ)
          ^ (-s) = (n : ℝ) ^ (-s) := fun c ↦ by
      simp [Equiv.sigmaFiberEquiv, c.2]
    simp only [Function.comp_apply, hc]
    have h3 : HasSum (fun _ : {I : Ideal (𝓞 E) // Ideal.absNorm I = n} ↦ (n : ℝ) ^ (-s))
        (∑' _ : {I : Ideal (𝓞 E) // Ideal.absNorm I = n}, (n : ℝ) ^ (-s)) :=
      Summable.of_finite.hasSum
    rw [tsum_const, nsmul_eq_mul] at h3
    exact h3)
  rw [idealZetaR, h2.tsum_eq]
  exact hsum
end ReciprocityTheory.Cheb
