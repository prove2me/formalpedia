-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_mem_of_prime_pow_mul_mem_59b855d6fd12
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:44.025148+00:00
-- url     : https://prove2.me/submissions/7425b580-5b20-4043-9a40-da8a3f57b984

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {A : Subalgebra ℤ Ω} {p : ℕ} (hp : p.Prime) {s : ℤ}
    (hs : ¬ (p : ℤ) ∣ s) (N : ℕ) {y : Ω} (h1 : (((p : ℤ) : Ω)) ^ N * y ∈ A)
    (h2 : (s : Ω) * y ∈ A) : y ∈ A := by
  have hcop : IsCoprime ((p : ℤ) ^ N) s := by
    have : IsCoprime (p : ℤ) s := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : ¬ p ∣ s.natAbs := fun h => hs (Int.natCast_dvd.mpr h)
      simpa [Int.gcd] using (Nat.Prime.coprime_iff_not_dvd hp).mpr this
    exact this.pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have : y = (u : Ω) * ((((p : ℤ) : Ω)) ^ N * y) + (v : Ω) * ((s : Ω) * y) := by
    have h := congrArg (Int.cast : ℤ → Ω) huv
    push_cast at h ⊢
    linear_combination (-y) * h
  rw [this]
  exact add_mem (mul_mem (intCast_mem A u) h1) (mul_mem (intCast_mem A v) h2)
end GroundTheory.Heights₂.Heights.Model
