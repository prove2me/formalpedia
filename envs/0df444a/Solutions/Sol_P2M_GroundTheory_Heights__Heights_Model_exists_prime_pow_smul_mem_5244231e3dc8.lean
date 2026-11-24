-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_prime_pow_smul_mem_5244231e3dc8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:13.043838+00:00
-- url     : https://prove2.me/submissions/df75b1b3-a208-4cf8-9b33-1e8cd6b80653

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_inv_mem_chartRing_at_8640e36f39af
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_smul_mem_of_chart_c43618aeade3

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
variable {Ω : Type} [Field Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]
variable (B₀ : ChartBundle o₀ x r E) (Bp : ∀ p, ChartBundle (o p) x r E)
variable {B₀ Bp}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {i : τ} (p : S)
    (hSR : SameRationalSpan (B₀.lat i) ((Bp p).lat i)) {w : E} (hw : w ∈ B₀.lat i) :
    ∃ k : ℕ, ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ k • w ∈ (Bp p).lat i := by
  obtain ⟨N, hN0, hN⟩ := hSR.1 w hw
  obtain ⟨k, n', hn', hN'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0.ne' ((p : Nat.Primes) : ℕ)
    (p : Nat.Primes).2.one_lt.ne'
  refine ⟨k, ?_⟩
  have hs : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ (n' : ℤ) := fun h => hn' (Int.natCast_dvd_natCast.1 h)
  obtain ⟨hs0, hsinv⟩ := inv_mem_chartRing_at (o := o) x p i hs
  have : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ k • w = ((n' : ℤ) : Ω)⁻¹ • ((N : Ω) • w) := by
    rw [smul_smul, hN']
    congr 1
    push_cast at hs0 ⊢
    field_simp
  rw [this, Nat.cast_smul_eq_nsmul]
  exact smul_mem_of_chart (Bp p) hsinv hN
end GroundTheory.Heights₂.Heights.Model
