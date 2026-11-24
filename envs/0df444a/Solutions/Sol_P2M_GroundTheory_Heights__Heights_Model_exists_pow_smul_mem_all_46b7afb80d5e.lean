-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_all_46b7afb80d5e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:43.585787+00:00
-- url     : https://prove2.me/submissions/2d5a3d3a-d6c3-4246-9835-8d65686c343b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_smul_mem_of_chart_c43618aeade3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_prime_pow_smul_mem_5244231e3dc8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_intCast_mem_chartRing_8f356cccfc37


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
theorem _root_.solution {i : τ} (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i))
    {w : E} (hw : w ∈ B₀.lat i) (z : ℤ) (P : S → Prop)
    (hz : ∀ p, P p → (((p : Nat.Primes) : ℕ) : ℤ) ∣ z) :
    ∃ K : ℕ, ∀ K' ≥ K, ∀ p, P p → ((z : Ω) ^ K') • w ∈ (Bp p).lat i := by
  classical
  choose k hk using fun p => exists_prime_pow_smul_mem p (hSR p) hw
  refine ⟨Finset.univ.sup k, fun K' hK' p hp => ?_⟩
  obtain ⟨c, hc⟩ := hz p hp
  have hle : k p ≤ K' := le_trans (Finset.le_sup (Finset.mem_univ p)) hK'
  have : ((z : Ω) ^ K') • w =
      ((z : Ω) ^ (K' - k p) * (c : Ω) ^ k p) • ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ k p • w := by
    rw [smul_smul]
    congr 1
    rw [hc, Int.cast_mul, mul_assoc, ← mul_pow, mul_comm (c : Ω), ← Int.cast_mul, ← hc,
      pow_sub_mul_pow _ hle]
  rw [this]
  exact smul_mem_of_chart (Bp p) (mul_mem (pow_mem (intCast_mem_chartRing x i _ _) _)
    (pow_mem (intCast_mem_chartRing x i _ _) _)) (hk p)
end GroundTheory.Heights₂.Heights.Model
