-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_glueLat_frame_f0b793a7400f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:10:30.397646+00:00
-- url     : https://prove2.me/submissions/d68d672d-3f80-4c94-acb0-616cd1041a68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrameP
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PChartGlue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_frame_cover_ac01afdb2b09
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_frame_at_prime_1f139d9a93c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_frame_away_41fe0ec9e5f5


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
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {Ω : Type} [Field Ω] [CharZero Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
    {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
    {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
    [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
    [∀ p, Algebra (o p) Ω] {B₀ : ChartBundle o₀ x r E} {Bp : ∀ p, ChartBundle (o p) x r E}
    {i : τ} (hi : x i ≠ 0) (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) :
    ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing ℤ x i) ∧ (∀ l, c l ∈ chartRing ℤ x i) ∧
      ∑ l, c l * f l = 1 ∧ ∀ l, IsFrameAt (chartRing ℤ x i) r (glueLat B₀ Bp i) (f l) := by
  refine exists_frame_cover _ r _ fun Q hQ => ?_
  by_cases hmQ : ((primeProd S : ℤ) : chartRing ℤ x i) ∈ Q
  · rw [primeProd, Int.cast_prod] at hmQ
    obtain ⟨p, hp, hpQ⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hQ.isPrime)).1 hmQ
    exact frame_at_prime hi hSR Q hQ.isPrime ⟨p, hp⟩ hpQ
  · exact frame_away hi hSR Q hQ.isPrime hmQ
end GroundTheory.Heights₂.Heights.Model
