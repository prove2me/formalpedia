-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_glueLat_overlap_1478a5dc89ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:05:09.808815+00:00
-- url     : https://prove2.me/submissions/3a956313-e650-4ea1-aa22-095ad4a00461

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_smul_mem_of_chart_c43618aeade3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_glueLat_7887799b35f2

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
theorem _root_.solution (i j : τ) (hi : x i ≠ 0) (hj : x j ≠ 0) (e : E)
    (he : e ∈ glueLat B₀ Bp i) : ∃ m : ℕ, (x i / x j) ^ m • e ∈ glueLat B₀ Bp j := by
  classical
  obtain ⟨h0, hp⟩ := (mem_glueLat B₀ Bp).1 he
  obtain ⟨m₀, hm₀⟩ := B₀.overlap i j hi hj e h0
  choose mp hmp using fun p => (Bp p).overlap i j hi hj e (hp p)
  refine ⟨max m₀ (Finset.univ.sup mp), (mem_glueLat B₀ Bp).2 ⟨?_, fun p => ?_⟩⟩
  · rw [← pow_sub_mul_pow _ (le_max_left m₀ (Finset.univ.sup mp)), mul_smul]
    exact smul_mem_of_chart B₀ (pow_mem (div_mem_chartRing x j i) _) hm₀
  · have hle : mp p ≤ max m₀ (Finset.univ.sup mp) :=
      le_trans (Finset.le_sup (Finset.mem_univ p)) (le_max_right _ _)
    rw [← pow_sub_mul_pow _ hle, mul_smul]
    exact smul_mem_of_chart (Bp p) (pow_mem (div_mem_chartRing x j i) _) (hmp p)
end GroundTheory.Heights₂.Heights.Model
