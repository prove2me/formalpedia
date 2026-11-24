-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_glueLat_stable_271b11ede81b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:49.838823+00:00
-- url     : https://prove2.me/submissions/ce02a582-5650-44ed-8d30-47db14325cb6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_glueLat_7887799b35f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_chartRing_of_int_e441a7136a3a


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
theorem _root_.solution (i : τ) (a : Ω) (ha : a ∈ chartRing ℤ x i) (e : E)
    (he : e ∈ glueLat B₀ Bp i) : a • e ∈ glueLat B₀ Bp i := by
  obtain ⟨h0, hp⟩ := (mem_glueLat B₀ Bp).1 he
  exact (mem_glueLat B₀ Bp).2 ⟨B₀.stable i a (mem_chartRing_of_int x i o₀ ha) e h0,
    fun p => (Bp p).stable i a (mem_chartRing_of_int x i (o p) ha) e (hp p)⟩
end GroundTheory.Heights₂.Heights.Model
