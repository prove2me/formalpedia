-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_inv_mem_chartRing_at_8640e36f39af
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:00.952469+00:00
-- url     : https://prove2.me/submissions/33199f55-d67e-4d6c-bd37-6a007f0a9a7f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_primeTo_af81357ada47
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_inv_mem_chartRing_loc_47fca36ef53c


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
variable (x)
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (p : S) (i : τ) {s : ℤ} (hs : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ s) :
    (s : Ω) ≠ 0 ∧ (s : Ω)⁻¹ ∈ chartRing (o p) x i :=
  inv_mem_chartRing_loc x i (o p) (primeTo (p : Nat.Primes)) (mem_primeTo.2 hs)
end GroundTheory.Heights₂.Heights.Model
