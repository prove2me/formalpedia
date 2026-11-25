-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_mem_B__iff_9151688a4893
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:40:59.653974+00:00
-- url     : https://prove2.me/submissions/2a6da479-134f-42b4-98ca-99f893e83767

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_inv_prod_mem_chartRing_6138e0eacf84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_dvd_primeProd_4e2ae87d1026
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_smul_mem_of_chart_c43618aeade3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_glueLat_7887799b35f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_all_46b7afb80d5e
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
theorem _root_.solution {i : τ} (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (v : E) :
    v ∈ B₀.lat i ↔ ∃ n : ℕ, primeProd S ^ n • v ∈ glueLat B₀ Bp i := by
  constructor
  · intro hv
    obtain ⟨K, hK⟩ := exists_pow_smul_mem_all hSR hv (primeProd S) (fun _ => True)
      (fun p _ => dvd_primeProd p.2)
    refine ⟨K, (mem_glueLat B₀ Bp).2 ⟨?_, fun p => ?_⟩⟩
    · rw [← Int.cast_smul_eq_zsmul Ω, Int.cast_pow]
      exact smul_mem_of_chart B₀ (pow_mem (intCast_mem_chartRing x i _ _) _) hv
    · rw [← Int.cast_smul_eq_zsmul Ω, Int.cast_pow]
      exact hK K le_rfl p trivial
  · rintro ⟨n, hn⟩
    have h0 := ((mem_glueLat B₀ Bp).1 hn).1
    rw [← Int.cast_smul_eq_zsmul Ω, Int.cast_pow] at h0
    obtain ⟨hm0, hm⟩ := inv_prod_mem_chartRing x o₀ (S := S) i
    have : v = (((primeProd S : ℤ) : Ω)⁻¹) ^ n • (((primeProd S : ℤ) : Ω) ^ n • v) := by
      rw [smul_smul, ← mul_pow, inv_mul_cancel₀ hm0, one_pow, one_smul]
    rw [this]
    exact smul_mem_of_chart B₀ (pow_mem hm _) h0
end GroundTheory.Heights₂.Heights.Model
