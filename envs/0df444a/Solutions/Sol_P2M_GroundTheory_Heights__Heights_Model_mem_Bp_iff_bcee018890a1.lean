-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_mem_Bp_iff_bcee018890a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:01.03396+00:00
-- url     : https://prove2.me/submissions/0775617a-56e4-4999-b4ed-096e0b5972e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_inv_mem_chartRing_at_8640e36f39af
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_dvd_primeProdErase_78c935ca4e5b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_not_dvd_primeProdErase_f3d914f81af6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_inv_prime_mem_chartRing_6e030817a089
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_smul_mem_of_chart_c43618aeade3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_intCast_smul_mem_3c62fb0adb4f
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
theorem _root_.solution [CharZero Ω] {i : τ} (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (p : S) (v : E) :
    v ∈ (Bp p).lat i ↔ ∃ s : ℤ, ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ s ∧ s • v ∈ glueLat B₀ Bp i := by
  constructor
  · intro hv
    obtain ⟨N, hN0, hN⟩ := (hSR p).2 v hv
    obtain ⟨k, n', hn', hN'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0.ne' ((p : Nat.Primes) : ℕ)
      (p : Nat.Primes).2.one_lt.ne'
    have hw : ((n' : ℤ) : Ω) • v ∈ B₀.lat i := by
      have : ((n' : ℤ) : Ω) • v =
          ((((p : Nat.Primes) : ℕ) : ℤ) : Ω)⁻¹ ^ k • ((N : Ω) • v) := by
        rw [smul_smul, hN']
        congr 1
        have : (((p : Nat.Primes) : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 (p : Nat.Primes).2.ne_zero
        push_cast
        rw [inv_pow, mul_comm ((((p : Nat.Primes) : ℕ) : Ω) ^ k), ← mul_assoc, mul_comm _ (n' : Ω),
          mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ this), mul_one]
      rw [this, Nat.cast_smul_eq_nsmul]
      exact smul_mem_of_chart B₀ (pow_mem (inv_prime_mem_chartRing x o₀ p.2 i) _) hN
    obtain ⟨K, hK⟩ := exists_pow_smul_mem_all hSR hw (primeProdErase S p) (fun q => q ≠ p)
      (fun q hq => dvd_primeProdErase q.2 (fun h => hq (Subtype.ext h)))
    have hs : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ (n' * primeProdErase S p ^ K) := by
      rw [(Nat.prime_iff_prime_int.mp (p : Nat.Primes).2).dvd_mul]
      rintro (h | h)
      · exact hn' (Int.natCast_dvd_natCast.1 h)
      · exact not_dvd_primeProdErase _ ((Nat.prime_iff_prime_int.mp (p : Nat.Primes).2).dvd_of_dvd_pow h)
    refine ⟨n' * primeProdErase S p ^ K, hs, ?_⟩
    rw [← Int.cast_smul_eq_zsmul Ω]
    have heq : (((n' * primeProdErase S p ^ K : ℤ)) : Ω) • v =
        ((primeProdErase S p : Ω) ^ K) • (((n' : ℤ) : Ω) • v) := by
      rw [smul_smul]; congr 1; push_cast; ring
    refine (mem_glueLat B₀ Bp).2 ⟨?_, fun q => ?_⟩
    · rw [heq]
      exact smul_mem_of_chart B₀ (pow_mem (intCast_mem_chartRing x i _ _) _) hw
    · by_cases hq : q = p
      · subst hq
        exact intCast_smul_mem (Bp q) _ hv
      · rw [heq]
        exact hK K le_rfl q hq
  · rintro ⟨s, hs, hsv⟩
    have h0 := ((mem_glueLat B₀ Bp).1 hsv).2 p
    rw [← Int.cast_smul_eq_zsmul Ω] at h0
    obtain ⟨hs0, hsinv⟩ := inv_mem_chartRing_at (o := o) x p i hs
    have : v = ((s : Ω)⁻¹) • ((s : Ω) • v) := by
      rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [this]
    exact smul_mem_of_chart (Bp p) hsinv h0
end GroundTheory.Heights₂.Heights.Model
