-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_restrict_gen_01ebcde5e209
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:41:58.135643+00:00
-- url     : https://prove2.me/submissions/6088041b-15f9-4a30-aa4c-ec753c0107e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LineBundleRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLineBundleRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_mem_of_mem_restrictUnion_6649aa89f6fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartRing_sub_locAt_a84ca9ba7312
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_add_75c3baa8859e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_div_084462a2e36e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_inv_eb034c1f50b6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_mul_614d2e1fada9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_one_d19ae30e21d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_chartRing_of_mul_eq_one_e838a6f7d60a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (Q : LineBundle k x) :
    ∃ γ : Ω, γ ≠ 0 ∧ RedGood hxy Q.toSubSystem γ ∧ ∀ I : Chart y,
      ∃ b ∈ chartRing k x (liftChart hxy I), b ∈ locAt k x y ∧ redAt k x y b ≠ 0 ∧
        b * γ ∈ Q.sub (liftChart hxy I) := by
  by_cases hI : Nonempty (Chart y)
  swap
  · exact ⟨1, one_ne_zero, fun I => (hI ⟨I⟩).elim, fun I => (hI ⟨I⟩).elim⟩
  obtain ⟨I₀⟩ := hI
  obtain ⟨M, hM⟩ := Q.invertible (liftChart hxy I₀)
  have hA : ∀ {q m : Ω}, q ∈ Q.sub (liftChart hxy I₀) → m ∈ M → q * m ∈ locAt k x y :=
    fun hq hm => (chartRing_sub_locAt hsp hxy I₀ (mul_mem_chartRing_of_mul_eq_one hM hq hm)).1
  have h1 : (1 : Ω) ∈ Q.sub (liftChart hxy I₀) * M := by
    rw [hM]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨γ, hγ, m₀, hm₀, hne⟩ :
      ∃ γ ∈ Q.sub (liftChart hxy I₀), ∃ m₀ ∈ M, redAt k x y (γ * m₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := Submodule.mul_induction_on (C := fun z => z ∈ locAt k x y ∧ redAt k x y z = 0) h1
      (fun q hq m hm => ⟨hA hq hm, hcon q hq m hm⟩)
      (fun u v hu hv => ⟨(locAt_add hsp hu.1 hv.1).1, by
        rw [(locAt_add hsp hu.1 hv.1).2, hu.2, hv.2, add_zero]⟩)
    rw [(locAt_one hsp).2] at this
    exact one_ne_zero this.2
  have hγm := hA hγ hm₀
  have hγm0 := (locAt_inv hsp hγm hne).1
  have hγ0 : γ ≠ 0 := left_ne_zero_of_mul hγm0
  have hm0 : m₀ ≠ 0 := right_ne_zero_of_mul hγm0
  refine ⟨γ, hγ0, ?_, ?_⟩
  · intro I q hq
    have hsub : I.1 ⊆ (restrictUnion I₀ I).1 := Finset.subset_union_right
    obtain ⟨a, -, haL, har, haq⟩ := exists_mul_mem_of_mem_restrictUnion hsp hxy Q I₀ I
      (Q.mono (liftChart hxy I) (liftChart hxy (restrictUnion I₀ I)) hsub q hq)
    have ha0 : a ≠ 0 := (locAt_inv hsp haL har).1
    have hnum := hA haq hm₀
    have hden := locAt_mul hsp haL hγm
    have hden0 : redAt k x y (a * (γ * m₀)) ≠ 0 := by rw [hden.2]; exact mul_ne_zero har hne
    have heq : q / γ = a * q * m₀ / (a * (γ * m₀)) := by
      rw [mul_assoc a q m₀, mul_div_mul_left _ _ ha0, mul_div_mul_right _ _ hm0]
    rw [heq]; exact (locAt_div hsp hnum hden.1 hden0).1
  · intro I
    have hsub : I₀.1 ⊆ (restrictUnion I I₀).1 := Finset.subset_union_right
    exact exists_mul_mem_of_mem_restrictUnion hsp hxy Q I I₀
      (Q.mono (liftChart hxy I₀) (liftChart hxy (restrictUnion I I₀)) hsub γ hγ)
end GroundTheory.Heights₂.Heights.Kleiman
