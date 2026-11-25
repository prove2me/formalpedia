-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_redSys_invertible_40e65343188b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:06:07.217064+00:00
-- url     : https://prove2.me/submissions/bb25a14c-f306-424a-ab37-e3f2fd99b422

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LineBundleRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLineBundleRestrict
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
variable {γ : Ω} {Q : LineBundle k x}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hγ0 : γ ≠ 0) (hg : RedGood hxy Q.toSubSystem γ) (I : Chart y)
    (hb : ∃ b ∈ chartRing k x (liftChart hxy I), b ∈ locAt k x y ∧ redAt k x y b ≠ 0 ∧
      b * γ ∈ Q.sub (liftChart hxy I)) :
    ∃ M' : Submodule (chartRing k y I) K', (redSys hxy Q.toSubSystem γ).sub I * M' = 1 := by
  obtain ⟨b, -, hbL, hbr, hbγ⟩ := hb
  obtain ⟨M, hM⟩ := Q.invertible (liftChart hxy I)
  refine ⟨Submodule.span (chartRing k y I) ((fun m => redAt k x y (m * γ)) '' M), ?_⟩
  have hA : ∀ {q m : Ω}, q ∈ Q.sub (liftChart hxy I) → m ∈ M →
      q * m ∈ chartRing k x (liftChart hxy I) :=
    fun hq hm => mul_mem_chartRing_of_mul_eq_one hM hq hm
  have hb0 : b ≠ 0 := (locAt_inv hsp hbL hbr).1
  have hmg : ∀ {m : Ω}, m ∈ M → m * γ ∈ locAt k x y := by
    intro m hm
    have h1 := (chartRing_sub_locAt hsp hxy I (hA hbγ hm)).1
    have heq : m * γ = b * γ * m / b := by rw [eq_div_iff hb0]; ring
    rw [heq]; exact (locAt_div hsp h1 hbL hbr).1
  have hsplit : ∀ q m : Ω, q * m = q / γ * (m * γ) := fun q m => by field_simp
  apply le_antisymm
  · change Submodule.span _ _ * Submodule.span _ _ ≤ 1
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨q, hq, rfl⟩, _, ⟨m, hm, rfl⟩, rfl⟩
    show redAt k x y (q / γ) * redAt k x y (m * γ) ∈ (1 : Submodule (chartRing k y I) K')
    rw [← (locAt_mul hsp (hg I q hq) (hmg hm)).2, ← hsplit]
    exact Submodule.mem_one.mpr ⟨⟨_, (chartRing_sub_locAt hsp hxy I (hA hq hm)).2⟩, rfl⟩
  · rw [Submodule.one_le]
    have h1 : (1 : Ω) ∈ Q.sub (liftChart hxy I) * M := by
      rw [hM]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
    have := Submodule.mul_induction_on (C := fun z => z ∈ locAt k x y ∧ redAt k x y z ∈
        (redSys hxy Q.toSubSystem γ).sub I *
          Submodule.span (chartRing k y I) ((fun m => redAt k x y (m * γ)) '' M)) h1
      (fun q hq m hm => ⟨(chartRing_sub_locAt hsp hxy I (hA hq hm)).1, by
        rw [hsplit, (locAt_mul hsp (hg I q hq) (hmg hm)).2]
        exact Submodule.mul_mem_mul (Submodule.subset_span ⟨q, hq, rfl⟩)
          (Submodule.subset_span ⟨m, hm, rfl⟩)⟩)
      (fun u v hu hv => ⟨(locAt_add hsp hu.1 hv.1).1, by
        rw [(locAt_add hsp hu.1 hv.1).2]; exact Submodule.add_mem _ hu.2 hv.2⟩)
    rw [(locAt_one hsp).2] at this
    exact this.2
end GroundTheory.Heights₂.Heights.Kleiman
