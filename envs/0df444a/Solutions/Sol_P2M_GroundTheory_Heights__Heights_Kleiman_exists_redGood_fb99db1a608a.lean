-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_redGood_fb99db1a608a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:19:16.879801+00:00
-- url     : https://prove2.me/submissions/7d79e316-b481-47a5-adb4-57f67d907643

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_chartRing_of_mul_eq_one_e838a6f7d60a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_sub_of_isVeryAmpleBy_4e23af4f9328
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartRing_sub_locAt_a84ca9ba7312
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_add_75c3baa8859e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_div_084462a2e36e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_inv_eb034c1f50b6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_mul_614d2e1fada9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_one_d19ae30e21d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_zero_68297b898f07


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
  (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
  {Nb : LineBundle k x} {r : ℕ} {h : Fin (r + 1) → Ω}
include hsp
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hV : IsVeryAmpleBy Nb.toSubSystem h) (I₀ : Chart y) :
    ∃ l₀ : Fin (r + 1), h l₀ ≠ 0 ∧ (∀ l, h l / h l₀ ∈ locAt k x y) ∧
      RedGood hxy Nb.toSubSystem (h l₀) := by
  obtain ⟨M, hM⟩ := Nb.invertible (liftChart hxy I₀)
  have hgen := hV.generates (liftChart hxy I₀)
  have hA : ∀ {q m : Ω}, q ∈ Nb.sub (liftChart hxy I₀) → m ∈ M → q * m ∈ locAt k x y :=
    fun hq hm => (chartRing_sub_locAt hsp hxy I₀ (mul_mem_chartRing_of_mul_eq_one hM hq hm)).1
  have h1 : (1 : Ω) ∈ Nb.sub (liftChart hxy I₀) * M := by
    rw [hM]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨l₀, m₀, hm₀, hne⟩ : ∃ l₀, ∃ m₀ ∈ M, redAt k x y (h l₀ * m₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : ∀ q ∈ Nb.sub (liftChart hxy I₀), ∀ m ∈ M, redAt k x y (q * m) = 0 := by
      intro q hq m hm
      rw [← hgen] at hq
      refine Submodule.span_induction (p := fun q _ => redAt k x y (q * m) = 0) ?_ ?_ ?_ ?_ hq
      · rintro _ ⟨l, rfl⟩; exact hcon l m hm
      · rw [zero_mul]; exact (locAt_zero hsp).2
      · intro u v hu hv ihu ihv
        rw [add_mul, (locAt_add hsp (hA (hgen ▸ hu) hm) (hA (hgen ▸ hv) hm)).2, ihu, ihv, add_zero]
      · intro c u hu ihu
        rw [chartRing_smul_def, mul_assoc,
          (locAt_mul hsp (chartRing_sub_locAt hsp hxy I₀ c.2).1 (hA (hgen ▸ hu) hm)).2, ihu, mul_zero]
    have := Submodule.mul_induction_on (C := fun z => z ∈ locAt k x y ∧ redAt k x y z = 0) h1
      (fun q hq m hm => ⟨hA hq hm, hzero q hq m hm⟩)
      (fun u v hu hv => ⟨(locAt_add hsp hu.1 hv.1).1, by
        rw [(locAt_add hsp hu.1 hv.1).2, hu.2, hv.2, add_zero]⟩)
    rw [(locAt_one hsp).2] at this
    exact one_ne_zero this.2
  have hgm : h l₀ * m₀ ∈ locAt k x y := hA (mem_sub_of_isVeryAmpleBy hV l₀ _) hm₀
  have hgm0 := (locAt_inv hsp hgm hne).1
  have hg0 : h l₀ ≠ 0 := left_ne_zero_of_mul hgm0
  have hm0 : m₀ ≠ 0 := right_ne_zero_of_mul hgm0
  have hl : ∀ l, h l / h l₀ ∈ locAt k x y := by
    intro l
    rw [← mul_div_mul_right (h l) (h l₀) hm0]
    exact (locAt_div hsp (hA (mem_sub_of_isVeryAmpleBy hV l _) hm₀) hgm hne).1
  refine ⟨l₀, hg0, hl, ?_⟩
  intro I q hq
  have hgenI := hV.generates (liftChart hxy I)
  rw [← hgenI] at hq
  refine Submodule.span_induction (p := fun q _ => q / h l₀ ∈ locAt k x y) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨l, rfl⟩; exact hl l
  · rw [zero_div]; exact (locAt_zero hsp).1
  · intro u v _ _ hu hv; rw [add_div]; exact (locAt_add hsp hu hv).1
  · intro c u _ hu
    rw [chartRing_smul_def, mul_div_assoc]
    exact (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 hu).1
end GroundTheory.Heights₂.Heights.Kleiman
