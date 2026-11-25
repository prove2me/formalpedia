-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_vaes_mem_pow_of_forall_6563325dceaa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:22:03.206672+00:00
-- url     : https://prove2.me/submissions/9ea1fa82-b2f3-4eba-b8e0-65acbb5e4963

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleEmbedSectionsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleEmbedSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_eq_pow_ebcff08057ae


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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {y : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (Q : LineBundle k y) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Q.toSubSystem h) (I : Chart y) {m : ℕ} {s : Ω}
    (hs : ∀ j, h j ≠ 0 → ∃ e : ℕ, s * h j ^ e ∈ (Q.toSubSystem.pow (m + e)).sub I) :
    s ∈ (Q.toSubSystem.pow m).sub I := by
  have hs' : ∀ j, h j ≠ 0 → ∃ e : ℕ, s * h j ^ e ∈ Q.toSubSystem.sub I ^ (m + e) := fun j hj => by
    obtain ⟨e, he⟩ := hs j hj
    exact ⟨e, by rw [← SubSystem.pow_sub_eq_pow Q.toSubSystem]; exact he⟩
  rw [SubSystem.pow_sub_eq_pow Q.toSubSystem]
  clear hs
  obtain ⟨P', hPP'⟩ := Q.invertible I
  set P := Q.toSubSystem.sub I with hP
  let c : Ideal (chartRing k y I) := (P ^ m).comap (LinearMap.toSpanSingleton _ Ω s)
  have hc : ∀ a, a ∈ c ↔ (a : Ω) * s ∈ P ^ m := fun a => by
    change a • s ∈ P ^ m ↔ _; rw [chartRing_smul_def]
  have key : ∀ j, ∀ q ∈ P', ∀ a : chartRing k y I, (a : Ω) = h j * q → a ∈ c.radical := by
    intro j q hq a ha
    by_cases hj : h j = 0
    · have : a = 0 := Subtype.ext (by rw [ha, hj, zero_mul]; rfl)
      rw [this]; exact Ideal.zero_mem _
    obtain ⟨e, he⟩ := hs' j hj
    refine ⟨e, (hc _).mpr ?_⟩
    have hmem := Submodule.mul_mem_mul he (Submodule.pow_mem_pow P' hq e)
    rw [pow_add, mul_assoc, ← mul_pow, hPP', one_pow, mul_one] at hmem
    rw [Subalgebra.coe_pow, ha]
    convert hmem using 1
    ring
  let M : Submodule (chartRing k y I) Ω := Submodule.map (Algebra.linearMap (chartRing k y I) Ω) c.radical
  have hle : P * P' ≤ M := by
    refine Submodule.mul_le.mpr fun p hp q hq => ?_
    rw [hP, ← hv.generates I] at hp
    induction hp using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      have h1 : h j * q ∈ P * P' := Submodule.mul_mem_mul
        (by rw [hP, ← hv.generates I]; exact Submodule.subset_span ⟨j, rfl⟩) hq
      rw [hPP'] at h1
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp h1
      exact ⟨a, key j q hq a ha, ha⟩
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add u v _ _ hu hv => rw [add_mul]; exact Submodule.add_mem _ hu hv
    | smul a u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hu
  have h1 : (1 : Ω) ∈ M := hle (by rw [hPP']; exact Submodule.one_le.mp le_rfl)
  obtain ⟨a, ha, ha1⟩ := h1
  have : a = 1 := Subtype.ext ha1
  have ha' : (1 : chartRing k y I) ∈ c.radical := this ▸ ha
  rw [← Ideal.eq_top_iff_one, Ideal.radical_eq_top, Ideal.eq_top_iff_one, hc] at ha'
  simpa using ha'
end GroundTheory.Heights₂.Heights.Kleiman
