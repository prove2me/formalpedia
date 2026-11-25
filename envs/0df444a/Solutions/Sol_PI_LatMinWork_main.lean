-- Prove2me | solution 1 for PI.LatMinWork.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:12.475094+00:00
-- url     : https://prove2.me/submissions/1f855e28-10fa-43ab-895f-f0d3470dcf0f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinimalLatticeNorm_NormTwoEqOne
import Theorems.Thm_PI_LatMinWork_norm_two_eq_one
import Theorems.Thm_PI_LatMinWork_bound_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LatMinWork
variable {p : ℕ} [hp : Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℤ_[p] V]
namespace PI.LatMinWork
theorem _root_.solution (hp2 : p ≠ 2) (B : V → V → ℚ_[p]) (L : Submodule ℤ_[p] V) (hL : L.FG)
    (hsm : ∀ (c : ℤ_[p]) u v, B (c • u) v = (c : ℚ_[p]) * B u v)
    (hadd : ∀ u u' v, B (u + u') v = B u v + B u' v)
    (hsym : ∀ u ∈ L, ∀ v ∈ L, B u v = B v u) (hne : ∃ u ∈ L, ∃ v ∈ L, B u v ≠ 0) :
    ∃ x ∈ L, B x x ≠ 0 ∧ ∀ u ∈ L, ∃ c : ℤ_[p], B u x = (c : ℚ_[p]) * B x x := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨u0, hu0, v0, hv0, hne0⟩ := hne
  have hSL : ∀ a ∈ S, a ∈ L := fun a ha => hS ▸ Submodule.subset_span ha
  have hB0 : ∀ v, B 0 v = 0 := fun v => by simpa using hsm 0 0 v
  have hSn : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · subst h
      rw [Finset.coe_empty, Submodule.span_empty] at hS
      rw [← hS, Submodule.mem_bot] at hu0
      subst hu0
      exact absurd (hB0 v0) hne0
    · exact h
  obtain ⟨q, hq, hqmax⟩ := (S ×ˢ S).exists_max_image (fun q : V × V => ‖B q.1 q.2‖) (hSn.product hSn)
  obtain ⟨a, b⟩ := q
  have ha : a ∈ S := (Finset.mem_product.1 hq).1
  have hb : b ∈ S := (Finset.mem_product.1 hq).2
  have hmaxS : ∀ a' ∈ S, ∀ b' ∈ S, ‖B a' b'‖ ≤ ‖B a b‖ := fun a' ha' b' hb' =>
    hqmax (a', b') (Finset.mem_product.2 ⟨ha', hb'⟩)
  have hM0 : 0 ≤ ‖B a b‖ := norm_nonneg _
  have h1 : ∀ b' ∈ S, ∀ u ∈ L, ‖B u b'‖ ≤ ‖B a b‖ := fun b' hb' u hu => by
    rw [← hS] at hu
    exact bound_span B hsm hadd (↑S) b' _ hM0 (fun a' ha' => hmaxS a' ha' b' hb') u hu
  have hbound : ∀ u ∈ L, ∀ v ∈ L, ‖B u v‖ ≤ ‖B a b‖ := by
    intro u hu v hv
    rw [hsym u hu v hv]
    have h2 : ∀ b' ∈ (S : Set V), ‖B b' u‖ ≤ ‖B a b‖ := fun b' hb' => by
      rw [hsym b' (hSL b' hb') u hu]; exact h1 b' hb' u hu
    rw [← hS] at hv
    exact bound_span B hsm hadd (↑S) u _ hM0 h2 v hv
  have hMpos : 0 < ‖B a b‖ := lt_of_lt_of_le (norm_pos_iff.2 hne0) (hbound u0 hu0 v0 hv0)
  have haL := hSL a ha
  have hbL := hSL b hb
  have hx : ∃ x ∈ L, ‖B x x‖ = ‖B a b‖ := by
    by_cases haa : ‖B a a‖ = ‖B a b‖
    · exact ⟨a, haL, haa⟩
    by_cases hbb : ‖B b b‖ = ‖B a b‖
    · exact ⟨b, hbL, hbb⟩
    have habL := L.add_mem haL hbL
    refine ⟨a + b, habL, ?_⟩
    have e : B (a + b) (a + b) = 2 * B a b + (B a a + B b b) := by
      rw [hadd, hsym a haL _ habL, hsym b hbL _ habL, hadd, hadd, hsym b hbL a haL]; ring
    have hlt : ‖B a a + B b b‖ < ‖B a b‖ := lt_of_le_of_lt (show ‖B a a + B b b‖ ≤ max ‖B a a‖ ‖B b b‖ by first | exact Padic.nonarchimedean _ _ | exact IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (lt_of_le_of_ne (hbound a haL a haL) haa) (lt_of_le_of_ne (hbound b hbL b hbL) hbb))
    have h2ab : ‖2 * B a b‖ = ‖B a b‖ := by rw [norm_mul, norm_two_eq_one hp2, one_mul]
    rw [e, (show ‖2 * B a b + (B a a + B b b)‖ = max ‖2 * B a b‖ ‖B a a + B b b‖ by
      first
        | exact Padic.add_eq_max_of_ne (by rw [h2ab]; exact hlt.ne')
        | exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h2ab]; exact hlt.ne')), h2ab]
    exact max_eq_left hlt.le
  obtain ⟨x, hxL, hxn⟩ := hx
  have hxx : B x x ≠ 0 := fun h => by rw [h, norm_zero] at hxn; linarith
  refine ⟨x, hxL, hxx, fun u hu => ?_⟩
  have hc : ‖B u x / B x x‖ ≤ 1 := by
    rw [norm_div, hxn, div_le_one hMpos]; exact hbound u hu x hxL
  exact ⟨(⟨B u x / B x x, hc⟩ : {y : ℚ_[p] // ‖y‖ ≤ 1}), (div_mul_cancel₀ _ hxx).symm⟩
end PI.LatMinWork
