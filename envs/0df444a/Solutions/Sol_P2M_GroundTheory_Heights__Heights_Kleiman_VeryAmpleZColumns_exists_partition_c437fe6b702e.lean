-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_exists_partition_c437fe6b702e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:30.394018+00:00
-- url     : https://prove2.me/submissions/81e21006-1b99-4424-aca2-d71d2cb6aabd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZColumnsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZColumns

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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ}
variable {G : SubSystem S x E} {H : SubSystem S x Ω} {h : Fin (r + 1) → Ω} {I : Chart x}
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
theorem _root_.solution {H : LineBundle S x} (hV : IsVeryAmpleBy H.toSubSystem h) (I : Chart x)
    (m : ℕ) : ∃ w : Fin (r + 1) → Ω, ∑ k, w k * h k ^ m = 1 ∧
      ∀ k, ∀ q ∈ H.sub I ^ m, w k * q ∈ chartRing S x I := by
  have hH : ∀ j, h j ∈ H.sub I := fun j => (Submodule.mem_iInf _).mp (hV.mem_secs j) I
  obtain ⟨Q', hQ'⟩ := H.invertible I
  have h1 : (1 : Ω) ∈ H.sub I * Q' := by
    rw [hQ']; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have key : ∀ z ∈ H.sub I * Q', ∃ u : Fin (r + 1) → Ω, (∀ k, u k ∈ Q') ∧ ∑ k, h k * u k = z := by
    intro z hz
    refine Submodule.mul_induction_on hz (fun c hc q hq => ?_) ?_
    · rw [← hV.generates I] at hc
      obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hc
      refine ⟨fun k => f k • q, fun k => Submodule.smul_mem _ _ hq, ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [chartRing_smul_def]; ring
    · rintro a b ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
      exact ⟨u + u', fun k => add_mem (hu k) (hu' k), by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]⟩
  obtain ⟨u, hu, hsum⟩ := key 1 h1
  have hinv : ∀ k, ∀ q ∈ H.sub I, u k * q ∈ chartRing S x I := fun k q hq => by
    have := Submodule.mul_mem_mul hq (hu k)
    rw [hQ', Submodule.mem_one] at this
    obtain ⟨y, hy⟩ := this
    rw [mul_comm, ← hy]; exact y.2
  have hinvm : ∀ k, ∀ (m : ℕ), ∀ q ∈ H.sub I ^ m, u k ^ m * q ∈ chartRing S x I := by
    intro k m
    induction m with
    | zero =>
      intro q hq
      rw [pow_zero, Submodule.mem_one] at hq
      obtain ⟨y, rfl⟩ := hq
      rw [pow_zero, one_mul]; exact y.2
    | succ m ih =>
      intro q hq
      rw [pow_succ] at hq
      refine Submodule.mul_induction_on hq (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · rw [show u k ^ (m + 1) * (a * b) = (u k ^ m * a) * (u k * b) by ring]
        exact mul_mem (ih a ha) (hinv k b hb)
      · rw [mul_add]; exact add_mem ha hb
  let b : Fin (r + 1) → chartRing S x I := fun k => ⟨h k * u k, by
    rw [mul_comm]; exact hinv k _ (hH k)⟩
  have htop : Ideal.span (Set.range b) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun _ => 1, Subtype.ext ?_⟩
    simp only [one_mul, b, AddSubmonoidClass.coe_finsetSum, OneMemClass.coe_one]
    exact hsum
  have htop' := Ideal.span_pow_eq_top _ htop m
  rw [← Set.range_comp] at htop'
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (htop' ▸ Submodule.mem_top : (1 : chartRing S x I) ∈ Ideal.span (Set.range ((fun y => y ^ m) ∘ b)))
  refine ⟨fun k => (c k : Ω) * u k ^ m, ?_, fun k q hq => ?_⟩
  · have := congrArg (fun y : chartRing S x I => (y : Ω)) hc
    simp only [Function.comp_apply, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
      SubmonoidClass.coe_pow, OneMemClass.coe_one, b] at this
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rw [mul_assoc]; exact mul_mem (c k).2 (hinvm k m q hq)
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
