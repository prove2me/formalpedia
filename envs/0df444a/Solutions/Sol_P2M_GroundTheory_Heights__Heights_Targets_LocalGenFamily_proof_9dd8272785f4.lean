-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_LocalGenFamily_proof_9dd8272785f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:08:33.391124+00:00
-- url     : https://prove2.me/submissions/c5971bf6-bf4e-4ff0-9d38-28c85eed3cf1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLocalGenFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
namespace GroundTheory.Heights₂.Heights.Targets
namespace LocalGenFamily
theorem _root_.solution : LocalGenFamily.Statement := by
  intro Ω _ B X η _ f hfin hX hf0 hc hloc
  have : Module.Finite ℤ B := hfin
  have : IsNoetherianRing B := IsNoetherianRing.of_finite ℤ B

  let K : η → Ideal B := fun i =>
    { carrier := {t : B | (t : Ω) * f i ∈ X}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Subring.coe_add, add_mul] at ha hb ⊢
        exact X.add_mem ha hb
      zero_mem' := by simp only [Set.mem_ofPred_eq, ZeroMemClass.coe_zero, zero_mul]; exact X.zero_mem
      smul_mem' := fun c t ht => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, Subring.coe_mul, mul_assoc] at ht ⊢
        exact hX _ c.2 _ ht }
  have hK : ∀ i, ∀ t : B, t ∈ K i ↔ (t : Ω) * f i ∈ X := fun _ _ => Iff.rfl
  have hfg : ∀ i, ∃ T : Finset B, Ideal.span (T : Set B) = K i := fun i => IsNoetherian.noetherian (K i)
  choose T hT using hfg
  refine ⟨?_, Σ i : η, {t : B // t ∈ T i}, inferInstance, fun j => (j.2.1 : Ω) * f j.1, ?_, ?_, ?_⟩
  ·
    obtain ⟨m, hm⟩ := Ideal.exists_maximal B
    obtain ⟨i, ⟨b, hbm, hbX⟩, -⟩ := hloc m hm
    have hb : (b : Ω) ≠ 0 := by
      intro h
      exact hbm (by rw [show b = 0 from Subtype.ext h]; exact m.zero_mem)
    intro hbot
    rw [hbot, AddSubgroup.mem_bot] at hbX
    exact mul_ne_zero hb (hf0 i) hbX
  · rintro ⟨i, t, ht⟩
    rw [← hK, ← hT i]
    exact Ideal.subset_span ht
  · rintro ⟨i, t, -⟩
    obtain ⟨c, hcB, hc0, hcf⟩ := hc i
    refine ⟨c, hcB, hc0, ?_⟩
    rw [mul_left_comm]
    exact B.mul_mem t.2 hcf
  · intro m hm
    obtain ⟨i, ⟨b, hbm, hbX⟩, hall⟩ := hloc m hm
    have : ∃ t ∈ T i, t ∉ m := by
      by_contra hno
      push Not at hno
      have hle : K i ≤ m := by
        rw [← hT i, Ideal.span_le]
        exact fun t ht => hno t ht
      exact hbm (hle ((hK i b).2 hbX))
    obtain ⟨t, htT, htm⟩ := this
    refine ⟨⟨i, t, htT⟩, fun z hz => ?_⟩
    obtain ⟨b', c', hb'm, hbz⟩ := hall z hz
    refine ⟨t * b', c', fun h => ?_, ?_⟩
    · rcases hm.isPrime.mem_or_mem h with h | h
      · exact htm h
      · exact hb'm h
    · simp only [Subring.coe_mul]
      calc (t : Ω) * b' * z = t * (b' * z) := by ring
        _ = t * (c' * f i) := by rw [hbz]
        _ = c' * (t * f i) := by ring
end LocalGenFamily
end GroundTheory.Heights₂.Heights.Targets
