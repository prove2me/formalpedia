-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qk18.polyIn_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:25:18.338788+00:00
-- url     : https://prove2.me/submissions/10c2a26d-7eaa-45e1-a114-a509cd1f205a

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PolyInMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qk18
theorem _root_.solution :
    ∀ {R : Type} [inst : Ring R] [inst_1 : Algebra ℂ R] {f g : ℂ → R} {d₁ d₂ : ℕ},
      UpperTheory.Reformulated.B.Qk18.PolyIn f d₁ →
        UpperTheory.Reformulated.B.Qk18.PolyIn g d₂ → UpperTheory.Reformulated.B.Qk18.PolyIn (fun (t : ℂ) ↦ f t * g t) (d₁ + d₂) := by
  intro R _ _ f g d₁ d₂ hf hg
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨fun n => ∑ i ∈ Finset.range (d₁ + 1), ∑ j ∈ Finset.range (d₂ + 1),
    if i + j = n then a i * b j else 0, fun s => ?_⟩
  show f s * g s = _
  rw [ha s, hb s, Finset.sum_mul_sum]
  simp only [Finset.smul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hmem : i + j ∈ Finset.range (d₁ + d₂ + 1) := by
    rw [Finset.mem_range] at hi hj ⊢
    omega
  rw [Finset.sum_eq_single_of_mem (i + j) hmem]
  · rw [if_pos rfl, smul_mul_smul_comm, pow_add]
  · intro k _ hk
    rw [if_neg (Ne.symm hk), smul_zero]
end UpperTheory.Reformulated.B.Qk18
