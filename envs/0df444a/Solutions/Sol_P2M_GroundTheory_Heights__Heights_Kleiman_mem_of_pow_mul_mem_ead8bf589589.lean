-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_pow_mul_mem_ead8bf589589
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:35:15.587153+00:00
-- url     : https://prove2.me/submissions/95bbb022-e9e6-4bc1-ab8b-668af194e31e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleTwistGenerated

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
open scoped Pointwise
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {B : Subalgebra k Ω} {n : ℕ} {a b : Fin n → Ω} {z : Ω}
    (ha : ∀ i, a i ∈ B) (hb : ∀ i, b i ∈ B) (hab : ∑ i, a i * b i = 1)
    (hz : ∀ i, ∃ E : ℕ, b i ^ E * z ∈ B) : z ∈ B := by
  choose E hE using hz
  have htop : Ideal.span (Set.range fun i => (⟨b i, hb i⟩ : B)) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun i => ⟨a i, ha i⟩, Subtype.ext ?_⟩
    simpa using hab
  have h2 := Ideal.span_pow_eq_top _ htop (∑ j, E j)
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at h2
  obtain ⟨c, hc⟩ := h2
  have hcoe : ∑ i, (c i : Ω) * b i ^ (∑ j, E j) = 1 := by
    have h5 := congrArg (fun y : B => (y : Ω)) hc
    simpa using h5
  have hsum : z = ∑ i, (c i : Ω) * (b i ^ (∑ j, E j) * z) := by
    calc z = (∑ i, (c i : Ω) * b i ^ (∑ j, E j)) * z := by rw [hcoe, one_mul]
      _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  refine sum_mem fun i _ => mul_mem (c i).2 ?_
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i) : E i ≤ ∑ j, E j)
  have h6 : b i ^ (∑ j, E j) * z = b i ^ d * (b i ^ E i * z) := by rw [hd]; ring
  rw [h6]
  exact mul_mem (pow_mem (hb i) _) (hE i)
end GroundTheory.Heights₂.Heights.Kleiman
