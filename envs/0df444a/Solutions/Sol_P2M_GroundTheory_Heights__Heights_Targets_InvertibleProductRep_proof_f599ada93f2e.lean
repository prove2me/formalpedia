-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_InvertibleProductRep_proof_f599ada93f2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:09:33.170004+00:00
-- url     : https://prove2.me/submissions/82e5675a-aa60-47d8-a8d8-1e80ecb0ff14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PInvertibleProductRep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleProductRep_mem_of_local_baee30457324

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
namespace InvertibleProductRep
theorem _root_.solution : InvertibleProductRep.Statement := by
  intro Ω _ B M N P η _ g h β δ β' δ' I J hβ hδ hβ' hδ' hM hN hP hloc x
  have hβΩ : (β : Ω) ≠ 0 := fun h0 => hβ (Subtype.ext (by rw [h0]; rfl))
  have hβ'Ω : (β' : Ω) ≠ 0 := fun h0 => hβ' (Subtype.ext (by rw [h0]; rfl))
  have hne : ((β * β' : B) : Ω) ≠ 0 := by push_cast; exact mul_ne_zero hβΩ hβ'Ω
  have notin : ∀ (m : Ideal B), m.IsMaximal → ∀ a b c : B, a ∉ m → b ∉ m → c ∉ m → a * b * c ∉ m := by
    intro m hm a b c ha hb hc h0
    rcases hm.isPrime.mem_or_mem h0 with h1 | h1
    · rcases hm.isPrime.mem_or_mem h1 with h2 | h2
      · exact ha h2
      · exact hb h2
    · exact hc h1
  constructor
  · intro hx
    let Y : AddSubgroup Ω :=
      { carrier := {w | ∃ y ∈ I * J, ((β * β' : B) : Ω) * w = ((δ * δ' : B) : Ω) * (y : Ω)}
        add_mem' := by
          rintro a c ⟨y₁, hy₁, e₁⟩ ⟨y₂, hy₂, e₂⟩
          refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
          push_cast at e₁ e₂ ⊢
          linear_combination e₁ + e₂
        zero_mem' := ⟨0, zero_mem _, by simp⟩
        neg_mem' := by
          rintro a ⟨y, hy, e⟩
          refine ⟨-y, neg_mem hy, ?_⟩
          push_cast at e ⊢
          linear_combination -e }
    have hYst : ∀ b ∈ B, ∀ z ∈ Y, b * z ∈ Y := by
      rintro b hb z ⟨y, hy, e⟩
      refine ⟨⟨b, hb⟩ * y, (I * J).mul_mem_left _ hy, ?_⟩
      push_cast at e ⊢
      linear_combination b * e
    have key : x ∈ Y := by
      refine InvertibleProductRep.mem_of_local B Y hYst x fun m hm => ?_
      obtain ⟨i, ⟨⟨b₁, hb₁, hgM⟩, -⟩, ⟨⟨b₂, hb₂, hhN⟩, -⟩, ⟨-, hPz⟩⟩ := hloc m hm
      obtain ⟨b, c, hb, e⟩ := hPz x hx
      obtain ⟨u, hu, eu⟩ := (hM _).1 hgM
      obtain ⟨v, hv, ev⟩ := (hN _).1 hhN
      refine ⟨b₁ * b₂ * b, notin m hm _ _ _ hb₁ hb₂ hb, c * (u * v),
        (I * J).mul_mem_left _ (Ideal.mul_mem_mul hu hv), ?_⟩
      push_cast at e eu ev ⊢
      linear_combination ((β : Ω) * β' * b₁ * b₂) * e + ((c : Ω) * β' * b₂ * h i) * eu +
        ((c : Ω) * δ * u) * ev
    obtain ⟨y, hy, e⟩ := key
    exact ⟨y, hy, by push_cast at e ⊢; linear_combination e⟩
  · rintro ⟨y, hy, e⟩
    have claim : ∀ r ∈ I * J, ((δ * δ' : B) : Ω) * (r : Ω) / ((β * β' : B) : Ω) ∈ P := by
      intro r hr
      refine Submodule.mul_induction_on
        (C := fun r : B => ((δ * δ' : B) : Ω) * (r : Ω) / ((β * β' : B) : Ω) ∈ P) hr ?_ ?_
      · intro u hu v hv
        have hp : (δ : Ω) * u / β ∈ M := (hM _).2 ⟨u, hu, by field_simp⟩
        have hq : (δ' : Ω) * v / β' ∈ N := (hN _).2 ⟨v, hv, by field_simp⟩
        have hpq : ((δ : Ω) * u / β) * ((δ' : Ω) * v / β') ∈ P := by
          refine InvertibleProductRep.mem_of_local B P hP _ fun m hm => ?_
          obtain ⟨i, ⟨-, hMz⟩, ⟨-, hNz⟩, ⟨⟨b'', hb'', hgh⟩, -⟩⟩ := hloc m hm
          obtain ⟨b, c, hb, e₁⟩ := hMz _ hp
          obtain ⟨b', c', hb', e₂⟩ := hNz _ hq
          refine ⟨b * b' * b'', notin m hm _ _ _ hb hb' hb'', ?_⟩
          have eq : ((b * b' * b'' : B) : Ω) * (((δ : Ω) * u / β) * ((δ' : Ω) * v / β')) =
              ((c * c' : B) : Ω) * ((b'' : Ω) * (g i * h i)) := by
            push_cast
            linear_combination ((b' : Ω) * b'' * ((δ' : Ω) * v / β')) * e₁ + ((c : Ω) * b'' * g i) * e₂
          rw [eq]
          exact hP _ (c * c').2 _ hgh
        have : ((δ * δ' : B) : Ω) * ((u * v : B) : Ω) / ((β * β' : B) : Ω) =
            ((δ : Ω) * u / β) * ((δ' : Ω) * v / β') := by
          push_cast
          field_simp
        rw [this]
        exact hpq
      · intro a c ha hc
        have : ((δ * δ' : B) : Ω) * ((a + c : B) : Ω) / ((β * β' : B) : Ω) =
            ((δ * δ' : B) : Ω) * (a : Ω) / ((β * β' : B) : Ω) +
              ((δ * δ' : B) : Ω) * (c : Ω) / ((β * β' : B) : Ω) := by
          push_cast
          ring
        rw [this]
        exact P.add_mem ha hc
    have hx : x = ((δ * δ' : B) : Ω) * (y : Ω) / ((β * β' : B) : Ω) := by
      rw [eq_div_iff hne]
      push_cast at e ⊢
      linear_combination e
    rw [hx]
    exact claim y hy
end InvertibleProductRep
end GroundTheory.Heights₂.Heights.Targets
