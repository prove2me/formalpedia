-- Prove2me | solution 1 for Representation.span_range_eq_top_of_span_range_eq_top_of_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4c473be1-6fa9-5f03-a1c1-6302b6fd80c2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_span_range_eq_top_of_span_range_eq_top_of_trace_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SpanTraceAsm

open Module

section Nondeg

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem eq_zero_of_forall_trace_mul_eq_zero (a : Module.End k V)
    (h : ∀ y : Module.End k V, LinearMap.trace k V (y * a) = 0) : a = 0 := by
  by_contra ha
  obtain ⟨v, hv⟩ : ∃ v, a v ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ha (LinearMap.ext hall)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hv
  have hy : (LinearMap.smulRight f v) * a = LinearMap.smulRight (f.comp a) v := by
    ext w
    simp [LinearMap.smulRight_apply]
  have := h (LinearMap.smulRight f v)
  rw [hy, LinearMap.trace_smulRight, LinearMap.comp_apply, hf] at this
  exact one_ne_zero this

end Nondeg

section Main

variable {k : Type} [Field k] {G : Type} [Monoid G]
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
  [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]

def jointSpan (ρ₁ : G →* Module.End k V₁) (ρ₂ : G →* Module.End k V₂) :
    Submodule k (Module.End k V₁ × Module.End k V₂) :=
  Submodule.span k (Set.range fun g => (ρ₁ g, ρ₂ g))

theorem mul_mem_jointSpan (ρ₁ : G →* Module.End k V₁) (ρ₂ : G →* Module.End k V₂)
    {x y : Module.End k V₁ × Module.End k V₂} (hx : x ∈ jointSpan ρ₁ ρ₂)
    (hy : y ∈ jointSpan ρ₁ ρ₂) : x * y ∈ jointSpan ρ₁ ρ₂ := by
  unfold jointSpan at *
  open scoped Pointwise in
  have hsub : (Set.range fun g => (ρ₁ g, ρ₂ g)) * (Set.range fun g => (ρ₁ g, ρ₂ g)) ⊆
      Set.range fun g => (ρ₁ g, ρ₂ g) := by
    rintro _ ⟨_, ⟨g, rfl⟩, _, ⟨h, rfl⟩, rfl⟩
    exact ⟨g * h, by simp [Prod.mk_mul_mk]⟩
  have := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at this
  exact Submodule.span_mono hsub this

theorem map_fst_jointSpan (ρ₁ : G →* Module.End k V₁) (ρ₂ : G →* Module.End k V₂) :
    (jointSpan ρ₁ ρ₂).map (LinearMap.fst k _ _) = Submodule.span k (Set.range ⇑ρ₁) := by
  unfold jointSpan
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem map_snd_jointSpan (ρ₁ : G →* Module.End k V₁) (ρ₂ : G →* Module.End k V₂) :
    (jointSpan ρ₁ ρ₂).map (LinearMap.snd k _ _) = Submodule.span k (Set.range ⇑ρ₂) := by
  unfold jointSpan
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem trace_fst_eq_trace_snd (ρ₁ : G →* Module.End k V₁) (ρ₂ : G →* Module.End k V₂)
    (htr : ∀ g : G, LinearMap.trace k V₁ (ρ₁ g) = LinearMap.trace k V₂ (ρ₂ g))
    {x : Module.End k V₁ × Module.End k V₂} (hx : x ∈ jointSpan ρ₁ ρ₂) :
    LinearMap.trace k V₁ x.1 = LinearMap.trace k V₂ x.2 := by
  unfold jointSpan at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact htr g
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem span_eq_top (ρ₁ : G →* Module.End k V₁) (ρ₂ : G →* Module.End k V₂)
    (hrank : Module.finrank k V₁ = Module.finrank k V₂)
    (hspan₁ : Submodule.span k (Set.range ⇑ρ₁) = ⊤)
    (htr : ∀ g : G, LinearMap.trace k V₁ (ρ₁ g) = LinearMap.trace k V₂ (ρ₂ g)) :
    Submodule.span k (Set.range ⇑ρ₂) = ⊤ := by
  set B := jointSpan ρ₁ ρ₂ with hB

  have hinj : ∀ x ∈ B, x.2 = 0 → x = 0 := by
    intro x hx hx2
    have hx1 : x.1 = 0 := by
      refine eq_zero_of_forall_trace_mul_eq_zero x.1 fun y => ?_

      have hy : y ∈ (B.map (LinearMap.fst k _ _)) := by
        rw [hB, map_fst_jointSpan, hspan₁]; exact Submodule.mem_top
      obtain ⟨z, hz, rfl⟩ := hy
      have hzx : z * x ∈ B := mul_mem_jointSpan ρ₁ ρ₂ hz hx
      have := trace_fst_eq_trace_snd ρ₁ ρ₂ htr hzx
      rw [Prod.fst_mul, Prod.snd_mul, hx2, mul_zero, map_zero] at this
      exact this
    exact Prod.ext hx1 hx2

  have hle₁ : Module.finrank k (Module.End k V₁) ≤ Module.finrank k B := by
    have h1 : Module.finrank k (B.map (LinearMap.fst k _ _)) ≤ Module.finrank k B :=
      Submodule.finrank_map_le _ _
    rw [hB, map_fst_jointSpan, hspan₁, finrank_top] at h1
    exact h1
  have hle₂ : Module.finrank k B ≤ Module.finrank k (Submodule.span k (Set.range ⇑ρ₂)) := by
    have hker : LinearMap.ker ((LinearMap.snd k _ _).domRestrict B) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      rintro ⟨x, hx⟩ h
      exact Subtype.ext (hinj x hx h)
    have h1 := LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hker)
    rw [LinearMap.range_domRestrict] at h1
    rw [← h1, hB, map_snd_jointSpan]
  have hEnd : Module.finrank k (Module.End k V₁) = Module.finrank k (Module.End k V₂) := by
    rw [Module.finrank_linearMap, Module.finrank_linearMap, hrank]
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le _)
  calc Module.finrank k (Module.End k V₂) = Module.finrank k (Module.End k V₁) := hEnd.symm
    _ ≤ Module.finrank k B := hle₁
    _ ≤ _ := hle₂

end Main

end SpanTraceAsm

theorem solution
    {k : Type} [Field k] {G : Type} [Monoid G]
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    (ρ₁ : G →* Module.End k V₁) (ρ₂ : G →* Module.End k V₂)
    (hrank : Module.finrank k V₁ = Module.finrank k V₂)
    (hspan₁ : Submodule.span k (Set.range ⇑ρ₁) = ⊤)
    (htr : ∀ g : G, LinearMap.trace k V₁ (ρ₁ g) = LinearMap.trace k V₂ (ρ₂ g)) :
    Submodule.span k (Set.range ⇑ρ₂) = ⊤ :=
  SpanTraceAsm.span_eq_top ρ₁ ρ₂ hrank hspan₁ htr

end S_Representation_span_range_eq_top_of_span_range_eq_top_of_trace_eq
end P2MW
export P2MW.S_Representation_span_range_eq_top_of_span_range_eq_top_of_trace_eq (solution)
