-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Yt3.exists_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:34:35.309518+00:00
-- url     : https://prove2.me/submissions/96d03c7f-97e8-4b5d-a195-b551cc5de13b

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Yt3.mem_conj {G : Type} [Group G] {K : Subgroup G} {g y : G} :
    y ∈ Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) g)) K ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Yt3
theorem _root_.solution :
    ∀ {G : Type} [inst : Group G] {K : Subgroup G} {g : G},
      (Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) g)) K).relIndex K ≠ (0 : ℕ) →
        ∃ (R : Finset G),
          (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * g * k₂) ∧
            ∀ (x : G), (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) → ∃! γ : G, γ ∈ R ∧ γ⁻¹ * x ∈ K := by
  intro G _ K g h
  classical
  set H : Subgroup K :=
    (Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) g)) K).subgroupOf K with hH
  have hfin : Finite (K ⧸ H) := Nat.finite_of_card_ne_zero h
  letI : Fintype (K ⧸ H) := Fintype.ofFinite _
  have key : ∀ (a b : K) (k : G), k ∈ K →
      ((((a : G) * g)⁻¹ * ((b : G) * g * k) ∈ K) ↔ (a : K ⧸ H) = (b : K ⧸ H)) := by
    intro a b k hk
    rw [QuotientGroup.eq, hH, Subgroup.mem_subgroupOf, UpperTheory.Reformulated.B.Yt3.mem_conj,
      ← mul_assoc, K.mul_mem_cancel_right hk]
    simp [mul_assoc]
  refine ⟨Finset.univ.image (fun q : K ⧸ H => ((q.out : K) : G) * g), ?_, ?_⟩
  · intro γ hγ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hγ
    exact ⟨_, (q.out).2, 1, K.one_mem, (mul_one _).symm⟩
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    refine ⟨(((((⟨k₁, hk₁⟩ : K) : K ⧸ H)).out : K) : G) * g,
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · exact (key _ ⟨k₁, hk₁⟩ k₂ hk₂).2 (QuotientGroup.out_eq' _)
    · rintro γ ⟨hγ, hx⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hγ
      have := (key _ ⟨k₁, hk₁⟩ k₂ hk₂).1 hx
      rw [QuotientGroup.out_eq'] at this
      rw [this]
end UpperTheory.Reformulated.B.Yt3
