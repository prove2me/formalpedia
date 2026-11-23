-- Prove2me | solution 1 for UpperTheory.Reformulated.B.TwistedKernelFixed.eq_zero_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:13.097645+00:00
-- url     : https://prove2.me/submissions/5f15cf09-4b4b-41c6-ad14-fb98c29080d3

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.TwistedKernelFixed.sum_shift {H V : Type} [Group H] [AddCommGroup V] [_root_.Module ℂ V]
    (ρ : H →* (V →ₗ[ℂ] V)) (K : Subgroup H) [K.Normal] [Fintype (H ⧸ K)] (u : V)
    (hu : ∀ k ∈ K, ρ k u = u) (n : H) :
    ∑ q : H ⧸ K, ρ q.out (ρ n u) = ∑ q : H ⧸ K, ρ q.out u := by
  refine Fintype.sum_equiv (Equiv.mulRight (n : H ⧸ K)) _ _ fun q => ?_
  have h1 : ((q.out * n : H) : H ⧸ K) = (((q * (n : H ⧸ K)).out : H) : H ⧸ K) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq']
  have h2 := hu _ (QuotientGroup.eq.mp h1)
  have h3 : (q * (n : H ⧸ K)).out = q.out * n * ((q.out * n)⁻¹ * (q * (n : H ⧸ K)).out) := by
    rw [mul_inv_cancel_left]
  rw [Equiv.coe_mulRight, h3, map_mul, Module.End.mul_apply, h2, map_mul, Module.End.mul_apply]
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.TwistedKernelFixed
theorem _root_.solution :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] {π : Representation ℂ G V}
      [inst_3 : TopologicalSpace G] [IsTopologicalGroup G],
      UpperTheory.Reformulated.B.TwistedKernelFixed.IsSmooth π →
        ∀ {H : Subgroup G},
          IsCompact (↑H : Set G) →
            ∀ {v : V}, v ∈ UpperTheory.Reformulated.B.TwistedKernelFixed.fixed π H → v ∈ UpperTheory.Reformulated.B.TwistedKernelFixed.twKer π H (1 : ↥H →* ℂˣ) → v = (0 : V) := by
  intro G V _ _ _ π _ _ hs H hH v hv hw
  classical
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have key : ∀ w ∈ UpperTheory.Reformulated.B.TwistedKernelFixed.twKer π H (1 : ↥H →* ℂˣ),
      ∃ K : Subgroup H, K.FiniteIndex ∧ ∀ (L : Subgroup H) [L.Normal] [Fintype (H ⧸ L)], L ≤ K →
        ∑ q : H ⧸ L, π (q.out : H) w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, u, rfl⟩ := hx
      let K : Subgroup H :=
        { carrier := {h | π (h : G) u = u}
          mul_mem' := fun {a b} ha hb => by
            have ha' : π (a : G) u = u := ha
            have hb' : π (b : G) u = u := hb
            show π ((a : G) * b) u = u
            rw [map_mul, Module.End.mul_apply, hb', ha']
          one_mem' := by
            show π (1 : G) u = u
            rw [map_one, Module.End.one_apply]
          inv_mem' := fun {a} ha => by
            have ha' : π (a : G) u = u := ha
            show π ((a : G)⁻¹) u = u
            conv_lhs => rw [← ha']
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
      have hK : IsOpen (K : Set H) := (hs u).preimage continuous_subtype_val
      haveI := Subgroup.quotient_finite_of_isOpen K hK
      refine ⟨K, Subgroup.finiteIndex_of_finite_quotient, fun L _ _ hL => ?_⟩
      have := UpperTheory.Reformulated.B.TwistedKernelFixed.sum_shift (π.comp H.subtype) L u (fun k hk => hL hk) n
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr this
    | zero => exact ⟨⊤, inferInstance, fun L _ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨K₁, h₁, hx⟩ := hx
      obtain ⟨K₂, h₂, hy⟩ := hy
      refine ⟨K₁ ⊓ K₂, inferInstance, fun L _ _ hL => ?_⟩
      simp only [map_add, Finset.sum_add_distrib]
      rw [hx L (hL.trans inf_le_left), hy L (hL.trans inf_le_right), add_zero]
    | smul c x _ hx =>
      obtain ⟨K, h, hx⟩ := hx
      refine ⟨K, h, fun L _ _ hL => ?_⟩
      simp only [map_smul]
      rw [← Finset.smul_sum, hx L hL, smul_zero]
  obtain ⟨K, hK, h⟩ := key v hw
  haveI : Fintype (H ⧸ K.normalCore) := Fintype.ofFinite _
  have h0 := h K.normalCore K.normalCore_le
  have hv' : ∀ g : H, π (g : G) v = v := fun g => by
    have := hv g
    simpa using this
  simp only [hv', Finset.sum_const, Finset.card_univ] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h0
  exact (smul_eq_zero.mp h0).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
end UpperTheory.Reformulated.B.TwistedKernelFixed
