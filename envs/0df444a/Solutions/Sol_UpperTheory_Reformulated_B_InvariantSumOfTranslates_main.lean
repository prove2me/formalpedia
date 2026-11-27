-- Prove2me | solution 1 for UpperTheory.Reformulated.B.InvariantSumOfTranslates.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:33:12.445849+00:00
-- url     : https://prove2.me/submissions/1eac8057-b048-4ba2-bfa7-7106fbfe685f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DeRhamEllipticIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.InvariantSumOfTranslates
theorem _root_.solution :
    ∀ {K S : Type} [inst : Group K] [inst_1 : TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
      [inst_4 : AddCommGroup S] [inst_5 : _root_.Module ℂ S] (ω : K →* Module.End ℂ S) (f₀ : S),
      (∃ U ∈ nhds (1 : K), ∀ k ∈ U, ((ω : K → Module.End ℂ S) k : S → S) f₀ = f₀) →
        ∃ (m : ℕ) (k : Fin (m + (1 : ℕ)) → K),
          ∀ (g : K),
            ((ω : K → Module.End ℂ S) g : S → S) (∑ i : Fin (m + (1 : ℕ)), ((ω : K → Module.End ℂ S) (k i) : S → S) f₀) =
              ∑ i : Fin (m + (1 : ℕ)), ((ω : K → Module.End ℂ S) (k i) : S → S) f₀ := by
  intro K S _ _ _ _ _ _ ω f₀ h
  obtain ⟨U, hU, hfix⟩ := h
  have hmul : ∀ (a b : K) (v : S), ω (a * b) v = ω a (ω b v) := by
    intro a b v
    rw [map_mul, Module.End.mul_apply]

  let H : Subgroup K :=
    { carrier := {k | ω k f₀ = f₀}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [hmul, hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : ω a⁻¹ (ω a f₀) = f₀ := by
          rw [← hmul]; simp
        rwa [ha] at h1 }
  have hmem : ∀ k, k ∈ H ↔ ω k f₀ = f₀ := fun k => Iff.rfl
  have hopen : IsOpen (H : Set K) :=
    H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hU (fun k hk => hfix k hk))
  haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hopen
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _

  let F : K ⧸ H → S := fun q => ω q.out f₀
  have hF : ∀ (g : K) (q : K ⧸ H), ω g (F q) = F (g • q) := by
    intro g q
    have hq : ((g * q.out : K) : K ⧸ H) = g • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hq' : (((g • q).out : K) : K ⧸ H) = ((g * q.out : K) : K ⧸ H) := by
      rw [hq, QuotientGroup.out_eq']
    have hh : ((g • q).out)⁻¹ * (g * q.out) ∈ H := QuotientGroup.eq.mp hq'
    have h2 : g * q.out = (g • q).out * (((g • q).out)⁻¹ * (g * q.out)) := by group
    change ω g (ω q.out f₀) = ω (g • q).out f₀
    rw [← hmul, h2, hmul, (hmem _).mp hh]
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card (K ⧸ H) = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e : Fin (m + 1) ≃ K ⧸ H := (Fintype.equivFinOfCardEq hm).symm
  refine ⟨m, fun i => (e i).out, fun g => ?_⟩
  have hsum : ∑ i : Fin (m + 1), ω (e i).out f₀ = ∑ q, F q := Equiv.sum_comp e F
  rw [hsum, map_sum]
  simp_rw [hF]
  exact Equiv.sum_comp (MulAction.toPerm g) F
end UpperTheory.Reformulated.B.InvariantSumOfTranslates
