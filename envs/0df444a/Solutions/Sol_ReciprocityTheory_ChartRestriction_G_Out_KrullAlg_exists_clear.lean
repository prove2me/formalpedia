-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.exists_clear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:26:46.037861+00:00
-- url     : https://prove2.me/submissions/cf014216-7f29-4e90-ad94-5218048e4aa0

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.Integer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_MemRangeOfForallHeightOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_KrullAlg_exists_assoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]
namespace ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
theorem _root_.solution [IsNoetherianRing A] [IsIntegrallyClosed A] {ι : Type*} [Finite ι]
    (x : ι → K) (hx : ∃ i, x i ∉ (algebraMap A K).range) :
    ∃ P : Ideal A, P.IsPrime ∧ P.height = 1 ∧ ∃ b ∈ P,
      (∀ i, algebraMap A K b * x i ∈ (algebraMap A K).range) ∧
      ∃ i, ∃ u ∉ P, algebraMap A K u = algebraMap A K b * x i := by
  classical
  obtain ⟨d, P, hP, hPmem, i0, hi0⟩ := exists_assoc x hx
  obtain ⟨b0, hb0⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A)
    (fun i => algebraMap A K d * x i)
  have hb0P : (b0 : A) ∈ P := (hPmem _).2 fun i => by
    obtain ⟨y, hy⟩ := hb0 i
    exact ⟨y, by rw [hy, Algebra.smul_def]⟩
  have hb0ne : (b0 : A) ≠ 0 := nonZeroDivisors.coe_ne_zero b0
  have hPne : P ≠ ⊥ := fun h => hb0ne (by rw [h] at hb0P; exact (Submodule.mem_bot A).1 hb0P)
  have hex : ∃ p ∈ P, ∃ u : A, algebraMap A K u = algebraMap A K p * (algebraMap A K d * x i0) ∧
      u ∉ P := by
    by_contra hne
    push_neg at hne
    apply hi0
    let N : Submodule A K := Submodule.map (Algebra.linearMap A K) P
    have hNfg : N.FG := (IsNoetherian.noetherian P).map (Algebra.linearMap A K)
    have hNne : N ≠ ⊥ := by
      intro h
      have hm : algebraMap A K b0 ∈ N := (Submodule.mem_map).2 ⟨(b0 : A), hb0P, rfl⟩
      rw [h, Submodule.mem_bot] at hm
      exact hb0ne ((IsFractionRing.injective A K) (hm.trans (map_zero _).symm))
    have hint : IsIntegral A (algebraMap A K d * x i0) := by
      refine isIntegral_of_smul_mem_submodule N hNne hNfg _ fun n hn => ?_
      obtain ⟨a, haP, rfl⟩ := (Submodule.mem_map).1 hn
      obtain ⟨u, hu⟩ := (hPmem a).1 haP i0
      have huP := hne a haP u hu
      refine (Submodule.mem_map).2 ⟨u, huP, ?_⟩
      simp only [Algebra.linearMap_apply, smul_eq_mul]
      rw [hu]
      ring
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    exact ⟨a, ha⟩
  obtain ⟨p, hpP, u, hu, huP⟩ := hex
  refine ⟨P, hP, ?_, p * d, P.mul_mem_right d hpP, fun j => ?_, i0, u, huP, ?_⟩
  · haveI : Submodule.IsPrincipal (Ideal.span {p}) := ⟨⟨p, rfl⟩⟩
    have hmin : P ∈ (Ideal.span {p}).minimalPrimes := by
      refine ⟨⟨hP, (Ideal.span_singleton_le_iff_mem P).2 hpP⟩, fun Q hQ hQP => ?_⟩
      intro q hq
      obtain ⟨v, hv⟩ := (hPmem q).1 hq i0
      have e : q * u = p * v := IsFractionRing.injective A K (by rw [map_mul, map_mul, hu, hv]; ring)
      have h1 : q * u ∈ Q := e ▸ Q.mul_mem_right v ((Ideal.span_singleton_le_iff_mem Q).1 hQ.2)
      rcases hQ.1.mem_or_mem h1 with h2 | h2
      · exact h2
      · exact absurd (hQP h2) huP
    have h1 : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hmin
    have h0 : P.height ≠ 0 := fun h => hPne (Ideal.height_eq_zero_iff_eq_bot.1 h)
    exact le_antisymm h1 (ENat.one_le_iff_ne_zero.2 h0)
  · obtain ⟨v, hv⟩ := (hPmem p).1 hpP j
    exact ⟨v, by rw [hv, map_mul]; ring⟩
  · rw [hu, map_mul]
    ring
end ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
