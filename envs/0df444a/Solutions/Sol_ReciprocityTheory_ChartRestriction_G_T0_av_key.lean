-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.av_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:36:15.118135+00:00
-- url     : https://prove2.me/submissions/e52fc434-1d74-4577-9d42-025d53906748

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AvPrimeDimOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_av_no_two_chain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {S : Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsLocalRing S] (g : S)
    (hg : g ≠ 0) (H : ∀ Q : Ideal S, Q.IsPrime → Q ≠ ⊥ → g ∈ Q) (Q : Ideal S) (hQ : Q.IsPrime)
    (hQ0 : Q ≠ ⊥) : Q.IsMaximal := by
  classical
  by_contra hQm
  set m := IsLocalRing.maximalIdeal S with hm_def
  have hQlt : Q < m := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ.ne_top)
    (fun h => hQm (h ▸ IsLocalRing.maximalIdeal.isMaximal S))
  haveI : (Ideal.span {g}).IsPrincipal := ⟨⟨g, rfl⟩⟩
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing S (Ideal.span {g})

  have hmin : ∀ P ∈ (Ideal.span {g}).minimalPrimes, P.IsPrime ∧ P ≠ ⊥ ∧ P.height ≤ 1 := by
    intro P hP
    refine ⟨hP.1.1, ?_, ?_⟩
    · intro h
      apply hg
      have := hP.1.2 (Ideal.mem_span_singleton_self g)
      rw [h] at this
      exact (Submodule.mem_bot S).mp this
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP

  have hbelow : ∀ P' : Ideal S, P'.IsPrime → P' ≠ ⊥ →
      ∃ P ∈ (Ideal.span {g}).minimalPrimes, P ≤ P' := by
    intro P' hP' h0
    exact Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).mpr (H P' hP' h0))

  have hm_not : ∀ P ∈ (Ideal.span {g}).minimalPrimes, ¬ m ≤ P := by
    intro P hP hmP
    obtain ⟨P0, hP0, hP0Q⟩ := hbelow Q hQ hQ0
    obtain ⟨hPp, -, hPh⟩ := hmin P hP
    obtain ⟨hP0p, hP00, -⟩ := hmin P0 hP0
    haveI := hPp
    haveI := hP0p
    exact av_no_two_chain (bot_lt_iff_ne_bot.mpr hP00)
      (lt_of_le_of_lt hP0Q (lt_of_lt_of_le hQlt hmP)) hPh

  obtain ⟨x, hxm, hxP⟩ : ∃ x ∈ m, ∀ P ∈ (Ideal.span {g}).minimalPrimes, x ∉ P := by
    by_contra hcon
    push_neg at hcon
    have hsub : (m : Set S) ⊆ ⋃ P ∈ (hfin.toFinset : Set (Ideal S)), ((id P : Ideal S) : Set S) := by
      intro y hy
      obtain ⟨P, hP, hyP⟩ := hcon y hy
      exact Set.mem_iUnion₂.mpr ⟨P, by simpa using hP, hyP⟩
    obtain ⟨P, hP, hle⟩ := (Ideal.subset_union_prime (f := id) ⊥ ⊥
      (fun P hP _ _ => (hmin P (by simpa using hP)).1)).mp hsub
    exact hm_not P (by simpa using hP) hle
  obtain ⟨P0, hP0, -⟩ := hbelow Q hQ hQ0
  have hx0 : x ≠ 0 := by
    intro h
    apply hxP P0 hP0
    rw [h]
    exact Submodule.zero_mem _
  obtain ⟨P', hP', -⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem m).mpr hxm)
  haveI := hP'.1.1
  have hxP' : x ∈ P' := hP'.1.2 (Ideal.mem_span_singleton_self x)
  have hP'0 : P' ≠ ⊥ := by
    intro h
    rw [h] at hxP'
    exact hx0 ((Submodule.mem_bot S).mp hxP')
  haveI : (Ideal.span {x}).IsPrincipal := ⟨⟨x, rfl⟩⟩
  have hP'h : P'.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P' hP'
  obtain ⟨P, hP, hPP'⟩ := hbelow P' hP'.1.1 hP'0
  obtain ⟨hPp, hP00, -⟩ := hmin P hP
  rcases lt_or_eq_of_le hPP' with hlt | heq
  · haveI := hPp
    exact av_no_two_chain (bot_lt_iff_ne_bot.mpr hP00) hlt hP'h
  · apply hxP P hP
    rw [heq]
    exact hxP'
end ReciprocityTheory.ChartRestriction.G.T0
