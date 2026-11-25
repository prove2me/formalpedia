-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.exists_rename_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:36.432168+00:00
-- url     : https://prove2.me/submissions/d396763e-5e90-43c5-8fd5-31d78d7682d9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValAlgebraMapEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {K : Type} [Field K] {σ : Type} (p : Ideal (MvPolynomial σ K))
    (hp : p.IsPrime ∧ p.height = 1) :
    ∃ e0 : σ, ∀ q : MvPolynomial {e // e ≠ e0} K, q ≠ 0 → rename Subtype.val q ∉ p := by
  classical
  haveI : UniqueFactorizationMonoid (MvPolynomial σ K) := MvPolynomial.uniqueFactorizationMonoid σ
  obtain ⟨hprime, hh⟩ := hp
  have hne : p ≠ ⊥ := by
    intro h
    rw [h, Ideal.height_bot] at hh
    exact zero_ne_one hh
  obtain ⟨g, hgp, hgprime⟩ := hprime.exists_mem_prime_of_ne_bot hne
  have hg0 : g ≠ 0 := hgprime.ne_zero
  haveI hPprime : (Ideal.span {g}).IsPrime := (Ideal.span_singleton_prime hg0).mpr hgprime
  have hPle : Ideal.span {g} ≤ p := (Ideal.span_singleton_le_iff_mem p).mpr hgp
  have hPeq : Ideal.span {g} = p := by
    by_contra hneq
    have hlt : Ideal.span {g} < p := lt_of_le_of_ne hPle hneq
    haveI : p.FiniteHeight := ⟨Or.inr (by rw [hh]; exact ENat.one_ne_top)⟩
    have h1 : (Ideal.span {g}).height < p.height := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
    rw [hh] at h1
    have hPh : (Ideal.span {g}).height = 0 := ENat.lt_one_iff_eq_zero.mp h1
    haveI : (Ideal.span {g}).FiniteHeight := ⟨Or.inr (by rw [hPh]; exact ENat.zero_ne_top)⟩
    have hbot : (⊥ : Ideal (MvPolynomial σ K)) < Ideal.span {g} := by
      rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
      exact hg0
    have h2 : (⊥ : Ideal (MvPolynomial σ K)).height < (Ideal.span {g}).height :=
      Ideal.height_strict_mono_of_isPrime_of_isPrime hbot
    rw [hPh] at h2
    exact absurd h2 not_lt_zero'
  have hvars : g.vars.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have htd : g.totalDegree = 0 := by
      apply Nat.eq_zero_of_le_zero
      unfold MvPolynomial.totalDegree
      apply Finset.sup_le
      intro d hd
      have hd0 : d = 0 := by
        ext i
        by_contra hi
        have hiv : i ∈ g.vars := (MvPolynomial.mem_vars i).mpr ⟨d, hd, Finsupp.mem_support_iff.mpr hi⟩
        rw [hemp] at hiv
        simp at hiv
      simp [hd0]
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at htd
    have ha : MvPolynomial.coeff 0 g ≠ 0 := by
      intro ha0
      apply hg0
      rw [htd, ha0, map_zero]
    apply hgprime.not_unit
    rw [htd]
    exact (isUnit_iff_ne_zero.mpr ha).map MvPolynomial.C
  obtain ⟨e0, he0⟩ := hvars
  refine ⟨e0, fun q hq hmem => ?_⟩
  rw [← hPeq, Ideal.mem_span_singleton] at hmem
  obtain ⟨h, hh2⟩ := hmem
  have hr0 : rename Subtype.val q ≠ 0 := by
    intro h0
    apply hq
    exact MvPolynomial.rename_injective _ Subtype.val_injective (by rw [h0, map_zero])
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hh2
    exact hr0 hh2
  have hdeg : MvPolynomial.degreeOf e0 (rename Subtype.val q) ≠ 0 := by
    rw [hh2, MvPolynomial.degreeOf_mul_eq hg0 hh0]
    have h3 := (MvPolynomial.mem_vars_iff_degreeOf_ne_zero).mp he0
    omega
  have hin : e0 ∈ (rename Subtype.val q).vars := MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr hdeg
  obtain ⟨i, -, hi⟩ := MvPolynomial.mem_vars_rename _ _ hin
  exact i.2 hi
end ReciprocityTheory.ChartRestriction.G.T0
