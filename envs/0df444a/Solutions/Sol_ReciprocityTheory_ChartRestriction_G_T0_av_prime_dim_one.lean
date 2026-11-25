-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.av_prime_dim_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:03.950871+00:00
-- url     : https://prove2.me/submissions/835a7ac7-bb88-4e79-ac13-214e0727208c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AvPrimeDimOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_av_key

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
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    (hdim : 1 ≤ ringKrullDim R) (h : R) (hh : h ≠ 0) :
    ∃ p : Ideal R, p.IsPrime ∧ ringKrullDim (R ⧸ p) = 1 ∧ h ∉ p := by
  classical
  set m := IsLocalRing.maximalIdeal R with hm_def
  have hm0 : m ≠ ⊥ := by
    intro e
    have hF : IsField R := (IsLocalRing.isField_iff_maximalIdeal_eq).mpr e
    rw [ringKrullDim_eq_zero_of_isField hF] at hdim
    exact absurd hdim (by norm_num)

  obtain ⟨p, ⟨hpP, hhp, hpm⟩, hpmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) {q : Ideal R | q.IsPrime ∧ h ∉ q ∧ q ≠ m}
    ⟨⊥, Ideal.bot_prime, fun h' => hh ((Submodule.mem_bot R).mp h'), fun e => hm0 e.symm⟩
  haveI := hpP
  refine ⟨p, hpP, ?_, hhp⟩
  have hplt : p < m := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hpP.ne_top) hpm
  obtain ⟨y, hym, hyp⟩ := SetLike.exists_of_lt hplt
  set f := Ideal.Quotient.mk p with hf_def
  haveI : IsLocalRing (R ⧸ p) := IsLocalRing.of_surjective' f Ideal.Quotient.mk_surjective
  have hfz : ∀ a : R, f a = 0 ↔ a ∈ p := fun a => Ideal.Quotient.eq_zero_iff_mem
  have hg0 : f (h * y) ≠ 0 := by
    rw [Ne, hfz]
    intro hm'
    rcases hpP.mem_or_mem hm' with h1 | h1
    · exact hhp h1
    · exact hyp h1

  have hall : ∀ Q : Ideal (R ⧸ p), Q.IsPrime → Q ≠ ⊥ → f (h * y) ∈ Q := by
    intro Q hQ hQ0
    haveI := hQ
    have hq : (Q.comap f).IsPrime := inferInstance
    have hpq : p < Q.comap f := by
      refine lt_of_le_of_ne (fun a ha => ?_) (fun e => hQ0 ?_)
      · show f a ∈ Q
        rw [(hfz a).mpr ha]
        exact Q.zero_mem
      · rw [eq_bot_iff]
        intro z hz
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
        have ha : a ∈ Q.comap f := hz
        rw [← e] at ha
        exact (Submodule.mem_bot _).mpr ((hfz a).mpr ha)
    show h * y ∈ Q.comap f
    by_cases hhq : h ∈ Q.comap f
    · exact Ideal.mul_mem_right _ _ hhq
    · have hqm : Q.comap f = m := by
        by_contra hne
        exact hpmax _ ⟨hq, hhq, hne⟩ hpq
      rw [hqm]
      exact Ideal.mul_mem_left _ _ hym
  have hmax : ∀ Q : Ideal (R ⧸ p), Q.IsPrime → Q ≠ ⊥ → Q.IsMaximal :=
    fun Q hQ hQ0 => av_key (f (h * y)) hg0 hall Q hQ hQ0
  apply le_antisymm
  · unfold ringKrullDim Order.krullDim
    refine iSup_le fun s => ?_
    by_contra hlt
    have h2 : 2 ≤ s.length := by
      by_contra h2
      apply hlt
      have : s.length ≤ 1 := by omega
      exact_mod_cast this
    have a01 : s ⟨0, by omega⟩ < s ⟨1, by omega⟩ := s.strictMono (Fin.mk_lt_mk.mpr (by norm_num))
    have a12 : s ⟨1, by omega⟩ < s ⟨2, by omega⟩ := s.strictMono (Fin.mk_lt_mk.mpr (by norm_num))
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at a01 a12
    have hne : (s ⟨1, by omega⟩).asIdeal ≠ ⊥ := fun e => not_lt_bot (e ▸ a01)
    have hM := hmax _ (s ⟨1, by omega⟩).isPrime hne
    exact a12.ne (hM.eq_of_le (s ⟨2, by omega⟩).isPrime.ne_top a12.le)
  · haveI hMp : (m.map f).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hplt.le)
    have hlt : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum (R ⧸ p)) < ⟨m.map f, hMp⟩ := by
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
      refine bot_lt_iff_ne_bot.mpr fun e => ?_
      have hy : f y ∈ m.map f := Ideal.mem_map_of_mem f hym
      have e' : m.map f = ⊥ := e
      rw [e'] at hy
      exact hyp ((hfz y).mp ((Submodule.mem_bot _).mp hy))
    have e1 := Order.height_add_one_le hlt
    calc (1 : WithBot ℕ∞) ≤ ((Order.height (⟨m.map f, hMp⟩ : PrimeSpectrum (R ⧸ p)) : ℕ∞) :
          WithBot ℕ∞) := by exact_mod_cast (le_add_self.trans e1)
      _ ≤ ringKrullDim (R ⧸ p) := Order.height_le_krullDim _
end ReciprocityTheory.ChartRestriction.G.T0
