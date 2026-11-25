-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.w_eq_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:35:48.505898+00:00
-- url     : https://prove2.me/submissions/3f300222-8b16-42ea-af80-37e48069243c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_psi_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_primeOf_isPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_w_zero_of_not_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_mem_factors_of_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_count_zero_of_not_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_count_mul_span
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Formalism.L2.Pj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {k : Type} [Field k] [Algebra V k]
  [IsFractionRing V k]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution (ψ : E →+* k) (hψ : Function.Injective ψ) (hP0 : primeOf (V := V) ψ hψ ≠ ⊥) :
    ∃ π : 𝓞 E, π ≠ 0 ∧ ∀ (n : ℕ) (x : 𝓞 E), x ≠ 0 →
      (normalizedFactors (Ideal.span {x})).count (primeOf (V := V) ψ hψ) = n →
      vV V (ψ (x : E)) = n * vV V (ψ (π : E)) := by
  set P := primeOf (V := V) ψ hψ with hPdef
  have hPp : P.IsPrime := primeOf_isPrime ψ hψ
  have hmulv : ∀ a b : 𝓞 E, a ≠ 0 → b ≠ 0 →
      vV V (ψ ((a * b : 𝓞 E) : E)) = vV V (ψ (a : E)) + vV V (ψ (b : E)) := by
    intro a b ha hb
    have hab : ((a * b : 𝓞 E) : E) = (a : E) * (b : E) := by simp
    rw [hab, map_mul]
    unfold vV
    rw [map_mul, WithZero.log_mul ((valV V (K' := k)).ne_zero_iff.mpr (psi_ne_zero ψ hψ ha))
      ((valV V (K' := k)).ne_zero_iff.mpr (psi_ne_zero ψ hψ hb))]
    ring
  have hspan : ∀ z : 𝓞 E, z ≠ 0 → Ideal.span {z} ≠ 0 := fun z hz => by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hz
  have hP2 : P ^ 2 < P := by
    refine lt_of_le_of_ne (Ideal.pow_le_self two_ne_zero) fun heq => ?_
    have h1 : P * P = P * ⊤ := by rw [← sq, heq, Ideal.mul_top]
    exact hPp.ne_top (mul_left_cancel₀ (by rwa [Ne, Ideal.zero_eq_bot]) h1)

  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hP2
  have hπ0 : π ≠ 0 := by rintro rfl; exact hπ2 (Submodule.zero_mem _)
  have hcπ : (normalizedFactors (Ideal.span {π})).count P = 1 := by
    have h1 := mem_factors_of_mem hPp hP0 hπ0 hπP
    by_contra hne
    apply hπ2
    have h2 : Multiset.replicate 2 P ≤ normalizedFactors (Ideal.span {π}) := by
      rw [Multiset.le_iff_count]
      intro Q
      rw [Multiset.count_replicate]
      split_ifs with hQ
      · subst hQ; omega
      · exact Nat.zero_le _
    have h3 : P ^ 2 ∣ Ideal.span {π} := by
      have := Multiset.prod_dvd_prod_of_le h2
      rw [Multiset.prod_replicate] at this
      exact this.trans (UniqueFactorizationMonoid.prod_normalizedFactors (hspan π hπ0)).dvd
    exact (Ideal.le_of_dvd h3) (Ideal.mem_span_singleton_self π)

  obtain ⟨A, hA⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hπP)
  have hAP : ¬ A ≤ P := by
    intro hle
    have hdvd : P ∣ A := Ideal.dvd_iff_le.2 hle
    have h4 : P * P ∣ Ideal.span {π} := hA ▸ mul_dvd_mul_left P hdvd
    apply hπ2
    rw [sq]
    exact (Ideal.le_of_dvd h4) (Ideal.mem_span_singleton_self π)
  obtain ⟨s, hsA, hsP⟩ := Set.not_subset.1 hAP
  have hs0 : s ≠ 0 := by rintro rfl; exact hsP (Submodule.zero_mem _)
  have hws : vV V (ψ (s : E)) = 0 := w_zero_of_not_mem ψ hψ hsP
  have hcs : (normalizedFactors (Ideal.span {s})).count P = 0 := count_zero_of_not_mem hsP
  refine ⟨π, hπ0, ?_⟩
  intro n
  induction n with
  | zero =>
    intro x hx hc
    have hxP : x ∉ P := fun hxP => by
      have := mem_factors_of_mem hPp hP0 hx hxP
      omega
    simp [w_zero_of_not_mem ψ hψ hxP]
  | succ n ih =>
    intro x hx hc
    have hxP : x ∈ P := by
      by_contra hxP
      rw [count_zero_of_not_mem hxP] at hc
      omega
    have hmem : x * s ∈ Ideal.span {π} := by rw [hA]; exact Ideal.mul_mem_mul hxP hsA
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hy
      exact mul_ne_zero hx hs0 hy.symm
    have hcy : (normalizedFactors (Ideal.span {y})).count P = n := by
      have h1 := count_mul_span (P := P) hy0 hπ0
      rw [hy, count_mul_span hx hs0, hc, hcs, hcπ] at h1
      omega
    have h2 := hmulv y π hy0 hπ0
    rw [hy, hmulv x s hx hs0, hws, ih y hy0 hcy] at h2
    push_cast
    linarith
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
