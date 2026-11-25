-- Prove2me | solution 1 for UpperTheory.Reformulated.B.LinearTermOfSubstitution.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:39:57.514872+00:00
-- url     : https://prove2.me/submissions/225da2a6-65c3-4d96-8e1f-544950b13df2

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegreeOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace DegreeOneCoeffSubstitution
open MvPowerSeries Finsupp
private lemma deg_one {σ : Type} [DecidableEq σ] (d : σ →₀ ℕ) (h : d.degree = 1) :
    ∃ s, d = Finsupp.single s 1 := by
  have hd : d ≠ 0 := by rintro rfl; simp at h
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hd
  refine ⟨s, ?_⟩
  have hsum : d s + ∑ i ∈ d.support.erase s, d i = 1 := by
    rw [Finset.add_sum_erase _ _ hs, ← degree_apply, h]
  have hs0 : d s ≠ 0 := Finsupp.mem_support_iff.mp hs
  have hds : d s = 1 := by omega
  have hrest : ∑ i ∈ d.support.erase s, d i = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at hrest
  ext i
  by_cases his : i = s
  · subst his; simp [hds]
  · rw [Finsupp.single_apply, if_neg (Ne.symm his)]
    by_cases hi : i ∈ d.support
    · exact hrest i (Finset.mem_erase.mpr ⟨his, hi⟩)
    · exact Finsupp.notMem_support_iff.mp hi
end DegreeOneCoeffSubstitution
end

set_option autoImplicit false

open MvPowerSeries Finsupp
namespace UpperTheory.Reformulated.B.LinearTermOfSubstitution
theorem _root_.solution :
    ∀ {S : Type}
    [inst : CommRing S] {σ τ : Type} [inst_1 : Fintype σ] [DecidableEq σ] [DecidableEq τ] (a : σ → MvPowerSeries τ S),
    (∀ (s : σ), (MvPowerSeries.constantCoeff : MvPowerSeries τ S → S) (a s) = (0 : S)) →
      ∀ (f : MvPowerSeries σ S) (t : τ),
        (MvPowerSeries.coeff fun₀ | t => (1 : ℕ) : MvPowerSeries τ S → S) (MvPowerSeries.subst a f) =
          ∑ s : σ,
            (MvPowerSeries.coeff fun₀ | s => (1 : ℕ) : MvPowerSeries σ S → S) f *
              (MvPowerSeries.coeff fun₀ | t => (1 : ℕ) : MvPowerSeries τ S → S) (a s) := by
  intro S _ σ τ _ _ _ a ha f t
  have hS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [coeff_subst hS]
  have key : ∀ d : σ →₀ ℕ, d ∉ Finset.univ.image (fun s => Finsupp.single s 1) →
      coeff (Finsupp.single t 1) (d.prod fun s e => a s ^ e) = 0 := by
    intro d hd
    by_cases h0 : d = 0
    · subst h0
      simp [coeff_one]
    have h1 : d.degree ≠ 1 := by
      intro h
      obtain ⟨s, rfl⟩ := DegreeOneCoeffSubstitution.deg_one d h
      exact hd (by simp)
    have h2 : 2 ≤ d.degree := by
      have : d.degree ≠ 0 := fun h => h0 ((degree_eq_zero_iff d).mp h)
      omega
    unfold Finsupp.prod
    apply coeff_of_lt_order
    rw [Finsupp.degree_single]
    refine lt_of_lt_of_le ?_ (le_order_prod _ _)
    calc ((1 : ℕ) : ℕ∞) < 2 := by norm_num
      _ ≤ ((d.degree : ℕ) : ℕ∞) := by exact_mod_cast h2
      _ = ∑ i ∈ d.support, ((d i : ℕ) : ℕ∞) := by rw [degree_apply]; push_cast; rfl
      _ ≤ ∑ i ∈ d.support, (a i ^ d i).order :=
          Finset.sum_le_sum fun i _ => le_order_pow_of_constantCoeff_eq_zero _ (ha i)
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun s => Finsupp.single s 1)) ?_]
  · rw [Finset.sum_image (fun x _ y _ h => Finsupp.single_left_injective one_ne_zero h)]
    apply Finset.sum_congr rfl
    intro s _
    simp [Finsupp.prod_single_index, smul_eq_mul]
  · intro d hd
    by_contra h
    apply hd
    simp only
    rw [key d (by simpa using h), smul_zero]
end UpperTheory.Reformulated.B.LinearTermOfSubstitution
