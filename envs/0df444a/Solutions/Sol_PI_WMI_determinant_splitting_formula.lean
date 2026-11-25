-- Prove2me | solution 1 for PI.WMI.determinant_splitting_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:07.160624+00:00
-- url     : https://prove2.me/submissions/e0dc6bc9-329a-46cf-af74-f4866d43eeda

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_DetSplit
import Theorems.Thm_PI_WMI_detSplit_fullMinor
import Theorems.Thm_PI_WMI_detSplit_prodMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_standardMonomialSpanDomain
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
namespace PI.WMI
theorem _root_.solution : DetSplit := by
  intro N ν c hν f hf
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨f, ?_, ?_⟩
    · have : (fun a : Fin 0 => ν a + c) = ν := funext fun a => a.elim0
      rwa [this] at hf
    · simp [detPoly]
  · classical
    have h0 := hν hN
    let T : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
      (Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν).map (LinearMap.mulLeft ℂ (detPoly N ^ c))
    suffices hT : f ∈ T by
      obtain ⟨f', hf', hff⟩ := hT
      exact ⟨f', hf', hff.symm⟩
    rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ N N] at hf
    refine (Submodule.span_le.2 ?_) hf
    rintro _ ⟨K, sz, hsz, I, hshape, rfl⟩
    let A : Finset (Fin K) := Finset.univ.filter fun k => sz k = N
    have hcard : ∀ t : Fin N, (Finset.univ.filter fun k => t.val < sz k).card =
        (Aᶜ.filter fun k => t.val < sz k).card + A.card := by
      intro t
      rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_sum_compl A, add_comm,
        Finset.card_eq_sum_ones A]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have : sz k = N := by simpa [A] using hk
      simp [this, t.isLt]
    have hA : A.card = c := by
      have h1 := congrFun hshape ⟨N - 1, by omega⟩
      have h2 := hcard ⟨N - 1, by omega⟩
      have h3 : (Aᶜ.filter fun k => N - 1 < sz k) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro k hk hlt
        have hkA : ¬ sz k = N := by simpa [A] using hk
        have := hsz k
        omega
      simp only [shapeDeg] at h1
      rw [h0] at h1
      rw [h3] at h2
      simp at h2
      omega
    have hrest : (fun t : Fin N => (Aᶜ.filter fun k => t.val < sz k).card) = ν := by
      funext t
      have h1 := congrFun hshape t
      simp only [shapeDeg] at h1
      have := hcard t
      omega
    have hmem := detSplit_prodMem sz hsz I Aᶜ
    rw [hrest] at hmem
    have hfac : ∀ k : Fin K, ∃ e : ℂ, k ∈ A → initMinor ℂ (I k) (hsz k) = C e * detPoly N := by
      intro k
      by_cases hk : k ∈ A
      · obtain ⟨e, he⟩ := detSplit_fullMinor (sz k) (I k) (hsz k) (by simpa [A] using hk)
        exact ⟨e, fun _ => he⟩
      · exact ⟨0, fun h => absurd h hk⟩
    choose e he using hfac
    refine ⟨C (∏ k ∈ A, e k) * ∏ k ∈ Aᶜ, initMinor ℂ (I k) (hsz k), ?_, ?_⟩
    · rw [C_mul']
      exact Submodule.smul_mem _ _ hmem
    · simp only [LinearMap.mulLeft_apply]
      unfold bideterminant
      rw [← Finset.prod_mul_prod_compl A, Finset.prod_congr rfl fun k hk => he k hk,
        Finset.prod_mul_distrib, Finset.prod_const, hA, map_prod]
      ring
end PI.WMI
