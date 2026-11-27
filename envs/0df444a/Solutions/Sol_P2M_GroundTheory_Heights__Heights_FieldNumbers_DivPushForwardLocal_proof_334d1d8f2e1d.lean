-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_DivPushForwardLocal_proof_334d1d8f2e1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:55:48.133302+00:00
-- url     : https://prove2.me/submissions/04fe311c-0d5d-4052-af57-f24695513395

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivCycleMinimal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeLocalLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocalRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFiniteRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLength
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KrullDimQuotientEqOneIffEqBot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivPushForwardLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_form_not_mem_3b065c8c97a1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_div_mem_degZeroLoc_250927a4bb6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_contractPrime_7e3d9fd91401
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_dimOneTorsionFreeFormula


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace DivPushForwardLocal
theorem _root_.solution (h1 : DivCycleMinimal.Statement.{u})
    (h2 : ConeLocalLength.Statement.{u}) (h3 : DegZeroLocalRing.Statement.{u})
    (h4 : SemilocalFiniteRank.Statement.{u}) (h5 : SemilocalLength.Statement.{u}) :
    DivPushForwardLocal.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hdim hdimP c a ha haP W hW hWd M hM1 hM0
  have := hP'.isPrime
  have hP := isMultiProjPrime_contractPrime j ι' hP'
  by_cases hPW : contractPrime j P' ⊔ Ideal.span {a} ≤ W
  · have := hW.isPrime
    have hPle : contractPrime j P' ≤ W := le_trans le_sup_left hPW
    obtain ⟨h, hh, hhW⟩ := exists_form_not_mem hW c
    let α : degZeroLoc (contractPrime j P') {W} := ⟨_, div_mem_degZeroLoc _ _ ha hh
      (fun hm => hhW (hPle hm)) (fun W₁ h₁ => (Set.mem_singleton_iff.mp h₁) ▸ hhW)⟩
    have hα0 : α ≠ 0 := by
      intro h0
      have h0' := congrArg Subtype.val h0
      rcases div_eq_zero_iff.mp h0' with h' | h' <;>
        rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h'
      · exact haP h'
      · exact hhW (hPle h')
    obtain ⟨⟨hNo, hLo⟩, hdA⟩ := h3 F K _ _ hP W hW hPle
    obtain ⟨hfin, htf, hrk⟩ := h4 F K K' j ι' P' hP' n hdim hdimP W hW hWd hPle
    have key := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula _ (degZeroLoc P' (fibrePrimes j P' W)) α
      (hdA n hdimP hWd) hα0
    obtain ⟨N, hN, hMN⟩ := h5 F K K' j ι' P' hP' n hdim hdimP c a h ha hh haP W hW hWd hPle hhW
      M hM1 hM0 α rfl
    obtain ⟨hmin, hfinm⟩ := h1 F K _ _ hP.isPrime n hdimP a haP W hW.isPrime hWd hPW
    have hcone := h2 F K _ _ hP W hW hPle c a h ha hh hhW α rfl
    have hdc : divCycle (contractPrime j P') a W =
        ((multAt (contractPrime j P' ⊔ Ideal.span {a}) W).toNat : ℤ) := by
      unfold divCycle
      rw [dif_pos ⟨hmin, hW.relevant⟩]
    rw [hMN, hdc]
    rw [hN, hrk, ← hcone] at key
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfinm
    rw [← hm] at key ⊢
    have hNm : N = relDeg j P' * m := by exact_mod_cast key
    rw [hNm, ENat.toNat_natCast]
    push_cast
    rfl
  · have hR : divCycle (contractPrime j P') a W = 0 := by
      unfold divCycle
      rw [dif_neg]
      rintro ⟨h, -⟩
      exact hPW h.1.2
    rw [hR, mul_zero]
    unfold cycEval
    refine finsum_eq_zero_of_forall_eq_zero fun W' => ?_
    by_cases hD : divCycle P' (rename (blockIncl j ι') a) W' = 0
    · rw [hD, zero_mul]
    · refine mul_eq_zero_of_right _ (hM0 W' fun hc => hPW ?_)
      unfold divCycle at hD
      split_ifs at hD with hm
      · rw [← hc]
        refine sup_le (Ideal.comap_mono (le_trans le_sup_left hm.1.1.2)) ?_
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hm.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
      · exact absurd rfl hD
end DivPushForwardLocal
end GroundTheory.Heights₂.Heights.FieldNumbers
