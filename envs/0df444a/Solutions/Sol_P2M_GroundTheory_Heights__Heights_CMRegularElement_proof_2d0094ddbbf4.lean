-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CMRegularElement_proof_2d0094ddbbf4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:25.286566+00:00
-- url     : https://prove2.me/submissions/8413b4f4-a60c-4020-85a7-e329ab2c3429

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CMDepthAssoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMRegularElement
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_nonZeroDivisors_of_not_mem_minimalPrimes_5ade1a33ecea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_isRegular_quotSMulTop_35a6944ac9d9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing RingTheory.Sequence CategoryTheory Abelian Limits Pointwise
universe u
namespace GroundTheory.Heights₂.Heights
namespace CMRegularElement
theorem _root_.solution : CMRegularElement.Statement.{u} := by
  intro B _ _ y hym hy
  have hnzd := mem_nonZeroDivisors_of_not_mem_minimalPrimes hy
  refine ⟨hnzd, ?_⟩
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hyreg : IsSMulRegular B y := Module.Flat.isSMulRegular_of_nonZeroDivisors hnzd
  obtain ⟨rs', hlen, hm', hreg'⟩ := exists_isRegular_quotSMulTop hm hreg hyreg hym
  set I := Ideal.span {y} with hIdef
  have hI : I ≠ ⊤ := Ideal.span_singleton_ne_top ((mem_maximalIdeal _).mp hym)
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (B ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hloc : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I (by
    rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hym)
  have hsub : (y • (⊤ : Submodule B B)) = I := by
    rw [hIdef, ← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop y B ≃ₗ[B] B ⧸ I := Submodule.quotEquivOfEq _ _ hsub
  have hw : IsWeaklyRegular (B ⧸ I) (rs'.map (algebraMap B (B ⧸ I))) :=
    (isWeaklyRegular_map_algebraMap_iff (S := B ⧸ I) (M := B ⧸ I) rs').mpr
      ((e.isWeaklyRegular_congr rs').mp hreg'.toIsWeaklyRegular)
  have hdimq := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hnzd hym
  refine { exists_isWeaklyRegular := ⟨rs'.map (algebraMap B (B ⧸ I)), ?_, hw, ?_⟩ }
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact map_nonunit (Ideal.Quotient.mk I) s (hm' s hs)
  · rw [List.length_map, hlen]
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ I) := ringKrullDim_nonneg_of_nontrivial
    rw [hdim] at hdimq
    obtain ⟨d, hd⟩ : ∃ d : ℕ∞, ringKrullDim (B ⧸ I) = d :=
      (WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot WithBot.zero_ne_bot h0)).imp fun _ h => h.symm
    rw [hd] at hdimq ⊢
    have h2 : d + 1 = (rs.length : ℕ∞) := by exact_mod_cast hdimq
    induction d using ENat.recTopCoe with
    | top => simp at h2
    | coe k =>
      norm_cast at h2 ⊢
      rw [show k = rs.length - 1 by omega]
end CMRegularElement
end GroundTheory.Heights₂.Heights
