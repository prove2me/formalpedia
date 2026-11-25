-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagArith_proof_a9ca35fc7a0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:20:42.548193+00:00
-- url     : https://prove2.me/submissions/5ce5d539-59ce-4412-948c-314af9ff06c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagArith
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_X_inr_notMem_ebd94c5eb49d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_algebraMap_int_injective_bbfc0045ba62

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace FlagArith
theorem _root_.solution (hMH : FlagMultiHomog.Statement) (hTr : FlagConeTrdeg.Statement)
    (hDim : IntDomainDim.Statement) : FlagArith.Statement := by
  intro K _ ι _ N1 t n P d c m B hP hc hB
  have := hP.2.1.1

  have hHor : IsHorizontal (flagIdeal P B) := by
    have h := hP.2.2.1
    rw [← imageZ_flagIdeal P B] at h
    refine Eq.trans (Ideal.ext fun a => ?_) h
    simp only [Ideal.mem_comap, imageZ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C]
  have hprime : (flagIdeal P B).IsPrime := RingHom.ker_isPrime _
  refine ⟨⟨Sum.inl hP.1.some⟩, ⟨hprime, hMH K ι N1 t n P c m B hP.2.1.1 hP.2.1.2.1 hc.1 hB, ?_⟩, hHor, ?_⟩
  ·
    rintro (k | j)
    · obtain ⟨i, hi⟩ := hP.2.1.2.2 k
      refine ⟨i, fun h => hi ?_⟩
      rw [← imageZ_flagIdeal P B]
      show rename inlV (X ⟨k, i⟩) ∈ flagIdeal P B
      rwa [rename_X]
    · obtain ⟨S, hS⟩ := exists_X_inr_notMem P B hB.1 j
      exact ⟨S, hS⟩
  ·
    have dimP := hDim (MRing ι ⧸ P) (algebraMap_int_injective P hP.2.2.1)
    have dimF := hDim (MRing (FlagBundleBlocks ι N1 n) ⧸ flagIdeal P B) (algebraMap_int_injective _ hHor)
    rw [hTr K ι N1 n P B hP.2.1.1 hP.2.2.1 hB.1] at dimF
    rw [hP.2.2.2] at dimP
    rw [dimF]
    have hK : 0 < Fintype.card K := Fintype.card_pos_iff.2 hP.1
    have h1 : ((d + Fintype.card K : ℕ) : ℕ∞) = (Algebra.trdeg ℤ (MRing ι ⧸ P)).toENat + 1 := by
      exact_mod_cast dimP
    simp only [map_add, map_natCast, Fintype.card_sum, Fintype.card_fin]
    generalize (Algebra.trdeg ℤ (MRing ι ⧸ P)).toENat = s at h1 ⊢
    induction s using ENat.recTopCoe with
    | top => simp at h1
    | coe s =>
      norm_cast at h1 ⊢
      rw [show s + (flagDim n + (n - 1)) + 1 = flagDim n + d + (Fintype.card K + (n - 1)) by omega]
end FlagArith
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
