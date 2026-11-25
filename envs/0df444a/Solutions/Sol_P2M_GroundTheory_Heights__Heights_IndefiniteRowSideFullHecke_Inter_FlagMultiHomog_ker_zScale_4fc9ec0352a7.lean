-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_ker_zScale_4fc9ec0352a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:05:42.132801+00:00
-- url     : https://prove2.me/submissions/1def7141-c7c8-4134-8bbc-b681e706950f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_eval__genPt_365ba5726aa3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveComplexPoint_eval__smul_homog_35af9e8e8d54


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {N1 n : ℕ}
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
theorem _root_.solution (P : Ideal (MRing ι)) [P.IsPrime] (hP : IsMultiHomogIdeal P) (n : ℕ) :
    RingHom.ker (zScale P n) = P := by
  refine le_antisymm (fun f hf => ?_) ?_
  · have h1 : (eval fun _ => (1 : TRing P n)).comp (zScale P n) =
        C.comp ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) :=
      MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => by simp [zScale, genPt]
    have h2 := RingHom.congr_fun h1 f
    rw [RingHom.comp_apply, RingHom.mem_ker.1 hf, map_zero] at h2
    rw [← ker_algebraMap_comp_mk P, RingHom.mem_ker]
    exact C_injective _ _ (h2.symm.trans C_0.symm)
  · obtain ⟨S, hS, hSP⟩ := hP
    refine hSP.le.trans (Ideal.span_le.2 fun s hs => ?_)
    obtain ⟨a, ha⟩ := hS s hs
    have hsP : s ∈ P := by rw [hSP]; exact Ideal.subset_span hs
    rw [SetLike.mem_coe, RingHom.mem_ker, zScale, coe_eval₂Hom]
    have h3 := HeightsSet.CurveComplexPoint.eval₂_smul_homog s a ha
      (fun k => (X (Sum.inl k) : LRing P n)) (fun p => ((C : TRing P n →+* LRing P n).comp C) (genPt P p))
    have h4 := eval₂_genPt (S := LRing P n) P ((C : TRing P n →+* LRing P n).comp C) s
    simp only [RingHom.comp_apply] at h3 h4
    rw [show (fun p : Σ k, ι k => (C (C (genPt P p)) * X (Sum.inl p.1) : LRing P n)) =
        fun p => X (Sum.inl p.1) * C (C (genPt P p)) from funext fun _ => mul_comm _ _, h3, h4,
      Ideal.Quotient.eq_zero_iff_mem.2 hsP, map_zero, map_zero, map_zero, mul_zero]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
