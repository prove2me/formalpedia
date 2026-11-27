-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermProjectionFunctionForm_proof_b03528fdb50a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:57:22.751898+00:00
-- url     : https://prove2.me/submissions/ec86a408-3a25-4109-afcb-92fd5263c7db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermProjectionFunctionForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermProjectionFunctionForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermProjectionFunctionForm_germPull_toGerm_aad33b7ed9c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermProjectionFunctionForm_coordGerm_eq_toGerm_b996a416353a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermProjectionFunctionForm_isGermCombination_of_mem_2c61ded304bf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermPrimitivePresentation_toGerm_mem_iff_9b3ec135511e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter PrimeGermPrimitivePresentation
noncomputable section
open GermProjectionFunctionForm
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GermProjectionFunctionForm
theorem _root_.solution : GermProjectionFunctionForm.Statement := by
  classical
  intro σ _ w k p d A hp ⟨hinj, hgen, hint⟩
  let Z : σ → anFun w := fun i => mkA (fun z : σ → ℂ => z i)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)
  have hZ : ∀ i, coordGerm w i = toGerm w (Z i) := coordGerm_eq_toGerm w
  have hpull : ∀ φ : holGerms (A w), germPull A (A.analyticAt w) rfl φ = toGerm w (compA A w (rep φ)) := by
    intro φ
    conv_lhs => rw [← toGerm_rep φ]
    exact germPull_toGerm A w (rep φ)
  refine ⟨?_, ?_, ?_⟩
  · intro h hh hcomb
    have hmem := (toGerm_mem_iff hp (compA A w (mkA h hh))).2 hcomb
    rw [← germPull_toGerm] at hmem
    have h0 := congrArg Subtype.val (hinj _ hmem)
    exact Germ.coe_eq.1 (h0.trans (Germ.coe_zero (l := 𝓝 (A w)) (M := ℂ)).symm)
  · intro i
    obtain ⟨q, hq, hqP⟩ := hint i
    refine ⟨q.natDegree, fun j => (rep (q.coeff j)).1, fun j => (rep (q.coeff j)).2, ?_⟩
    have key : q.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w i) =
        toGerm w (Z i ^ q.natDegree + ∑ j : Fin q.natDegree, compA A w (rep (q.coeff j)) * Z i ^ (j : ℕ)) := by
      conv_lhs => rw [hq.as_sum]
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_finsetSum,
        Polynomial.eval₂_mul, Polynomial.eval₂_C, map_add, map_pow, map_sum, map_mul, hpull, hZ]
      rw [Fin.sum_univ_eq_sum_range (fun j => toGerm w (compA A w (rep (q.coeff j))) * toGerm w (Z i) ^ j)]
    rw [key] at hqP
    refine isGermCombination_of_mem p _ hqP _ fun z => ?_
    simp [Z, mkA, compA, Finset.sum_apply]
  · intro g hg
    obtain ⟨F, hF⟩ := hgen (toGerm w (mkA g hg))
    let e := Finsupp.equivFunOnFinite (α := σ) (M := ℕ)
    refine ⟨F.support.image e, fun m => (rep (F.coeff (e.symm m))).1, fun m _ => (rep (F.coeff (e.symm m))).2, ?_⟩
    have key : toGerm w (mkA g hg) - MvPolynomial.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w) F =
        toGerm w (mkA g hg - ∑ m ∈ F.support, compA A w (rep (F.coeff m)) * ∏ i, Z i ^ m i) := by
      rw [MvPolynomial.eval₂_eq']
      simp only [map_sub, map_sum, map_mul, map_prod, map_pow, hpull, hZ]
    rw [key] at hF
    refine isGermCombination_of_mem p _ hF _ fun z => ?_
    rw [Finset.sum_image (fun x _ y _ h => e.injective h)]
    simp [Z, mkA, compA, Finset.sum_apply, Finset.prod_apply, e]
end GermProjectionFunctionForm
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
