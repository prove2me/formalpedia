-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.STD.fourier_test
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:07.346421+00:00
-- url     : https://prove2.me/submissions/72fe51ba-bf42-4379-b216-f86018f01537

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiff
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_eTr_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_dList_exp
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_sum_sign_prod_ell
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_ibp_dList
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_integrable_mul_of_contOn
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_isT_dList


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.STD
theorem _root_.solution (β : Matrix (Fin n) (Fin n) ℂ) (hdet : β.det = 0) {φ : Vr n → ℂ} (hφ : IsT Set.univ φ) :
    ∫ x, (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * dList (List.ofFn (ml σ)).reverse φ x) * eTr β x = 0 := by
  set E : Vr n → ℂ := fun y => 1 * Complex.exp (ell β (herm y)) with hE
  have hEs : ContDiffOn ℝ ∞ E Set.univ := by
    refine (contDiff_const.mul ?_).contDiffOn
    exact Complex.contDiff_exp.comp (((ell β).restrictScalars ℝ).contDiff.comp (hermL n).contDiff)
  have hT : ∀ σ : Equiv.Perm (Fin n), IsT Set.univ (dList (List.ofFn (ml σ)).reverse φ) := fun σ => isT_dList hφ _
  have hint : ∀ σ : Equiv.Perm (Fin n), Integrable (fun x => E x * dList (List.ofFn (ml σ)).reverse φ x) :=
    fun σ => integrable_mul_of_contOn isOpen_univ hEs.continuousOn (hT σ).smooth.continuous (hT σ).cpt
      (Set.subset_univ _)
  have h1 : (fun x => (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * dList (List.ofFn (ml σ)).reverse φ x) *
      eTr β x) = fun x => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
        (E x * dList (List.ofFn (ml σ)).reverse φ x) := by
    funext x; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun σ _ => ?_; rw [eTr_eq]; simp only [E]; ring
  rw [h1, integral_finsetSum _ (fun σ _ => (hint σ).const_mul _)]
  have h2 : ∀ σ : Equiv.Perm (Fin n), ∫ x, (Equiv.Perm.sign σ : ℂ) * (E x * dList (List.ofFn (ml σ)).reverse φ x) =
      (Equiv.Perm.sign σ : ℂ) * ((-1) ^ Fintype.card (Fin n) *
        (((List.ofFn (ml σ)).map fun a => ell β (Matrix.single a.1 a.2 1)).prod *
          ∫ x, Complex.exp (ell β (herm x)) * φ x)) := by
    intro σ
    rw [integral_const_mul, ibp_dList isOpen_univ _ hEs hφ, List.reverse_reverse, List.length_reverse,
      List.length_ofFn]
    congr 2
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [E]
    rw [dList_exp β _ 1 x]
    ring
  rw [Finset.sum_congr rfl (fun σ _ => h2 σ)]
  have h3 : ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * ((-1) ^ Fintype.card (Fin n) *
        (((List.ofFn (ml σ)).map fun a => ell β (Matrix.single a.1 a.2 1)).prod *
          ∫ x, Complex.exp (ell β (herm x)) * φ x)) =
      (-1) ^ Fintype.card (Fin n) * (∫ x, Complex.exp (ell β (herm x)) * φ x) *
        ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
          ((List.ofFn (ml σ)).map fun a => ell β (Matrix.single a.1 a.2 1)).prod := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun σ _ => ?_; ring
  rw [h3, sum_sign_prod_ell, hdet]
  ring
end PositivityTheory.Rg.Sw.LVs.STD
