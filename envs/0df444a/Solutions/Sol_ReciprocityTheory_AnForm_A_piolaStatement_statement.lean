-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.piolaStatement_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:13.722093+00:00
-- url     : https://prove2.me/submissions/5a9d445b-73ec-4384-8c9b-81c6efd0d430

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Theorems.Thm_ReciprocityTheory_AnForm_A_third_fderiv_symm_one_two
import Theorems.Thm_ReciprocityTheory_AnForm_A_differentiableAt_snd_fderiv
import Theorems.Thm_ReciprocityTheory_AnForm_A_third_fderiv_symm_two_three
import Theorems.Thm_ReciprocityTheory_AnForm_A_dzEntry_symm
import Theorems.Thm_ReciprocityTheory_AnForm_A_dzbEntry_symm
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessCof_hasDeriv
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessMat_apply
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_sum_col
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_sum_row
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_update_comb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : PiolaStatement := by
  intro n φ U hU hφ z hz
  have hφz : ∀ i, ContDiffAt ℝ 3 (φ i) z := fun i => (hφ i).contDiffAt (hU.mem_nhds hz)
  have hdiff : ∀ i, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (φ i))) z :=
    fun i => differentiableAt_snd_fderiv _ z (hφz i)
  set T : Fin n → (Fin (n + 1) → ℂ) →L[ℝ] BilinSp (n + 1) :=
    fun i => fderiv ℝ (fderiv ℝ (fderiv ℝ (φ i))) z with hTdef
  set H : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun l => hessC (φ l) z with hH
  constructor
  · intro k
    have hj : ∀ j, dz j (fun y => hessCof φ y j k) z = ∑ i, mdisc (Function.update
        (Function.update (Fin.cons 0 H) 0 (Matrix.single j k 1)) i.succ
        ((1 / 2 : ℂ) • hessMat (T i (Pi.single j 1)) +
          (-(Complex.I / 2)) • hessMat (T i (Complex.I • Pi.single j 1)))) := by
      intro j
      obtain ⟨_, hD⟩ := hessCof_hasDeriv φ z hdiff j k
      rw [Fin.update_cons_zero]
      simp only [mdisc_update_comb, Finset.sum_add_distrib, ← Finset.mul_sum]
      show (fderiv ℝ _ z _ - Complex.I * fderiv ℝ _ z _) / 2 = _
      rw [hD, hD]; ring
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine mdisc_sum_row _ 0 i.succ (Fin.succ_ne_zero i).symm k _ fun j a b => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, hessMat_apply, smul_eq_mul]
    exact dzEntry_symm (T i) (third_fderiv_symm_one_two _ z (hφz i)) j a b
  · intro j
    have hk : ∀ k, dzb k (fun y => hessCof φ y j k) z = ∑ i, mdisc (Function.update
        (Function.update (Fin.cons 0 H) 0 (Matrix.single j k 1)) i.succ
        ((1 / 2 : ℂ) • hessMat (T i (Pi.single k 1)) +
          (Complex.I / 2) • hessMat (T i (Complex.I • Pi.single k 1)))) := by
      intro k
      obtain ⟨_, hD⟩ := hessCof_hasDeriv φ z hdiff j k
      rw [Fin.update_cons_zero]
      simp only [mdisc_update_comb, Finset.sum_add_distrib, ← Finset.mul_sum]
      show (fderiv ℝ _ z _ + Complex.I * fderiv ℝ _ z _) / 2 = _
      rw [hD, hD]; ring
    rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine mdisc_sum_col _ 0 i.succ (Fin.succ_ne_zero i).symm j _ fun k a b => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, hessMat_apply, smul_eq_mul]
    refine dzbEntry_symm (T i) (fun u x y => ?_) k a b
    rw [third_fderiv_symm_one_two _ z (hφz i), third_fderiv_symm_two_three _ z (hφz i), third_fderiv_symm_one_two _ z (hφz i)]
end ReciprocityTheory.AnForm.A
