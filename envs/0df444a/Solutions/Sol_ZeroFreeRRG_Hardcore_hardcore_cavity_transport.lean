-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_cavity_transport
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:04:40.026118+00:00
-- url     : https://prove2.me/submissions/3dde0227-63ba-435f-883e-5576db6786ca

import Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_affine_transport
import Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_affine_nontrivial
import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators
open MeasureTheory ZeroFreeRRG.Hardcore

private lemma pi0 (a : ℝ) : Model.pi .hardcore a (0 : Fin 2) = 1-a := by
  simp [Model.pi, Model.Spin, Model.P, Fin.sum_univ_two] <;> ring
private lemma pi1 (a : ℝ) : Model.pi .hardcore a (1 : Fin 2) = a := by
  simp [Model.pi, Model.Spin, Model.P, Fin.sum_univ_two]

theorem solution (a a' : ℝ) (ha : 0 < a) (hlt : a < a') (ha' : a' < 1/2)
    (ν : ProbabilityMeasure ((.hardcore : Model).Spin → ℝ)) (hν : ν ∈ cavityLaws .hardcore a) :
    let c := (1-a')/(1-a)
    0 < c ∧ c < 1 ∧ ∃ ν' ∈ cavityLaws .hardcore a',
      (ν ≠ diracPi .hardcore a → ν' ≠ diracPi .hardcore a') ∧
      (ν' : Measure ((.hardcore : Model).Spin → ℝ)) =
        Measure.map (fun x : ((.hardcore : Model).Spin → ℝ) => fun i =>
          (1-c)*(if i.val = 1 then 1 else 0) + c*x i) (ν : Measure _) := by
  classical
  dsimp only
  let c : ℝ := (1-a')/(1-a)
  have hd : 0 < 1-a := by linarith
  have hd' : 0 < 1-a' := by linarith
  have hc0 : 0 < c := div_pos hd' hd
  have hc1 : c < 1 := (div_lt_one hd).2 (by linarith)
  let r : (.hardcore : Model).Spin → ℝ := fun i => if i.val = 1 then 1 else 0
  have hr : r ∈ stdSimplex ℝ ((.hardcore : Model).Spin) := by
    change r ∈ stdSimplex ℝ (Fin 2)
    constructor
    · intro i
      dsimp [r]
      split_ifs <;> norm_num
    · change (∑ i : Fin 2, r i) = 1
      rw [Fin.sum_univ_two]
      norm_num [r]
  have hmean : ∀ i : (.hardcore : Model).Spin,
      Model.pi .hardcore a' i = (1-c)*r i+c*Model.pi .hardcore a i := by
    intro i
    change Fin 2 at i
    fin_cases i
    · change Model.pi .hardcore a' (0 : Fin 2) = (1-c)*r (0 : Fin 2)+c*Model.pi .hardcore a (0 : Fin 2)
      rw [pi0,pi0]
      dsimp [r,c]
      norm_num only [Fin.val_zero, Nat.zero_ne_one, ite_false, mul_zero, add_zero]
      field_simp
      <;> ring
    · change Model.pi .hardcore a' (1 : Fin 2) = (1-c)*r (1 : Fin 2)+c*Model.pi .hardcore a (1 : Fin 2)
      rw [pi1,pi1]
      dsimp [r,c]
      field_simp
      <;> ring
  obtain ⟨ν',hν',hmap⟩ := cavity_affine_transport .hardcore a a' ν hν r hr c hc0.le hc1.le hmean
  refine ⟨hc0,hc1,ν',hν',?_,?_⟩
  · intro hne
    obtain ⟨ξ,hξ,hξne,hξmap⟩ := cavity_affine_nontrivial .hardcore a a' ν hν r hr c hc0.le hc1.le (ne_of_gt hc0) hmean hne
    have heq : ν' = ξ := ProbabilityMeasure.toMeasure_injective (hmap.trans hξmap.symm)
    simpa [heq] using hξne
  · simpa [r,c] using hmap
