-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.reveal_overlap_miss_concentration
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:38:50.488411+00:00
-- url     : https://prove2.me/submissions/0bb44695-cb4d-4f64-920e-997d1d4c045b

import Definitions.Def_ZeroFreeRRG_Hardcore_RevealOverlap
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_pi_positive_simplex
import Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_two_sided_bernstein
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid)
    (t s η : ℝ) (ht : m.PosParam t) (hs : 0 < s) (hs1 : s ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) (n : ℕ) (σ σ' : Fin n → m.Spin)
    (hdev : fullOverlapDeviation m t η σ σ') :
    (∑ U : Finset (Fin n), revealProb s U *
      (if ¬ revealedOverlapH m t s η U (fun v => σ v.1) (fun v => σ' v.1) then 1 else 0))
      ≤ 2*Real.exp (-(s*η^2/12)*n) := by
  classical
  letI : DecidableEq (m.Spin × m.Spin) := Classical.decEq _
  obtain ⟨ab,hab⟩ := hdev
  let p : ℝ := m.pi t ab.1 * m.pi t ab.2
  let z : Fin n → ℝ := fun v => (if σ v = ab.1 ∧ σ' v = ab.2 then 1 else 0)-p
  have hπ := model_pi_positive_simplex m hm t ht
  have hpi1 : m.pi t ab.1 ∈ Icc (0:ℝ) 1 := mem_Icc_of_mem_stdSimplex hπ.2 ab.1
  have hpi2 : m.pi t ab.2 ∈ Icc (0:ℝ) 1 := mem_Icc_of_mem_stdSimplex hπ.2 ab.2
  have hp0 : 0 ≤ p := mul_nonneg hpi1.1 hpi2.1
  have hp1 : p ≤ 1 := by
    dsimp [p]
    have hh := mul_le_mul_of_nonneg_right hpi1.2 hpi2.1
    nlinarith [hpi2.2]
  have hz (v : Fin n) : |z v| ≤ 1 := by
    dsimp [z]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hprob (U : Finset (Fin n)) : 0 ≤ revealProb s U := by
    unfold revealProb
    exact mul_nonneg (pow_nonneg hs.le _) (pow_nonneg (sub_nonneg.mpr hs1) _)
  by_cases hn : n = 0
  · have hH (U : Finset (Fin n)) : revealedOverlapH m t s η U (fun v => σ v.1) (fun v => σ' v.1) := by
      refine ⟨ab,?_⟩
      simpa [hn] using abs_nonneg (∑ v : {v : Fin n // v ∈ U},
        ((if σ v.1 = ab.1 ∧ σ' v.1 = ab.2 then (1:ℝ) else 0)-p))
    simp only [hH,not_true_eq_false, ↓reduceIte,mul_zero,Finset.sum_const_zero]
    positivity
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have htotal : (∑ v : Fin n, z v) = n*(ZeroFreeRRG.Hardcore.overlap σ σ' ab-p) := by
    dsimp [z,ZeroFreeRRG.Hardcore.overlap,empMarg]
    rw [Finset.sum_sub_distrib,Finset.sum_boole]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have heq : (Finset.univ.filter (fun v : Fin n => σ v = ab.1 ∧ σ' v = ab.2)).card =
        (Finset.univ.filter (fun v : Fin n => (σ v,σ' v) = ab)).card := by
      apply congrArg Finset.card
      ext v
      simp [Prod.ext_iff]
    rw [heq]
    field_simp
  have htotalabs : s*η*n < |s*(∑ v : Fin n, z v)| := by
    rw [htotal,abs_mul,abs_of_pos hs,abs_mul,abs_of_pos hnpos]
    change η < |ZeroFreeRRG.Hardcore.overlap σ σ' ab-p| at hab
    have hh := mul_lt_mul_of_pos_left hab (mul_pos hs hnpos)
    nlinarith
  have hpoint (U : Finset (Fin n)) :
      (if ¬ revealedOverlapH m t s η U (fun v => σ v.1) (fun v => σ' v.1) then (1:ℝ) else 0) ≤
      (if s*η*n/2 ≤ |(∑ v ∈ U, z v) - s*(∑ v : Fin n, z v)| then 1 else 0) := by
    split_ifs with hbad hbig <;> try norm_num
    exfalso
    rename_i hbig
    have hsmall : |∑ v ∈ U, z v| < s*η*n/2 := by
      by_contra hnot
      apply hbad
      refine ⟨ab,?_⟩
      have hh : s*η*n/2 ≤ |∑ v ∈ U, z v| := le_of_not_gt hnot
      change s*η*n/2 ≤ |∑ v : {v : Fin n // v ∈ U}, z v.1|
      rw [Finset.sum_coe_sort]
      exact hh
    have htriangle := abs_add_le ((∑ v ∈ U, z v) - s*(∑ v : Fin n, z v)) (-(∑ v ∈ U, z v))
    have hnotbig : |(∑ v ∈ U, z v) - s*(∑ v : Fin n, z v)| < s*η*n/2 := lt_of_not_ge hbig
    have htri : |s*(∑ v : Fin n, z v)| ≤
        |(∑ v ∈ U, z v) - s*(∑ v : Fin n, z v)| + |∑ v ∈ U, z v| := by
      have heq : ((∑ v ∈ U, z v) - s*(∑ v : Fin n, z v)) + (-(∑ v ∈ U, z v)) =
          -(s*(∑ v : Fin n, z v)) := by ring
      rw [heq,abs_neg,abs_neg] at htriangle
      exact htriangle
    linarith
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Finset (Fin n))))
    (fun U _ => mul_le_mul_of_nonneg_left (hpoint U) (hprob U))
  exact hsum.trans (reveal_two_sided_bernstein n s η z hs.le hs1 hη hη1 hz)
