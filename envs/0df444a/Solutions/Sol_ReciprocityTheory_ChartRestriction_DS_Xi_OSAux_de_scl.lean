-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.de_scl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:18:53.57238+00:00
-- url     : https://prove2.me/submissions/cb489d22-4b5d-4ecf-9bf2-96a37d639d9b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux
private lemma scl_fst_norm {p m : ℕ} (τ : ℝ) (h1 : 1 ≤ τ) (x : Xp (p + 1) m) (j : Fin (p + 1)) :
    ‖x.1 j‖ ≤ ‖(scl τ x).1 j‖ := by
  by_cases hj : j = 0
  · subst hj
    have e : (scl τ x).1 0 = (τ : ℂ) * x.1 0 := by simp [scl]
    have hτ : ‖(τ : ℂ)‖ = τ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [e, norm_mul, hτ]
    exact le_mul_of_one_le_left (norm_nonneg _) h1
  · have e : (scl τ x).1 j = x.1 j := by simp [scl, hj]
    rw [e]
private lemma scl_snd_sq {p m : ℕ} (τ : ℝ) (h1 : 1 ≤ τ) (h2 : τ ≤ 2) (x : Xp (p + 1) m) (j : Fin (p + 1)) :
    ‖x.2.1 j‖ ^ 2 / 4 ≤ ‖(scl τ x).2.1 j‖ ^ 2 := by
  have ha := sq_nonneg ‖x.2.1 j‖
  by_cases hj : j = 0
  · subst hj
    have hτ : ‖(τ : ℂ)‖ = τ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have e : (scl τ x).2.1 0 = x.2.1 0 / (τ : ℂ) := by simp [scl]
    rw [e, norm_div, hτ, div_pow, div_le_div_iff₀ (by norm_num) (by positivity)]
    apply mul_le_mul_of_nonneg_left _ ha
    nlinarith
  · have e : (scl τ x).2.1 j = x.2.1 j := by simp [scl, hj]
    rw [e]
    linarith
private lemma Lsq_scl {p m : ℕ} (τ : ℝ) (h1 : 1 ≤ τ) (x : Xp (p + 1) m) (l : Fin (p + 2)) :
    Lsq x l ≤ Lsq (scl τ x) l := by
  unfold Lsq
  have hs : (∑ j : Fin (p + 1), if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) ≤
      ∑ j : Fin (p + 1), if j.val < l.val then ‖(scl τ x).1 j‖ ^ 2 else 0 := by
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · have h := scl_fst_norm τ h1 x j
      gcongr
    · exact le_rfl
  linarith
private lemma Lsq_pos {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 0 < Lsq x l := by
  unfold Lsq
  have h : 0 ≤ ∑ j : Fin p, (if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  linarith
private lemma rhoSq_nonneg {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 0 ≤ rhoSq x l := by
  unfold rhoSq
  have h1 := Lsq_pos x (Fin.last p)
  have h2 : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h3 : 0 ≤ ∑ j : Fin p, (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  linarith
private lemma rhoSq_scl {p m : ℕ} (τ : ℝ) (h1 : 1 ≤ τ) (h2 : τ ≤ 2) (x : Xp (p + 1) m) (l : Fin (p + 2)) :
    rhoSq x l / 4 ≤ rhoSq (scl τ x) l := by
  have hA := Lsq_scl τ h1 x (Fin.last (p + 1))
  have hA0 := Lsq_pos x (Fin.last (p + 1))
  have hB : (scl τ x).2.2.1 = x.2.2.1 := rfl
  have hB0 : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hC : (∑ j : Fin (p + 1), (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0)) / 4 ≤
      ∑ j : Fin (p + 1), (if l.val ≤ j.val then ‖(scl τ x).2.1 j‖ ^ 2 else 0) := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · exact scl_snd_sq τ h1 h2 x j
    · simp
  unfold rhoSq
  rw [hB]
  linarith
private lemma bco_scl {p m : ℕ} (τ : ℝ) (h1 : 1 ≤ τ) (x : Xp (p + 1) m) (l : Fin (p + 2)) :
    bco (scl τ x) l = bco x l := by
  have e1 : (scl τ x).2.2.1 = x.2.2.1 := rfl
  have e2 : (scl τ x).2.2.2 = x.2.2.2 := rfl
  unfold bco
  rw [e1, e2]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have key : (scl τ x).2.1 j * star ((scl τ x).1 j) = x.2.1 j * star (x.1 j) := by
    by_cases hj : j = 0
    · subst hj
      have hτ : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
      have e3 : (scl τ x).2.1 0 = x.2.1 0 / (τ : ℂ) := by simp [scl]
      have e4 : (scl τ x).1 0 = (τ : ℂ) * x.1 0 := by simp [scl]
      rw [e3, e4, star_mul', Complex.star_def, Complex.conj_ofReal]
      field_simp
    · have e3 : (scl τ x).2.1 j = x.2.1 j := by simp [scl, hj]
      have e4 : (scl τ x).1 j = x.1 j := by simp [scl, hj]
      rw [e3, e4]
  rw [key]
end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution {p m : ℕ} (τ : ℝ) (h1 : 1 ≤ τ) (h2 : τ ≤ 2) (x : Xp (p + 1) m) (l : Fin (p + 2)) :
    de x l / 2 ≤ de (scl τ x) l := by
  unfold de
  rw [bco_scl τ h1 x l]
  have hL := Lsq_scl τ h1 x l
  have hL0 := Lsq_pos x l
  have hr := rhoSq_scl τ h1 h2 x l
  have hr0 := rhoSq_nonneg x l
  have hb := sq_nonneg ‖bco x l‖
  have hm : Lsq x l * (rhoSq x l / 4) ≤ Lsq (scl τ x) l * rhoSq (scl τ x) l :=
    mul_le_mul hL hr (by positivity) (by linarith)
  have key : (Lsq x l * rhoSq x l + ‖bco x l‖ ^ 2) / 4 ≤
      Lsq (scl τ x) l * rhoSq (scl τ x) l + ‖bco x l‖ ^ 2 := by
    nlinarith
  have h4 : Real.sqrt ((Lsq x l * rhoSq x l + ‖bco x l‖ ^ 2) / 4) =
      Real.sqrt (Lsq x l * rhoSq x l + ‖bco x l‖ ^ 2) / 2 := by
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← h4]
  exact Real.sqrt_le_sqrt key
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
