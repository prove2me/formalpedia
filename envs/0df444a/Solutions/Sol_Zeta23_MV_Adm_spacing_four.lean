-- Prove2me | solution 1 for Zeta23.MV.Adm.spacing_four
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:34:24.254632+00:00
-- url     : https://prove2.me/submissions/328966d8-0e99-4181-b893-7be0e255b87d

import Mathlib
import Definitions.Def_Zeta23_MV_Spacing
import Theorems.Thm_Zeta23_MV_Adm_abs_le_of_mem_itv
import Theorems.Thm_Zeta23_MV_Adm_integral_inv_four_Icc

-- from Zeta23.MV.Spacing
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# MV step 0 — spacing lemmas for admissible weights

For an injective `freq : ι → ℝ` on a finite index type with ADMISSIBLE weights `δ`
(`0 < δ r` and `δ r ≤ |freq r − freq s|` for all `s ≠ r` — the shape of Zeta23.MVHilbert),
the open intervals `I_t = (freq t − δ t/2, freq t + δ t/2)` are pairwise disjoint, giving
by comparison with `∫ |u − freq s|^{−σ} du`:

* `spacing_sq`   (σ = 2):  Σ_{t≠s} δ t/(freq s − freq t)²  ≤  9/δ s
* `spacing_four` (σ = 4):  Σ_{t≠s} δ t/(freq s − freq t)⁴  ≤  27/(δ s)³
* `two_point`:  Σ_{k≠ℓ,m} δ k/((freq k − freq ℓ)²(freq k − freq m)²)
                  ≤ 36(δ ℓ + δ m)/(δ ℓ · δ m · (freq ℓ − freq m)²)

These replace [Preissmann 1984, Lemmes 1 & 6] (cited without proof in arXiv:2203.14950)
with elementary arguments at worse constants — sufficient for the ∃C form.
-/

noncomputable section
open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


namespace Adm

variable {freq δ : ι → ℝ} (h : Adm freq δ)


omit [Fintype ι] [DecidableEq ι] in
/-- Centers are far apart: `(δ t + δ t')/2 ≤ |freq t − freq t'|` for `t ≠ t'`. -/
lemma centers_far (h : Adm freq δ) {t t' : ι} (htt : t ≠ t') :
    (δ t + δ t') / 2 ≤ |freq t - freq t'| := by
  have h1 := h.le t t' htt
  have h2 := h.le t' t htt.symm
  rw [abs_sub_comm] at h2
  rcases le_total (δ t) (δ t') with hd | hd <;> linarith

/-- The intervals are pairwise disjoint. -/
lemma itv_disjoint (h : Adm freq δ) :
    Set.univ.PairwiseDisjoint (fun t : ι => Adm.itv (freq := freq) (δ := δ) t) := by
  intro t _ t' _ htt
  have hfar := h.centers_far htt
  rw [Function.onFun, Set.disjoint_left]
  intro u hu hu'
  simp only [Adm.itv, Set.mem_Ioo] at hu hu'
  rcases abs_cases (freq t - freq t') with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hfar <;>
    linarith [hu.1, hu.2, hu'.1, hu'.2]





section MainSpacing
variable (h : Adm freq δ) (s : ι)

/-- The two-sided tail window around `freq s`, radius `R`. -/
def window (freq δ : ι → ℝ) (s : ι) (R : ℝ) : Set ℝ :=
  Set.Icc (freq s - R) (freq s - δ s / 2) ∪ Set.Icc (freq s + δ s / 2) (freq s + R)

lemma mem_window (h : Adm freq δ) {s t : ι} (hts : t ≠ s) {R : ℝ}
    (hR : 3 / 2 * |freq s - freq t| ≤ R) {u : ℝ}
    (hu : u ∈ Adm.itv (freq := freq) (δ := δ) t) : u ∈ window freq δ s R := by
  have hb := h.abs_le_of_mem_itv hts hu
  have h1 : |u - freq s| ≤ R := by
    rw [abs_sub_comm]; exact hb.1.trans hR
  rcases le_total u (freq s) with hle | hle
  · left
    rw [abs_of_nonpos (by linarith : u - freq s ≤ 0)] at h1
    rw [abs_of_nonpos (by linarith : u - freq s ≤ 0)] at hb
    exact ⟨by linarith, by linarith [hb.2]⟩
  · right
    rw [abs_of_nonneg (by linarith : 0 ≤ u - freq s)] at h1
    rw [abs_of_nonneg (by linarith : 0 ≤ u - freq s)] at hb
    exact ⟨by linarith [hb.2], by linarith⟩

omit [Fintype ι] [DecidableEq ι] in
lemma window_integrable {s : ι} {R : ℝ} (hδs : 0 < δ s) {k : ℕ} (_hk : k ≠ 0) :
    MeasureTheory.IntegrableOn (fun u => ((u - freq s) ^ k)⁻¹) (window freq δ s R) := by
  have hcompact : IsCompact (window freq δ s R) := (isCompact_Icc).union isCompact_Icc
  refine ContinuousOn.integrableOn_compact hcompact ?_
  have hne : ∀ u ∈ window freq δ s R, (u - freq s) ^ k ≠ 0 := by
    intro u hu
    apply pow_ne_zero
    rcases hu with hu | hu
    · simp only [Set.mem_Icc] at hu; intro hh; nlinarith [hu.2]
    · simp only [Set.mem_Icc] at hu; intro hh; nlinarith [hu.1]
  exact ((continuous_sub_right (freq s)).pow k).continuousOn.inv₀ hne


end MainSpacing





end Adm
end MV
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open MV
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Adm
variable {freq δ : ι → ℝ} (h : Adm freq δ)

theorem solution (h : Adm freq δ) (s : ι) :
    ∑ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 4 ≤ 27 / δ s ^ 3 := by
  classical
  have hδs := h.pos s
  rcases Finset.eq_empty_or_nonempty (Finset.univ.erase s) with he | hne
  · rw [he, Finset.sum_empty]; positivity
  obtain ⟨t₀, ht₀⟩ := hne
  set g : ℝ → ℝ := fun u => ((u - freq s) ^ 4)⁻¹ with hg
  set M : ℝ := Finset.univ.sup' ⟨s, Finset.mem_univ s⟩ (fun t => |freq s - freq t|) with hM
  set R : ℝ := 3 / 2 * M + 1 with hR
  have hMle : ∀ t : ι, |freq s - freq t| ≤ M := fun t =>
    Finset.le_sup' (fun r => |freq s - freq r|) (Finset.mem_univ t)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMle s)
  have hδM : δ s ≤ M := (h.le s t₀ (Finset.ne_of_mem_erase ht₀).symm).trans (hMle t₀)
  have hRδ : δ s / 2 ≤ R := by linarith
  have hintW : MeasureTheory.IntegrableOn g (window freq δ s R) :=
    window_integrable (freq := freq) (δ := δ) hδs four_ne_zero
  have hsub : ∀ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t ⊆ window freq δ s R := by
    intro t ht u hu
    exact mem_window h (Finset.ne_of_mem_erase ht) (by linarith [hMle t]) hu
  have hper : ∀ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 4
      ≤ 81 / 16 * ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
    intro t ht
    have hts : t ≠ s := Finset.ne_of_mem_erase ht
    have hfst : (freq s - freq t) ≠ 0 := sub_ne_zero.2 fun hh => hts (h.inj hh.symm)
    have hpos4 : 0 < (freq s - freq t) ^ 4 := by positivity
    have hδt := h.pos t
    have hlow : ∀ u ∈ Adm.itv (freq := freq) (δ := δ) t,
        (81 / 16 * (freq s - freq t) ^ 4)⁻¹ ≤ g u := by
      intro u hu
      have hb := h.abs_le_of_mem_itv hts hu
      have hu0 : 0 < |u - freq s| := lt_of_lt_of_le (by linarith) hb.2
      have hsq : (u - freq s) ^ 4 ≤ 81 / 16 * (freq s - freq t) ^ 4 := by
        have h1 : |u - freq s| ≤ 3 / 2 * |freq s - freq t| := by
          rw [abs_sub_comm]; exact hb.1
        calc (u - freq s) ^ 4 = |u - freq s| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
          _ ≤ (3 / 2 * |freq s - freq t|) ^ 4 := by gcongr
          _ = 81 / 16 * |freq s - freq t| ^ 4 := by ring
          _ = 81 / 16 * (freq s - freq t) ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      have hupos : 0 < (u - freq s) ^ 4 := by
        have := abs_pos.1 hu0; positivity
      show _ ≤ ((u - freq s) ^ 4)⁻¹
      exact (inv_le_inv₀ (by positivity) hupos).2 hsq
    have hintT : MeasureTheory.IntegrableOn g (Adm.itv (freq := freq) (δ := δ) t) :=
      hintW.mono_set (hsub t ht)
    have h1 : ∫ _u in Adm.itv (freq := freq) (δ := δ) t, (81 / 16 * (freq s - freq t) ^ 4)⁻¹
        ≤ ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
      apply MeasureTheory.setIntegral_mono_on
      · exact MeasureTheory.integrableOn_const (by simp [Adm.itv])
      · exact hintT
      · exact measurableSet_Ioo
      · exact hlow
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at h1
    have hvol : (volume (Adm.itv (freq := freq) (δ := δ) t)).toReal = δ t := by
      rw [Adm.itv, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [MeasureTheory.measureReal_def, hvol] at h1
    calc δ t / (freq s - freq t) ^ 4
        = 81 / 16 * (δ t * (81 / 16 * (freq s - freq t) ^ 4)⁻¹) := by
          field_simp
      _ ≤ 81 / 16 * ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
          gcongr
  have hdisj : (↑(Finset.univ.erase s) : Set ι).PairwiseDisjoint
      (fun t => Adm.itv (freq := freq) (δ := δ) t) :=
    (h.itv_disjoint).subset (Set.subset_univ _)
  have hsum : ∑ t ∈ Finset.univ.erase s, ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u
      = ∫ u in ⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t, g u := by
    rw [MeasureTheory.integral_biUnion_finset]
    · exact fun t _ => measurableSet_Ioo
    · exact hdisj
    · exact fun t ht => hintW.mono_set (hsub t ht)
  have hUsub : (⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t)
      ⊆ window freq δ s R := by
    simp only [Set.iUnion_subset_iff]
    exact fun t ht => hsub t ht
  have hUmono : ∫ u in ⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t, g u
      ≤ ∫ u in window freq δ s R, g u := by
    apply MeasureTheory.setIntegral_mono_set hintW
    · exact Filter.Eventually.of_forall fun u => by positivity
    · exact Filter.Eventually.of_forall hUsub
  have hwindow : ∫ u in window freq δ s R, g u ≤ 16 / (3 * δ s ^ 3) := by
    have hd : Disjoint (Set.Icc (freq s - R) (freq s - δ s / 2))
        (Set.Icc (freq s + δ s / 2) (freq s + R)) := by
      rw [Set.disjoint_left]
      intro u hu hu'
      simp only [Set.mem_Icc] at hu hu'
      linarith [hu.2, hu'.1]
    have hil : MeasureTheory.IntegrableOn g (Set.Icc (freq s - R) (freq s - δ s / 2)) :=
      hintW.mono_set Set.subset_union_left
    have hir : MeasureTheory.IntegrableOn g (Set.Icc (freq s + δ s / 2) (freq s + R)) :=
      hintW.mono_set Set.subset_union_right
    rw [window, MeasureTheory.setIntegral_union hd measurableSet_Icc hil hir]
    have hleft : ∫ u in Set.Icc (freq s - R) (freq s - δ s / 2), g u
        = -((R ^ (3:ℕ))⁻¹ / 3) + ((δ s / 2) ^ (3:ℕ))⁻¹ / 3 := by
      rw [hg, integral_inv_four_Icc (by linarith) (Or.inr (by linarith))]
      have e1 : freq s - R - freq s = -R := by ring
      have e2 : freq s - δ s / 2 - freq s = -(δ s / 2) := by ring
      rw [e1, e2]
      have e3 : (-R) ^ (3:ℕ) = -(R ^ (3:ℕ)) := by ring
      have e4 : (-(δ s / 2)) ^ (3:ℕ) = -((δ s / 2) ^ (3:ℕ)) := by ring
      rw [e3, e4, inv_neg, inv_neg]
      ring
    have hright : ∫ u in Set.Icc (freq s + δ s / 2) (freq s + R), g u
        = ((δ s / 2) ^ (3:ℕ))⁻¹ / 3 - (R ^ (3:ℕ))⁻¹ / 3 := by
      rw [hg, integral_inv_four_Icc (by linarith) (Or.inl (by linarith))]
      have e1 : freq s + δ s / 2 - freq s = δ s / 2 := by ring
      have e2 : freq s + R - freq s = R := by ring
      rw [e1, e2]
    rw [hleft, hright]
    have hR0 : 0 < R := by linarith
    have hRi : 0 < (R ^ (3:ℕ))⁻¹ := by positivity
    have hhalf : ((δ s / 2) ^ (3:ℕ))⁻¹ = 8 / δ s ^ 3 := by
      rw [div_pow]
      norm_num
    have h16 : 16 / (3 * δ s ^ 3) = 8 / δ s ^ 3 / 3 + 8 / δ s ^ 3 / 3 := by ring
    rw [hhalf]
    linarith
  calc ∑ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 4
      ≤ ∑ t ∈ Finset.univ.erase s, 81 / 16 * ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u :=
        Finset.sum_le_sum hper
    _ = 81 / 16 * ∑ t ∈ Finset.univ.erase s, ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
        rw [Finset.mul_sum]
    _ = 81 / 16 * ∫ u in ⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t, g u := by
        rw [hsum]
    _ ≤ 81 / 16 * (16 / (3 * δ s ^ 3)) := by
        have := hUmono.trans hwindow
        gcongr
    _ = 27 / δ s ^ 3 := by field_simp; ring
