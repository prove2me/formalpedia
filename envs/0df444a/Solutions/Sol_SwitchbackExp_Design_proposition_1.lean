-- Prove2me | solution 1 for SwitchbackExp.Design.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T00:16:31.431747+00:00
-- url     : https://prove2.me/submissions/25a96a3c-c52f-45ea-8058-9c946770c9f6

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_Design_Setting

namespace SwbAux
open Finset SwitchbackExp.Design

lemma det_spec (P : Finset ℕ) (h1 : 1 ∈ P) (s : ℕ) (hs : 1 ≤ s) :
    detPoint P s ∈ P ∧ detPoint P s ≤ s ∧ ∀ x ∈ P, x ≤ s → x ≤ detPoint P s := by
  have hne : (P.filter (· ≤ s)).Nonempty := ⟨1, by simp [h1, hs]⟩
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup _ hne id
  have hd : detPoint P s = i := heq
  simp only [Finset.mem_filter] at hi
  refine ⟨hd ▸ hi.1, hd ▸ hi.2, fun x hx hxs => ?_⟩
  have : x ≤ (P.filter (· ≤ s)).sup id :=
    Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hx, hxs⟩)
  exact this

lemma det_mono (P : Finset ℕ) {s s' : ℕ} (h : s ≤ s') : detPoint P s ≤ detPoint P s' := by
  unfold detPoint
  apply Finset.sup_mono
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, le_trans hx.2 h⟩

lemma detPoints_sub (P : Finset ℕ) (h1 : 1 ∈ P) (m t : ℕ) (ht : m + 1 ≤ t) :
    detPoints P m t ⊆ P := by
  intro x hx
  simp only [detPoints, Finset.mem_image, Finset.mem_Icc] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  exact (det_spec P h1 s (by omega)).1

/-- expectation over coin vectors -/
noncomputable def E (P : Finset ℕ) (q : ℕ → ℝ) (f : (P → Bool) → ℝ) : ℝ :=
  ∑ c : P → Bool, coinProb P q c * f c

lemma E_prod (P : Finset ℕ) (q : ℕ → ℝ) (g : P → Bool → ℝ) :
    E P q (fun c => ∏ x : P, g x (c x)) =
      ∏ x : P, (q x * g x true + (1 - q x) * g x false) := by
  unfold E coinProb
  symm
  rw [show (∏ x : P, (q x * g x true + (1 - q x) * g x false)) =
      ∏ x : P, ∑ b : Bool, (if b then q x else 1 - q x) * g x b by
    refine Finset.prod_congr rfl fun x _ => ?_
    simp]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.prod_mul_distrib]

lemma prod_sub (P S : Finset ℕ) (hS : S ⊆ P) (f : ℕ → ℝ) :
    ∏ x : P, (if (x : ℕ) ∈ S then f x else 1) = ∏ u ∈ S, f u := by
  rw [Finset.prod_coe_sort P (fun u => if u ∈ S then f u else 1)]
  rw [Finset.prod_ite_mem, Finset.inter_eq_right.2 hS]

/-- indicator that all coins in `D` are heads -/
noncomputable def ind1 (P : Finset ℕ) (D : Finset ℕ) (c : P → Bool) : ℝ :=
  ∏ x : P, (if (x : ℕ) ∈ D then (if c x then 1 else 0) else 1)

/-- indicator that all coins in `D` are tails -/
noncomputable def ind0 (P : Finset ℕ) (D : Finset ℕ) (c : P → Bool) : ℝ :=
  ∏ x : P, (if (x : ℕ) ∈ D then (if c x then 0 else 1) else 1)

lemma E_one (P : Finset ℕ) (q : ℕ → ℝ) : E P q (fun _ => 1) = 1 := by
  have := E_prod P q (fun _ _ => 1)
  simp only [Finset.prod_const_one] at this
  rw [this]
  simp

lemma E_ind1 (P D : Finset ℕ) (hD : D ⊆ P) (q : ℕ → ℝ) :
    E P q (fun c => ind1 P D c) = ∏ u ∈ D, q u := by
  unfold ind1
  rw [E_prod (g := fun x b => if (x : ℕ) ∈ D then (if b then (1:ℝ) else 0) else 1)]
  rw [← prod_sub P D hD]
  refine Finset.prod_congr rfl fun x _ => ?_
  by_cases hx : (x : ℕ) ∈ D <;> simp [hx]

lemma E_ind0 (P D : Finset ℕ) (hD : D ⊆ P) (q : ℕ → ℝ) :
    E P q (fun c => ind0 P D c) = ∏ u ∈ D, (1 - q u) := by
  unfold ind0
  rw [E_prod (g := fun x b => if (x : ℕ) ∈ D then (if b then (0:ℝ) else 1) else 1)]
  rw [← prod_sub P D hD]
  refine Finset.prod_congr rfl fun x _ => ?_
  by_cases hx : (x : ℕ) ∈ D <;> simp [hx]

lemma E_ind11 (P D D' : Finset ℕ) (hD : D ⊆ P) (hD' : D' ⊆ P) (q : ℕ → ℝ) :
    E P q (fun c => ind1 P D c * ind1 P D' c) = ∏ u ∈ D ∪ D', q u := by
  unfold ind1
  simp only [← Finset.prod_mul_distrib]
  rw [E_prod (g := fun x b => (if (x : ℕ) ∈ D then (if b then (1:ℝ) else 0) else 1) *
      (if (x : ℕ) ∈ D' then (if b then (1:ℝ) else 0) else 1))]
  rw [← prod_sub P (D ∪ D') (Finset.union_subset hD hD')]
  refine Finset.prod_congr rfl fun x _ => ?_
  simp only [Finset.mem_union]
  split_ifs <;> simp_all

lemma E_ind00 (P D D' : Finset ℕ) (hD : D ⊆ P) (hD' : D' ⊆ P) (q : ℕ → ℝ) :
    E P q (fun c => ind0 P D c * ind0 P D' c) = ∏ u ∈ D ∪ D', (1 - q u) := by
  unfold ind0
  simp only [← Finset.prod_mul_distrib]
  rw [E_prod (g := fun x b => (if (x : ℕ) ∈ D then (if b then (0:ℝ) else 1) else 1) *
      (if (x : ℕ) ∈ D' then (if b then (0:ℝ) else 1) else 1))]
  rw [← prod_sub P (D ∪ D') (Finset.union_subset hD hD')]
  refine Finset.prod_congr rfl fun x _ => ?_
  simp only [Finset.mem_union]
  split_ifs <;> simp_all

lemma E_ind10 (P D D' : Finset ℕ) (hD : D ⊆ P) (hD' : D' ⊆ P) (q : ℕ → ℝ) :
    E P q (fun c => ind1 P D c * ind0 P D' c) =
      if (D ∩ D').Nonempty then 0 else (∏ u ∈ D, q u) * ∏ u ∈ D', (1 - q u) := by
  unfold ind1 ind0
  simp only [← Finset.prod_mul_distrib]
  rw [E_prod (g := fun x b => (if (x : ℕ) ∈ D then (if b then (1:ℝ) else 0) else 1) *
      (if (x : ℕ) ∈ D' then (if b then (0:ℝ) else 1) else 1))]
  by_cases hO : (D ∩ D').Nonempty
  · rw [if_pos hO]
    obtain ⟨u, hu⟩ := hO
    have huP : u ∈ P := hD (Finset.mem_inter.1 hu).1
    apply Finset.prod_eq_zero (i := ⟨u, huP⟩) (Finset.mem_univ _)
    simp only [Finset.mem_inter] at hu
    simp [hu.1, hu.2]
  · rw [if_neg hO]
    rw [← prod_sub P D hD, ← prod_sub P D' hD', ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    have : ¬ ((x : ℕ) ∈ D ∧ (x : ℕ) ∈ D') := fun h =>
      hO ⟨x, Finset.mem_inter.2 h⟩
    split_ifs <;> simp_all

lemma E_ind01 (P D D' : Finset ℕ) (hD : D ⊆ P) (hD' : D' ⊆ P) (q : ℕ → ℝ) :
    E P q (fun c => ind0 P D c * ind1 P D' c) =
      if (D ∩ D').Nonempty then 0 else (∏ u ∈ D, (1 - q u)) * ∏ u ∈ D', q u := by
  have h := E_ind10 P D' D hD' hD q
  rw [Finset.inter_comm] at h
  simp only [mul_comm (ind0 P D _)]
  rw [h]
  split_ifs <;> ring

end SwbAux

namespace SwbAux
open Finset SwitchbackExp.Design

lemma pathOf_eq (P : Finset ℕ) (c : P → Bool) (s : ℕ) (h : detPoint P s ∈ P) :
    pathOf P c s = c ⟨detPoint P s, h⟩ := by
  simp only [pathOf, dif_pos h]

lemma onesInd_path (P : Finset ℕ) (h1 : 1 ∈ P) (m t : ℕ) (ht : m + 1 ≤ t) (c : P → Bool) :
    onesInd m (pathOf P c) t = ind1 P (detPoints P m t) c := by
  unfold onesInd ind1
  by_cases hA : ∀ s ∈ Finset.Icc (t - m) t, pathOf P c s = true
  · rw [if_pos hA]
    symm
    apply Finset.prod_eq_one
    intro x _
    by_cases hx : (x : ℕ) ∈ detPoints P m t
    · rw [if_pos hx]
      simp only [detPoints, Finset.mem_image] at hx
      obtain ⟨s, hs, hsx⟩ := hx
      have hmem := (det_spec P h1 s (by simp [Finset.mem_Icc] at hs; omega)).1
      have := hA s hs
      rw [pathOf_eq P c s hmem] at this
      have hxe : (⟨detPoint P s, hmem⟩ : P) = x := Subtype.ext hsx
      rw [hxe] at this
      simp [this]
    · rw [if_neg hx]
  · rw [if_neg hA]
    push_neg at hA
    obtain ⟨s, hs, hfalse⟩ := hA
    have hmem := (det_spec P h1 s (by simp [Finset.mem_Icc] at hs; omega)).1
    symm
    apply Finset.prod_eq_zero (i := ⟨detPoint P s, hmem⟩) (Finset.mem_univ _)
    have hD : detPoint P s ∈ detPoints P m t := Finset.mem_image.2 ⟨s, hs, rfl⟩
    rw [pathOf_eq P c s hmem] at hfalse
    simp [hD, hfalse]

lemma zerosInd_path (P : Finset ℕ) (h1 : 1 ∈ P) (m t : ℕ) (ht : m + 1 ≤ t) (c : P → Bool) :
    zerosInd m (pathOf P c) t = ind0 P (detPoints P m t) c := by
  unfold zerosInd ind0
  by_cases hA : ∀ s ∈ Finset.Icc (t - m) t, pathOf P c s = false
  · rw [if_pos hA]
    symm
    apply Finset.prod_eq_one
    intro x _
    by_cases hx : (x : ℕ) ∈ detPoints P m t
    · rw [if_pos hx]
      simp only [detPoints, Finset.mem_image] at hx
      obtain ⟨s, hs, hsx⟩ := hx
      have hmem := (det_spec P h1 s (by simp [Finset.mem_Icc] at hs; omega)).1
      have := hA s hs
      rw [pathOf_eq P c s hmem] at this
      have hxe : (⟨detPoint P s, hmem⟩ : P) = x := Subtype.ext hsx
      rw [hxe] at this
      simp [this]
    · rw [if_neg hx]
  · rw [if_neg hA]
    push_neg at hA
    obtain ⟨s, hs, hfalse⟩ := hA
    have hmem := (det_spec P h1 s (by simp [Finset.mem_Icc] at hs; omega)).1
    symm
    apply Finset.prod_eq_zero (i := ⟨detPoint P s, hmem⟩) (Finset.mem_univ _)
    have hD : detPoint P s ∈ detPoints P m t := Finset.mem_image.2 ⟨s, hs, rfl⟩
    rw [pathOf_eq P c s hmem] at hfalse
    simp [hD, hfalse]

lemma obs1 (m T : ℕ) (Y : Outcomes) (hNA : NonAnticipating T Y) (hC : Carryover m T Y)
    (t : ℕ) (ht1 : m + 1 ≤ t) (htT : t ≤ T) (w : Path) :
    Y t w * onesInd m w t = Y1 Y t * onesInd m w t := by
  unfold onesInd
  split_ifs with h
  · simp only [mul_one]
    let w1 : Path := fun s => if s ≤ t then w s else true
    have e1 : Y t w = Y t w1 := hNA t (by omega) htT w w1 (fun s _ hs => by simp [w1, hs])
    have e2 : Y t w1 = Y t (fun _ => true) := hC t ht1 htT w1 _ (fun s hs1 hs2 => by
      by_cases hst : s ≤ t
      · simp only [w1, if_pos hst]
        exact h s (by simp [Finset.mem_Icc]; omega)
      · simp [w1, hst])
    rw [e1, e2]; rfl
  · simp

lemma obs0 (m T : ℕ) (Y : Outcomes) (hNA : NonAnticipating T Y) (hC : Carryover m T Y)
    (t : ℕ) (ht1 : m + 1 ≤ t) (htT : t ≤ T) (w : Path) :
    Y t w * zerosInd m w t = Y0 Y t * zerosInd m w t := by
  unfold zerosInd
  split_ifs with h
  · simp only [mul_one]
    let w1 : Path := fun s => if s ≤ t then w s else false
    have e1 : Y t w = Y t w1 := hNA t (by omega) htT w w1 (fun s _ hs => by simp [w1, hs])
    have e2 : Y t w1 = Y t (fun _ => false) := hC t ht1 htT w1 _ (fun s hs1 hs2 => by
      by_cases hst : s ≤ t
      · simp only [w1, if_pos hst]
        exact h s (by simp [Finset.mem_Icc]; omega)
      · simp [w1, hst])
    rw [e1, e2]; rfl
  · simp

/-- covariance computation -/
lemma E_cov (P D D' : Finset ℕ) (hD : D ⊆ P) (hD' : D' ⊆ P) (q : ℕ → ℝ)
    (hq : ∀ u ∈ P, 0 < q u ∧ q u < 1) (a b a' b' : ℝ) :
    E P q (fun c =>
      (a * (ind1 P D c / (∏ u ∈ D, q u) - 1) - b * (ind0 P D c / (∏ u ∈ D, (1 - q u)) - 1)) *
      (a' * (ind1 P D' c / (∏ u ∈ D', q u) - 1) - b' * (ind0 P D' c / (∏ u ∈ D', (1 - q u)) - 1)))
    = a * a' * (∏ u ∈ D ∩ D', 1 / q u - 1) + b * b' * (∏ u ∈ D ∩ D', 1 / (1 - q u) - 1)
      + (a * b' + b * a') * (if (D ∩ D').Nonempty then 1 else 0) := by
  set p1 := ∏ u ∈ D, q u with hp1
  set p0 := ∏ u ∈ D, (1 - q u) with hp0
  set p1' := ∏ u ∈ D', q u with hp1'
  set p0' := ∏ u ∈ D', (1 - q u) with hp0'
  have pos1 : 0 < p1 := Finset.prod_pos fun u hu => (hq u (hD hu)).1
  have pos0 : 0 < p0 := Finset.prod_pos fun u hu => by linarith [(hq u (hD hu)).2]
  have pos1' : 0 < p1' := Finset.prod_pos fun u hu => (hq u (hD' hu)).1
  have pos0' : 0 < p0' := Finset.prod_pos fun u hu => by linarith [(hq u (hD' hu)).2]
  have key : ∀ c : P → Bool, coinProb P q c *
      ((a * (ind1 P D c / p1 - 1) - b * (ind0 P D c / p0 - 1)) *
        (a' * (ind1 P D' c / p1' - 1) - b' * (ind0 P D' c / p0' - 1))) =
      a * a' / (p1 * p1') * (coinProb P q c * (ind1 P D c * ind1 P D' c))
      + (- (a * b' / (p1 * p0'))) * (coinProb P q c * (ind1 P D c * ind0 P D' c))
      + (- (b * a' / (p0 * p1'))) * (coinProb P q c * (ind0 P D c * ind1 P D' c))
      + b * b' / (p0 * p0') * (coinProb P q c * (ind0 P D c * ind0 P D' c))
      + (-(a' - b') * a / p1) * (coinProb P q c * ind1 P D c)
      + ((a' - b') * b / p0) * (coinProb P q c * ind0 P D c)
      + (-(a - b) * a' / p1') * (coinProb P q c * ind1 P D' c)
      + ((a - b) * b' / p0') * (coinProb P q c * ind0 P D' c)
      + ((a - b) * (a' - b')) * (coinProb P q c * 1) := by
    intro c
    field_simp
    ring
  unfold E
  rw [Finset.sum_congr rfl fun c _ => key c]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have e11 := E_ind11 P D D' hD hD' q
  have e00 := E_ind00 P D D' hD hD' q
  have e10 := E_ind10 P D D' hD hD' q
  have e01 := E_ind01 P D D' hD hD' q
  have e1 := E_ind1 P D hD q
  have e0 := E_ind0 P D hD q
  have e1' := E_ind1 P D' hD' q
  have e0' := E_ind0 P D' hD' q
  have eone := E_one P q
  unfold E at e11 e00 e10 e01 e1 e0 e1' e0' eone
  rw [e11, e00, e10, e01, e1, e0, e1', e0', eone]
  have u1 := Finset.prod_union_inter (s₁ := D) (s₂ := D') (f := q)
  have u0 := Finset.prod_union_inter (s₁ := D) (s₂ := D') (f := fun u => 1 - q u)
  have posI1 : 0 < ∏ u ∈ D ∩ D', q u :=
    Finset.prod_pos fun u hu => (hq u (hD (Finset.mem_inter.1 hu).1)).1
  have posI0 : 0 < ∏ u ∈ D ∩ D', (1 - q u) :=
    Finset.prod_pos fun u hu => by linarith [(hq u (hD (Finset.mem_inter.1 hu).1)).2]
  have i1 : ∏ u ∈ D ∩ D', 1 / q u = 1 / ∏ u ∈ D ∩ D', q u := by
    rw [Finset.prod_div_distrib, Finset.prod_const_one]
  have i0 : ∏ u ∈ D ∩ D', 1 / (1 - q u) = 1 / ∏ u ∈ D ∩ D', (1 - q u) := by
    rw [Finset.prod_div_distrib, Finset.prod_const_one]
  rw [i1, i0]
  have h11 : ∏ u ∈ D ∪ D', q u = p1 * p1' / ∏ u ∈ D ∩ D', q u := by
    rw [eq_div_iff posI1.ne', u1]
  have h00 : ∏ u ∈ D ∪ D', (1 - q u) = p0 * p0' / ∏ u ∈ D ∩ D', (1 - q u) := by
    rw [eq_div_iff posI0.ne', u0]
  rw [h11, h00]
  split_ifs with hO
  · field_simp
    ring
  · have hE : D ∩ D' = ∅ := Finset.not_nonempty_iff_eq_empty.1 hO
    rw [hE, Finset.prod_empty, Finset.prod_empty]
    field_simp
    ring

end SwbAux

namespace SwbAux
open Finset SwitchbackExp.Design

noncomputable def errT (m : ℕ) (P : Finset ℕ) (q : ℕ → ℝ) (Y : Outcomes) (t : ℕ) (c : P → Bool) : ℝ :=
  Y1 Y t * (ind1 P (detPoints P m t) c / (∏ u ∈ detPoints P m t, q u) - 1)
    - Y0 Y t * (ind0 P (detPoints P m t) c / (∏ u ∈ detPoints P m t, (1 - q u)) - 1)

noncomputable def Cterm (m : ℕ) (P : Finset ℕ) (q : ℕ → ℝ) (Y : Outcomes) (t t' : ℕ) : ℝ :=
  Y1 Y t * Y1 Y t' * (∏ u ∈ overlap P m t t', 1 / q u - 1)
    + Y0 Y t * Y0 Y t' * (∏ u ∈ overlap P m t t', 1 / (1 - q u) - 1)
    + (Y1 Y t * Y0 Y t' + Y0 Y t * Y1 Y t') * (if (overlap P m t t').Nonempty then 1 else 0)

lemma expect_ones (P : Finset ℕ) (h1 : 1 ∈ P) (q : ℕ → ℝ) (m t : ℕ) (ht : m + 1 ≤ t) :
    SwitchbackExp.Design.expect P q (fun v => onesInd m v t) = ∏ u ∈ detPoints P m t, q u := by
  unfold SwitchbackExp.Design.expect
  simp_rw [onesInd_path P h1 m t ht]
  exact E_ind1 P _ (detPoints_sub P h1 m t ht) q

lemma expect_zeros (P : Finset ℕ) (h1 : 1 ∈ P) (q : ℕ → ℝ) (m t : ℕ) (ht : m + 1 ≤ t) :
    SwitchbackExp.Design.expect P q (fun v => zerosInd m v t) = ∏ u ∈ detPoints P m t, (1 - q u) := by
  unfold SwitchbackExp.Design.expect
  simp_rw [zerosInd_path P h1 m t ht]
  exact E_ind0 P _ (detPoints_sub P h1 m t ht) q

lemma err_eq (m T : ℕ) (P : Finset ℕ) (h1 : 1 ∈ P) (q : ℕ → ℝ) (Y : Outcomes)
    (hNA : NonAnticipating T Y) (hC : Carryover m T Y) (c : P → Bool) :
    htEstimator m T P q Y (pathOf P c) - tau m T Y =
      (1 / ((T : ℝ) - m)) * ∑ t ∈ Finset.Icc (m + 1) T, errT m P q Y t c := by
  unfold htEstimator tau
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_Icc] at ht
  rw [obs1 m T Y hNA hC t ht.1 ht.2, obs0 m T Y hNA hC t ht.1 ht.2,
    onesInd_path P h1 m t ht.1, zerosInd_path P h1 m t ht.1,
    expect_ones P h1 q m t ht.1, expect_zeros P h1 q m t ht.1]
  unfold errT
  ring

theorem risk_formula (m T : ℕ) (P : Finset ℕ) (h1 : 1 ∈ P) (q : ℕ → ℝ)
    (hq : ∀ u ∈ P, 0 < q u ∧ q u < 1) (Y : Outcomes)
    (hNA : NonAnticipating T Y) (hC : Carryover m T Y) :
    risk m T P q Y = (1 / ((T : ℝ) - m)) ^ 2 *
      ∑ t ∈ Finset.Icc (m + 1) T, ∑ t' ∈ Finset.Icc (m + 1) T, Cterm m P q Y t t' := by
  unfold risk SwitchbackExp.Design.expect
  have h : ∀ c : P → Bool, coinProb P q c * (htEstimator m T P q Y (pathOf P c) - tau m T Y) ^ 2
      = (1 / ((T : ℝ) - m)) ^ 2 * ∑ t ∈ Finset.Icc (m + 1) T, ∑ t' ∈ Finset.Icc (m + 1) T,
          coinProb P q c * (errT m P q Y t c * errT m P q Y t' c) := by
    intro c
    rw [err_eq m T P h1 q Y hNA hC c]
    calc coinProb P q c * ((1 / ((T : ℝ) - m)) * ∑ t ∈ Finset.Icc (m + 1) T, errT m P q Y t c) ^ 2
        = (1 / ((T : ℝ) - m)) ^ 2 * (coinProb P q c *
          ((∑ t ∈ Finset.Icc (m + 1) T, errT m P q Y t c) *
            ∑ t ∈ Finset.Icc (m + 1) T, errT m P q Y t c)) := by ring
      _ = _ := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun c _ => h c, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t' ht' => ?_
  have hmt := (Finset.mem_Icc.1 ht).1
  have hmt' := (Finset.mem_Icc.1 ht').1
  have := E_cov P (detPoints P m t) (detPoints P m t') (detPoints_sub P h1 m t hmt)
    (detPoints_sub P h1 m t' hmt') q hq (Y1 Y t) (Y0 Y t) (Y1 Y t') (Y0 Y t')
  unfold E at this
  unfold errT Cterm overlap
  rw [this]

end SwbAux

namespace SwbAux
open Finset SwitchbackExp.Design

/-- the per-pair risk coefficient at `𝕐⁺` (divided by `B²`) -/
noncomputable def G (q : ℕ → ℝ) (O : Finset ℕ) : ℝ :=
  (∏ u ∈ O, 1 / q u - 1) + (∏ u ∈ O, 1 / (1 - q u) - 1) + 2 * (if O.Nonempty then 1 else 0)

lemma prod_inv_ge_one (O : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ u ∈ O, 0 < f u ∧ f u ≤ 1) :
    1 ≤ ∏ u ∈ O, 1 / f u := by
  rw [Finset.prod_div_distrib, Finset.prod_const_one]
  have hpos : 0 < ∏ u ∈ O, f u := Finset.prod_pos fun u hu => (hf u hu).1
  have hle : ∏ u ∈ O, f u ≤ 1 :=
    Finset.prod_le_one (fun u hu => (hf u hu).1.le) (fun u hu => (hf u hu).2)
  rw [le_div_iff₀ hpos]; linarith

lemma Cterm_plus (m : ℕ) (P : Finset ℕ) (q : ℕ → ℝ) (B : ℝ) (t t' : ℕ) :
    Cterm m P q (Yplus B) t t' = B ^ 2 * G q (overlap P m t t') := by
  unfold Cterm G Y1 Y0 Yplus
  ring

lemma Cterm_le (m T : ℕ) (P : Finset ℕ) (h1 : 1 ∈ P) (q : ℕ → ℝ)
    (hq : ∀ u ∈ P, 0 < q u ∧ q u < 1) (B : ℝ) (hB : 0 < B) (Y : Outcomes)
    (hY : Bounded B T Y) (t t' : ℕ) (ht : t ∈ Finset.Icc (m + 1) T)
    (ht' : t' ∈ Finset.Icc (m + 1) T) :
    Cterm m P q Y t t' ≤ Cterm m P q (Yplus B) t t' := by
  rw [Finset.mem_Icc] at ht ht'
  have hO : overlap P m t t' ⊆ P := fun u hu =>
    detPoints_sub P h1 m t ht.1 (Finset.mem_inter.1 hu).1
  have k1 : 0 ≤ ∏ u ∈ overlap P m t t', 1 / q u - 1 := by
    have := prod_inv_ge_one _ q (fun u hu => ⟨(hq u (hO hu)).1, (hq u (hO hu)).2.le⟩)
    linarith
  have k0 : 0 ≤ ∏ u ∈ overlap P m t t', 1 / (1 - q u) - 1 := by
    have := prod_inv_ge_one _ (fun u => 1 - q u)
      (fun u hu => ⟨by linarith [(hq u (hO hu)).2], by linarith [(hq u (hO hu)).1]⟩)
    linarith
  have k2 : (0:ℝ) ≤ (if (overlap P m t t').Nonempty then 1 else 0) := by
    split_ifs <;> norm_num
  have hab : ∀ x y : ℝ, |x| ≤ B → |y| ≤ B → x * y ≤ B * B := fun x y hx hy =>
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) hB.le)
  have a1 : |Y1 Y t| ≤ B := hY t (by omega) ht.2 _
  have a1' : |Y1 Y t'| ≤ B := hY t' (by omega) ht'.2 _
  have b1 : |Y0 Y t| ≤ B := hY t (by omega) ht.2 _
  have b1' : |Y0 Y t'| ≤ B := hY t' (by omega) ht'.2 _
  unfold Cterm
  have e1 : Y1 (Yplus B) t = B := rfl
  have e2 : Y1 (Yplus B) t' = B := rfl
  have e3 : Y0 (Yplus B) t = B := rfl
  have e4 : Y0 (Yplus B) t' = B := rfl
  rw [e1, e2, e3, e4]
  have := mul_le_mul_of_nonneg_right (hab _ _ a1 a1') k1
  have := mul_le_mul_of_nonneg_right (hab _ _ b1 b1') k0
  have := mul_le_mul_of_nonneg_right (add_le_add (hab _ _ a1 b1') (hab _ _ b1 a1')) k2
  linarith

lemma ec2 (O : Finset ℕ) (q : ℕ → ℝ) (hq : ∀ u ∈ O, 0 < q u ∧ q u < 1) :
    2 * 2 ^ O.card ≤ ∏ u ∈ O, 1 / q u + ∏ u ∈ O, 1 / (1 - q u) ∧
    (∏ u ∈ O, 1 / q u + ∏ u ∈ O, 1 / (1 - q u) = 2 * 2 ^ O.card → ∀ u ∈ O, q u = 1 / 2) := by
  set X := ∏ u ∈ O, 1 / q u with hX
  set Y := ∏ u ∈ O, 1 / (1 - q u) with hY
  have Xpos : 0 < X := Finset.prod_pos fun u hu => by have := (hq u hu).1; positivity
  have Ypos : 0 < Y := Finset.prod_pos fun u hu => by
    have := (hq u hu).2; have : 0 < 1 - q u := by linarith
    positivity
  have hXY : X * Y = ∏ u ∈ O, 1 / (q u * (1 - q u)) := by
    rw [hX, hY, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun u _ => ?_
    rw [one_div_mul_one_div]
  have h4 : ∀ u ∈ O, (4:ℝ) ≤ 1 / (q u * (1 - q u)) := fun u hu => by
    have h0 := (hq u hu).1; have h1 := (hq u hu).2
    have hp : 0 < q u * (1 - q u) := mul_pos h0 (by linarith)
    rw [le_div_iff₀ hp]; nlinarith [sq_nonneg (q u - 1/2)]
  have hpow : (∏ u ∈ O, (4:ℝ)) = 2 ^ O.card * 2 ^ O.card := by
    rw [Finset.prod_const, ← mul_pow]; norm_num
  have hge : 2 ^ O.card * 2 ^ O.card ≤ X * Y := by
    rw [hXY, ← hpow]
    exact Finset.prod_le_prod (fun _ _ => by norm_num) h4
  have hp2 : (0:ℝ) < 2 ^ O.card := by positivity
  refine ⟨?_, ?_⟩
  · nlinarith [sq_nonneg (X - Y)]
  · intro heq
    by_contra hne
    push Not at hne
    obtain ⟨u, hu, hqu⟩ := hne
    have hlt : 2 ^ O.card * 2 ^ O.card < X * Y := by
      rw [hXY, ← hpow]
      refine Finset.prod_lt_prod (fun _ _ => by norm_num) h4 ⟨u, hu, ?_⟩
      have h0 := (hq u hu).1; have h1 := (hq u hu).2
      have hp : 0 < q u * (1 - q u) := mul_pos h0 (by linarith)
      rw [lt_div_iff₀ hp]
      have : 0 < (q u - 1/2) ^ 2 := by
        have : q u - 1/2 ≠ 0 := sub_ne_zero.2 hqu
        positivity
      nlinarith
    nlinarith [sq_nonneg (X - Y)]

lemma G_ge (O : Finset ℕ) (q : ℕ → ℝ) (hq : ∀ u ∈ O, 0 < q u ∧ q u < 1) :
    G half O ≤ G q O ∧ (G q O = G half O → ∀ u ∈ O, q u = 1 / 2) := by
  have hh : ∀ u ∈ O, 0 < half u ∧ half u < 1 := fun u _ => by unfold half; norm_num
  have e1 : ∏ u ∈ O, 1 / half u = 2 ^ O.card := by
    unfold half; rw [Finset.prod_const]; norm_num
  have e2 : ∏ u ∈ O, 1 / (1 - half u) = 2 ^ O.card := by
    unfold half; rw [Finset.prod_const]; norm_num
  obtain ⟨h1, h2⟩ := ec2 O q hq
  unfold G
  rw [e1, e2]
  refine ⟨by linarith, fun heq => h2 (by linarith)⟩

lemma G_half_ge (O : Finset ℕ) : 4 * (O.card : ℝ) ≤ G half O ∧ (O.card ≤ 2 → G half O = 4 * O.card) := by
  have e1 : ∏ u ∈ O, 1 / half u = 2 ^ O.card := by
    unfold half; rw [Finset.prod_const]; norm_num
  have e2 : ∏ u ∈ O, 1 / (1 - half u) = 2 ^ O.card := by
    unfold half; rw [Finset.prod_const]; norm_num
  unfold G
  rw [e1, e2]
  rcases Nat.eq_zero_or_pos O.card with h0 | hpos
  · have : ¬ O.Nonempty := by
      rw [Finset.not_nonempty_iff_eq_empty]; exact Finset.card_eq_zero.1 h0
    rw [if_neg this, h0]; norm_num
  · have hne : O.Nonempty := Finset.card_pos.1 hpos
    rw [if_pos hne]
    refine ⟨?_, ?_⟩
    · have hlt : O.card - 1 < 2 ^ (O.card - 1) := Nat.lt_two_pow_self
      have hc : O.card = (O.card - 1) + 1 := by omega
      have : (O.card : ℝ) ≤ 2 ^ (O.card - 1) := by exact_mod_cast (by omega : O.card ≤ 2 ^ (O.card - 1))
      rw [hc, pow_succ]
      push_cast
      have : ((O.card - 1 : ℕ) : ℝ) + 1 ≤ 2 ^ (O.card - 1) := by
        have := (by omega : O.card - 1 + 1 ≤ 2 ^ (O.card - 1))
        exact_mod_cast this
      nlinarith
    · intro h2
      interval_cases h : O.card <;> norm_num

end SwbAux

namespace SwbAux
open Finset SwitchbackExp.Design

/-- the next randomization point after `p` (or `T+1`) -/
def nxt (P : Finset ℕ) (T p : ℕ) : ℕ :=
  if h : (P.filter (p < ·)).Nonempty then (P.filter (p < ·)).min' h else T + 1

lemma nxt_spec (P : Finset ℕ) (T : ℕ) (hP : P ⊆ Finset.Icc 1 T) (p : ℕ) (hp : p ≤ T) :
    p < nxt P T p ∧ nxt P T p ≤ T + 1 ∧ (∀ x ∈ P, p < x → nxt P T p ≤ x) ∧
      (nxt P T p ≤ T → nxt P T p ∈ P) := by
  unfold nxt
  split_ifs with h
  · have hm := Finset.min'_mem _ h
    simp only [Finset.mem_filter] at hm
    have hT := (Finset.mem_Icc.1 (hP hm.1)).2
    refine ⟨hm.2, by omega, fun x hx hpx => Finset.min'_le _ _ (by simp [hx, hpx]),
      fun _ => hm.1⟩
  · refine ⟨by omega, le_rfl, fun x hx hpx => ?_, fun h' => by omega⟩
    exact absurd ⟨x, by simp [hx, hpx]⟩ h

lemma det_iff (P : Finset ℕ) (T : ℕ) (h1 : 1 ∈ P) (hP : P ⊆ Finset.Icc 1 T) (p : ℕ) (hp : p ∈ P)
    (s : ℕ) (hs1 : 1 ≤ s) (hsT : s ≤ T) :
    detPoint P s = p ↔ p ≤ s ∧ s < nxt P T p := by
  have hpT := (Finset.mem_Icc.1 (hP hp)).2
  obtain ⟨n1, n2, n3, n4⟩ := nxt_spec P T hP p hpT
  obtain ⟨d1, d2, d3⟩ := det_spec P h1 s hs1
  constructor
  · rintro rfl
    refine ⟨d2, ?_⟩
    by_contra hc
    push Not at hc
    have := d3 _ (n4 (by omega)) hc
    omega
  · rintro ⟨hps, hsn⟩
    have h3 := d3 p hp hps
    by_contra hne
    have hlt : p < detPoint P s := lt_of_le_of_ne h3 (Ne.symm hne)
    have := n3 _ d1 hlt
    omega

lemma mem_D_iff (P : Finset ℕ) (m T : ℕ) (h1 : 1 ∈ P) (hP : P ⊆ Finset.Icc 1 T) (p : ℕ)
    (hp : p ∈ P) (t : ℕ) (ht1 : m + 1 ≤ t) (htT : t ≤ T) :
    p ∈ detPoints P m t ↔ p ≤ t ∧ t < nxt P T p + m := by
  have hpT := (Finset.mem_Icc.1 (hP hp)).2
  have hp1 := (Finset.mem_Icc.1 (hP hp)).1
  obtain ⟨n1, n2, n3, n4⟩ := nxt_spec P T hP p hpT
  simp only [detPoints, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨s, ⟨hs1, hs2⟩, hsp⟩
    have := (det_iff P T h1 hP p hp s (by omega) (by omega)).1 hsp
    omega
  · rintro ⟨h1', h2'⟩
    refine ⟨max p (t - m), ⟨by omega, by omega⟩, ?_⟩
    exact (det_iff P T h1 hP p hp _ (by omega) (by omega)).2 ⟨by omega, by omega⟩

/-- `N_p`: number of periods `t` whose determining set contains `p` -/
def Ncount (P : Finset ℕ) (m T p : ℕ) : ℕ :=
  ((Finset.Icc (m + 1) T).filter (fun t => p ∈ detPoints P m t)).card

/-- `d_p`: clamped epoch length -/
def dcount (P : Finset ℕ) (m T p : ℕ) : ℕ :=
  ((Finset.Ico (m + 1) (T - m + 1)).filter (fun x => detPoint P x = p)).card

lemma Ncount_eq (P : Finset ℕ) (m T : ℕ) (h1 : 1 ∈ P) (hP : P ⊆ Finset.Icc 1 T) (p : ℕ)
    (hp : p ∈ P) :
    Ncount P m T p = min (nxt P T p + m - 1) T + 1 - max p (m + 1) := by
  unfold Ncount
  have : (Finset.Icc (m + 1) T).filter (fun t => p ∈ detPoints P m t) =
      Finset.Icc (max p (m + 1)) (min (nxt P T p + m - 1) T) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨a, b⟩, c⟩
      rw [mem_D_iff P m T h1 hP p hp t a b] at c
      omega
    · intro h
      have a : m + 1 ≤ t := by omega
      have b : t ≤ T := by omega
      refine ⟨⟨a, b⟩, ?_⟩
      rw [mem_D_iff P m T h1 hP p hp t a b]
      omega
  rw [this, Nat.card_Icc]

lemma dcount_eq (P : Finset ℕ) (m T : ℕ) (h1 : 1 ∈ P) (hP : P ⊆ Finset.Icc 1 T) (p : ℕ)
    (hp : p ∈ P) :
    dcount P m T p = min (nxt P T p) (T - m + 1) - max p (m + 1) := by
  unfold dcount
  have : (Finset.Ico (m + 1) (T - m + 1)).filter (fun x => detPoint P x = p) =
      Finset.Ico (max p (m + 1)) (min (nxt P T p) (T - m + 1)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨a, b⟩, c⟩
      rw [det_iff P T h1 hP p hp x (by omega) (by omega)] at c
      omega
    · intro h
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [det_iff P T h1 hP p hp x (by omega) (by omega)]
      omega
  rw [this, Nat.card_Ico]

lemma sum_dcount (P : Finset ℕ) (m T : ℕ) (h1 : 1 ∈ P) :
    ∑ p ∈ P, dcount P m T p = T - 2 * m := by
  unfold dcount
  rw [← Finset.card_eq_sum_card_fiberwise (f := detPoint P)
    (s := Finset.Ico (m + 1) (T - m + 1)) (t := P)]
  · rw [Nat.card_Ico]; omega
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_Ico] at hx
    rw [Finset.mem_coe]
    exact (det_spec P h1 x (by omega)).1

lemma sum_overlap (P : Finset ℕ) (m T : ℕ) (h1 : 1 ∈ P) :
    ∑ t ∈ Finset.Icc (m + 1) T, ∑ t' ∈ Finset.Icc (m + 1) T, (overlap P m t t').card =
      ∑ p ∈ P, Ncount P m T p ^ 2 := by
  have hc : ∀ t ∈ Finset.Icc (m + 1) T, ∀ t' ∈ Finset.Icc (m + 1) T,
      (overlap P m t t').card = ∑ p ∈ P, (if p ∈ detPoints P m t then 1 else 0) *
        (if p ∈ detPoints P m t' then 1 else 0) := by
    intro t ht t' _
    have hsub : overlap P m t t' ⊆ P := fun u hu =>
      detPoints_sub P h1 m t (Finset.mem_Icc.1 ht).1 (Finset.mem_inter.1 hu).1
    have : overlap P m t t' = P.filter (fun p => p ∈ detPoints P m t ∧ p ∈ detPoints P m t') := by
      ext u
      simp only [overlap, Finset.mem_inter, Finset.mem_filter]
      constructor
      · intro h; exact ⟨hsub (Finset.mem_inter.2 h), h⟩
      · intro h; exact h.2
    rw [this, Finset.card_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun t' ht' => hc t ht t' ht']
  have hN : ∀ p ∈ P, Ncount P m T p ^ 2 = ∑ t ∈ Finset.Icc (m + 1) T, ∑ t' ∈ Finset.Icc (m + 1) T,
      (if p ∈ detPoints P m t then 1 else 0) * (if p ∈ detPoints P m t' then 1 else 0) := by
    intro p _
    unfold Ncount
    rw [Finset.card_filter, sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl hN]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]

lemma arith (m T p e : ℕ) (hp1 : 1 ≤ p) (hpe : p < e) (heT : e ≤ T + 1) (hpT : p ≤ T)
    (hmT : m + 1 ≤ T) (h2m : 2 * m ≤ T) :
    4 * m * (min e (T - m + 1) - max p (m + 1)) ≤ (min (e + m - 1) T + 1 - max p (m + 1)) ^ 2 ∧
    ((min (e + m - 1) T + 1 - max p (m + 1)) ^ 2 = 4 * m * (min e (T - m + 1) - max p (m + 1)) →
      m + 1 ≤ e ∧ p ≤ T - m + 1 ∧ min e (T - m + 1) - max p (m + 1) = m) := by
  have a1 : min (e + m - 1) T ≤ e + m - 1 := min_le_left _ _
  have a2 : min (e + m - 1) T ≤ T := min_le_right _ _
  have a3 := min_choice (e + m - 1) T
  have b1 : min e (T - m + 1) ≤ e := min_le_left _ _
  have b2 : min e (T - m + 1) ≤ T - m + 1 := min_le_right _ _
  have b3 := min_choice e (T - m + 1)
  have c1 : p ≤ max p (m + 1) := le_max_left _ _
  have c2 : m + 1 ≤ max p (m + 1) := le_max_right _ _
  have c3 := max_choice p (m + 1)
  generalize min (e + m - 1) T = A at *
  generalize min e (T - m + 1) = Bm at *
  generalize max p (m + 1) = C at *
  have hN1 : 1 ≤ A + 1 - C := by omega
  by_cases hc : m + 1 ≤ e ∧ p ≤ T - m + 1
  · have hNd : A + 1 - C = (Bm - C) + m := by omega
    rw [hNd]
    refine ⟨?_, fun h => ⟨hc.1, hc.2, ?_⟩⟩
    · generalize Bm - C = d
      zify; nlinarith [sq_nonneg ((d : ℤ) - m)]
    · generalize Bm - C = d at h ⊢
      zify at h ⊢; nlinarith [sq_nonneg ((d : ℤ) - m)]
  · have hd0 : Bm - C = 0 := by omega
    rw [hd0]
    refine ⟨by simp, fun h => ?_⟩
    have : 1 ≤ (A + 1 - C) ^ 2 := Nat.one_le_pow _ _ hN1
    rw [mul_zero] at h
    omega

end SwbAux

namespace SwbAux
open Finset SwitchbackExp.Design

noncomputable def F (m T : ℕ) (P : Finset ℕ) (q : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.Icc (m + 1) T, ∑ t' ∈ Finset.Icc (m + 1) T, G q (overlap P m t t')

lemma admissible_plus (m T : ℕ) (B : ℝ) (hB : 0 < B) : Admissible m T B (Yplus B) := by
  refine ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ => ?_⟩
  simp [Yplus, abs_of_pos hB]

lemma risk_plus (m T : ℕ) (P : Finset ℕ) (h1 : 1 ∈ P) (q : ℕ → ℝ)
    (hq : ∀ u ∈ P, 0 < q u ∧ q u < 1) (B : ℝ) :
    risk m T P q (Yplus B) = (1 / ((T : ℝ) - m)) ^ 2 * B ^ 2 * F m T P q := by
  rw [risk_formula m T P h1 q hq (Yplus B) (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)]
  unfold F
  simp only [Cterm_plus, ← Finset.mul_sum]
  ring

lemma risk_le_plus (m T : ℕ) (P : Finset ℕ) (h1 : 1 ∈ P) (q : ℕ → ℝ)
    (hq : ∀ u ∈ P, 0 < q u ∧ q u < 1) (B : ℝ) (hB : 0 < B) (Y : Outcomes)
    (hY : Admissible m T B Y) :
    risk m T P q Y ≤ risk m T P q (Yplus B) := by
  rw [risk_formula m T P h1 q hq Y hY.1 hY.2.1,
    risk_formula m T P h1 q hq (Yplus B) (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun t' ht' =>
    Cterm_le m T P h1 q hq B hB Y hY.2.2 t t' ht ht'

lemma F_half_le (m T : ℕ) (P : Finset ℕ) (hP1 : 1 ∈ P) (hP : P ⊆ Finset.Icc 1 T) (q : ℕ → ℝ)
    (hq : ∀ u ∈ P, 0 < q u ∧ q u < 1) (hmT : m + 1 ≤ T) :
    F m T P half ≤ F m T P q ∧ (F m T P q = F m T P half → ∀ u ∈ P, q u = 1 / 2) := by
  have hO : ∀ t ∈ Finset.Icc (m + 1) T, ∀ t', overlap P m t t' ⊆ P := fun t ht t' u hu =>
    detPoints_sub P hP1 m t (Finset.mem_Icc.1 ht).1 (Finset.mem_inter.1 hu).1
  have hle : ∀ t ∈ Finset.Icc (m + 1) T, ∀ t' ∈ Finset.Icc (m + 1) T,
      G half (overlap P m t t') ≤ G q (overlap P m t t') := fun t ht t' _ =>
    (G_ge _ q (fun u hu => hq u (hO t ht t' hu))).1
  refine ⟨Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun t' ht' => hle t ht t' ht', ?_⟩
  intro heq u hu
  have hinner := (Finset.sum_eq_sum_iff_of_le (fun t ht =>
    Finset.sum_le_sum fun t' ht' => hle t ht t' ht')).1 heq.symm
  have huT := (Finset.mem_Icc.1 (hP hu)).2
  have hu1 := (Finset.mem_Icc.1 (hP hu)).1
  set t0 := max u (m + 1) with ht0
  have ht0m : t0 ∈ Finset.Icc (m + 1) T := Finset.mem_Icc.2 ⟨le_max_right _ _, max_le huT hmT⟩
  have hterm := (Finset.sum_eq_sum_iff_of_le (fun t' ht' => hle t0 ht0m t' ht')).1
    (hinner t0 ht0m) t0 ht0m
  have hn := nxt_spec P T hP u huT
  have huD : u ∈ detPoints P m t0 := by
    rw [mem_D_iff P m T hP1 hP u hu t0 (le_max_right _ _) (max_le huT hmT)]
    omega
  have := (G_ge _ q (fun v hv => hq v (hO t0 ht0m t0 hv))).2 hterm.symm
  exact this u (by simp [overlap, huD])

lemma F_half_ge_N (m T : ℕ) (P : Finset ℕ) (hP1 : 1 ∈ P) :
    4 * ((∑ p ∈ P, Ncount P m T p ^ 2 : ℕ) : ℝ) ≤ F m T P half ∧
    ((∀ t ∈ Finset.Icc (m + 1) T, (detPoints P m t).card ≤ 2) →
      F m T P half = 4 * ((∑ p ∈ P, Ncount P m T p ^ 2 : ℕ) : ℝ)) := by
  rw [← sum_overlap P m T hP1]
  push_cast
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum]
  unfold F
  refine ⟨Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun t' _ =>
    (G_half_ge _).1, fun h2 => ?_⟩
  refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun t' _ => ?_
  apply (G_half_ge _).2
  exact le_trans (Finset.card_le_card Finset.inter_subset_left) (h2 t ht)

/-- per-point lower bound, summed -/
lemma sumN_ge (m T : ℕ) (P : Finset ℕ) (hP1 : 1 ∈ P) (hP : P ⊆ Finset.Icc 1 T)
    (hmT : m + 1 ≤ T) (h2m : 2 * m ≤ T) :
    4 * m * (T - 2 * m) ≤ ∑ p ∈ P, Ncount P m T p ^ 2 ∧
    (∑ p ∈ P, Ncount P m T p ^ 2 ≤ 4 * m * (T - 2 * m) →
      ∀ p ∈ P, m + 1 ≤ nxt P T p ∧ p ≤ T - m + 1 ∧
        min (nxt P T p) (T - m + 1) - max p (m + 1) = m) := by
  have hpt : ∀ p ∈ P, 4 * m * dcount P m T p ≤ Ncount P m T p ^ 2 ∧
      (Ncount P m T p ^ 2 = 4 * m * dcount P m T p → m + 1 ≤ nxt P T p ∧ p ≤ T - m + 1 ∧
        min (nxt P T p) (T - m + 1) - max p (m + 1) = m) := by
    intro p hp
    have hpT := (Finset.mem_Icc.1 (hP hp)).2
    have hp1 := (Finset.mem_Icc.1 (hP hp)).1
    obtain ⟨n1, n2, _, _⟩ := nxt_spec P T hP p hpT
    rw [Ncount_eq P m T hP1 hP p hp, dcount_eq P m T hP1 hP p hp]
    exact arith m T p (nxt P T p) hp1 n1 n2 hpT hmT h2m
  have hsum : 4 * m * (T - 2 * m) = ∑ p ∈ P, 4 * m * dcount P m T p := by
    rw [← Finset.mul_sum, sum_dcount P m T hP1]
  refine ⟨?_, fun hle => ?_⟩
  · rw [hsum]; exact Finset.sum_le_sum fun p hp => (hpt p hp).1
  · rw [hsum] at hle
    have := (Finset.sum_eq_sum_iff_of_le fun p hp => (hpt p hp).1).1
      (le_antisymm (Finset.sum_le_sum fun p hp => (hpt p hp).1) hle)
    exact fun p hp => (hpt p hp).2 (this p hp).symm

end SwbAux

namespace SwbAux
open Finset SwitchbackExp.Design

lemma mem_opt (m n x : ℕ) :
    x ∈ optPoints m n ↔ x = 1 ∨ ∃ k, 2 ≤ k ∧ k ≤ n - 2 ∧ x = k * m + 1 := by
  simp only [optPoints, Finset.mem_insert, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro (h | ⟨k, ⟨h1, h2⟩, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨k, h1, h2, h3.symm⟩
  · rintro (h | ⟨k, h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨k, ⟨h1, h2⟩, h3.symm⟩

lemma opt_spacing (m n : ℕ) (hm : 1 ≤ m) (x y : ℕ) (hx : x ∈ optPoints m n)
    (hy : y ∈ optPoints m n) (hxy : x < y) : x + m ≤ y := by
  rw [mem_opt] at hx hy
  rcases hx with rfl | ⟨k, hk2, hkn, rfl⟩ <;> rcases hy with rfl | ⟨j, hj2, hjn, rfl⟩
  · omega
  · have := Nat.mul_le_mul_right m hj2
    omega
  · omega
  · have hkj : k < j := by
      by_contra h
      push Not at h
      have := Nat.mul_le_mul_right m h
      omega
    have := Nat.mul_le_mul_right m (show k + 1 ≤ j by omega)
    rw [add_mul, one_mul] at this
    omega

lemma opt_sub (m n T : ℕ) (hm : 1 ≤ m) (hn : 4 ≤ n) (hT : T = n * m) :
    optPoints m n ⊆ Finset.Icc 1 T := by
  intro x hx
  rw [mem_opt] at hx
  rw [Finset.mem_Icc]
  rcases hx with rfl | ⟨k, hk2, hkn, rfl⟩
  · refine ⟨le_rfl, ?_⟩
    have := Nat.mul_le_mul_right m hn
    rw [hT]; omega
  · refine ⟨by omega, ?_⟩
    have h1 := Nat.mul_le_mul_right m (show k + 1 ≤ n by omega)
    rw [add_mul, one_mul] at h1
    rw [hT]; omega

lemma opt_card (m n : ℕ) (hm : 1 ≤ m) (hn : 4 ≤ n) : (optPoints m n).card = n - 2 := by
  unfold optPoints
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective]
    · rw [Nat.card_Icc]; omega
    · intro a b h
      simp only at h
      exact Nat.eq_of_mul_eq_mul_right hm (by omega)
  · simp only [Finset.mem_image, Finset.mem_Icc, not_exists, not_and]
    intro k hk h
    have := Nat.mul_le_mul_right m hk.1
    omega

lemma opt_regular (m n T : ℕ) (hm : 1 ≤ m) (hn : 4 ≤ n) (hT : T = n * m) :
    IsRegularPoints T (optPoints m n) := by
  refine ⟨(mem_opt m n 1).2 (Or.inl rfl), opt_sub m n T hm hn hT, ?_⟩
  rw [opt_card m n hm hn]; omega

lemma nxt_char (P : Finset ℕ) (T p v : ℕ) (hv : v ∈ P) (hpv : p < v)
    (hmin : ∀ x ∈ P, p < x → v ≤ x) : nxt P T p = v := by
  unfold nxt
  have hne : (P.filter (p < ·)).Nonempty := ⟨v, by simp [hv, hpv]⟩
  rw [dif_pos hne]
  apply le_antisymm
  · exact Finset.min'_le _ _ (by simp [hv, hpv])
  · apply Finset.le_min'
    intro y hy
    simp only [Finset.mem_filter] at hy
    exact hmin y hy.1 hy.2

lemma nxt_none (P : Finset ℕ) (T p : ℕ) (hall : ∀ x ∈ P, x ≤ p) : nxt P T p = T + 1 := by
  unfold nxt
  have hne : ¬ (P.filter (p < ·)).Nonempty := by
    rintro ⟨x, hx⟩
    simp only [Finset.mem_filter] at hx
    have := hall x hx.1
    omega
  rw [dif_neg hne]

lemma opt_N (m n T : ℕ) (hm : 1 ≤ m) (hn : 4 ≤ n) (hT : T = n * m) (p : ℕ)
    (hp : p ∈ optPoints m n) : Ncount (optPoints m n) m T p = 2 * m := by
  have hreg := opt_regular m n T hm hn hT
  rw [Ncount_eq _ m T hreg.1 hreg.2.1 p hp]
  have hT4 : 4 * m ≤ T := by rw [hT]; exact Nat.mul_le_mul_right m hn
  have hTn : (n - 2) * m + 2 * m = T := by
    rw [← add_mul, hT]; congr 1; omega
  have hp' := hp
  rw [mem_opt] at hp'
  rcases hp' with rfl | ⟨k, hk2, hkn, rfl⟩
  · have : nxt (optPoints m n) T 1 = 2 * m + 1 := by
      apply nxt_char
      · rw [mem_opt]; exact Or.inr ⟨2, le_rfl, by omega, rfl⟩
      · omega
      · intro x hx h1x
        have := opt_spacing m n hm 1 x hreg.1 hx h1x
        rw [mem_opt] at hx
        rcases hx with rfl | ⟨j, hj2, _, rfl⟩
        · omega
        · have := Nat.mul_le_mul_right m hj2; omega
    rw [this]; omega
  · by_cases hlast : k = n - 2
    · subst hlast
      have : nxt (optPoints m n) T ((n - 2) * m + 1) = T + 1 := by
        apply nxt_none
        intro x hx
        rw [mem_opt] at hx
        rcases hx with rfl | ⟨j, _, hjn, rfl⟩
        · omega
        · have := Nat.mul_le_mul_right m hjn; omega
      rw [this]
      have := Nat.mul_le_mul_right m hk2
      omega
    · have : nxt (optPoints m n) T (k * m + 1) = (k + 1) * m + 1 := by
        apply nxt_char
        · rw [mem_opt]; exact Or.inr ⟨k + 1, by omega, by omega, rfl⟩
        · rw [add_mul, one_mul]; omega
        · intro x hx hkx
          have := opt_spacing m n hm _ x hp hx hkx
          rw [add_mul, one_mul]; omega
      rw [this, add_mul, one_mul]
      have h1 := Nat.mul_le_mul_right m (show k + 2 ≤ n by omega)
      rw [add_mul] at h1
      have h2 := Nat.mul_le_mul_right m hk2
      omega

lemma opt_D_card (m n T : ℕ) (hm : 1 ≤ m) (hn : 4 ≤ n) (hT : T = n * m) (t : ℕ)
    (ht : m + 1 ≤ t) : (detPoints (optPoints m n) m t).card ≤ 2 := by
  have hreg := opt_regular m n T hm hn hT
  set P := optPoints m n with hPdef
  have hsub : detPoints P m t ⊆
      insert (detPoint P (t - m)) (P.filter (fun x => t - m < x ∧ x ≤ t)) := by
    intro x hx
    simp only [detPoints, Finset.mem_image, Finset.mem_Icc] at hx
    obtain ⟨s, ⟨hs1, hs2⟩, rfl⟩ := hx
    by_cases he : detPoint P s = detPoint P (t - m)
    · rw [he]; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      obtain ⟨d1, d2, d3⟩ := det_spec P hreg.1 s (by omega)
      rw [Finset.mem_filter]
      refine ⟨d1, ?_, by omega⟩
      by_contra hc
      push Not at hc
      have h1 := (det_spec P hreg.1 (t - m) (by omega)).2.2 _ d1 hc
      have h2 := det_mono P hs1
      exact he (le_antisymm h2 h1).symm
  have hf : (P.filter (fun x => t - m < x ∧ x ≤ t)).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    rcases lt_trichotomy a b with h | h | h
    · have := opt_spacing m n hm a b ha.1 hb.1 h; omega
    · exact h
    · have := opt_spacing m n hm b a hb.1 ha.1 h; omega
  calc (detPoints P m t).card ≤ (insert (detPoint P (t - m))
        (P.filter (fun x => t - m < x ∧ x ≤ t))).card := Finset.card_le_card hsub
    _ ≤ (P.filter (fun x => t - m < x ∧ x ≤ t)).card + 1 := Finset.card_insert_le _ _
    _ ≤ 2 := by omega

/-- the value of the objective at `𝕋*` -/
lemma opt_F (m n T : ℕ) (hm : 1 ≤ m) (hn : 4 ≤ n) (hT : T = n * m) :
    F m T (optPoints m n) half = 16 * (m : ℝ) * ((T - 2 * m : ℕ) : ℝ) := by
  have hreg := opt_regular m n T hm hn hT
  rw [(F_half_ge_N m T _ hreg.1).2 (fun t ht => opt_D_card m n T hm hn hT t
    (Finset.mem_Icc.1 ht).1)]
  rw [Finset.sum_congr rfl fun p hp => by rw [opt_N m n T hm hn hT p hp]]
  rw [Finset.sum_const, opt_card m n hm hn, smul_eq_mul]
  have : T - 2 * m = (n - 2) * m := by
    have hTn : (n - 2) * m + 2 * m = T := by
      rw [← add_mul, hT]; congr 1; omega
    omega
  rw [this]
  push_cast
  ring

/-- uniqueness: the equality conditions force `𝕋 = 𝕋*` -/
lemma opt_unique (m n T : ℕ) (hm : 1 ≤ m) (hn : 4 ≤ n) (hT : T = n * m) (P : Finset ℕ)
    (hP : IsRegularPoints T P)
    (hc : ∀ p ∈ P, m + 1 ≤ nxt P T p ∧ p ≤ T - m + 1 ∧
        min (nxt P T p) (T - m + 1) - max p (m + 1) = m) :
    P = optPoints m n := by
  have hT4 : 4 * m ≤ T := by rw [hT]; exact Nat.mul_le_mul_right m hn
  have hTn : (n - 2) * m + 2 * m = T := by
    rw [← add_mul, hT]; congr 1; omega
  -- cardinality
  have hcard : P.card = n - 2 := by
    have hs := sum_dcount P m T hP.1
    rw [Finset.sum_congr rfl (fun p hp => (dcount_eq P m T hP.1 hP.2.1 p hp).trans (hc p hp).2.2 :
      ∀ p ∈ P, dcount P m T p = m)] at hs
    rw [Finset.sum_const, smul_eq_mul] at hs
    apply Nat.eq_of_mul_eq_mul_right hm
    omega
  -- 𝕋* ⊆ P
  have hk : ∀ k, 2 ≤ k → k ≤ n - 2 → k * m + 1 ∈ P := by
    intro k hk2
    induction k, hk2 using Nat.le_induction with
    | base =>
      intro _
      obtain ⟨c1, c2, c3⟩ := hc 1 hP.1
      have hsp := nxt_spec P T hP.2.1 1 (by omega)
      have h21 : nxt P T 1 = 2 * m + 1 := by omega
      have := hsp.2.2.2 (by omega)
      rw [h21] at this
      exact this
    | succ k hk2 ih =>
      intro hkn
      have hmem := ih (by omega)
      obtain ⟨c1, c2, c3⟩ := hc _ hmem
      have hkm := Nat.mul_le_mul_right m (show k + 1 ≤ n - 2 by omega)
      rw [add_mul, one_mul] at hkm
      have hk1 := Nat.mul_le_mul_right m (show 1 ≤ k by omega)
      rw [one_mul] at hk1
      have hsp := nxt_spec P T hP.2.1 (k * m + 1) (by omega)
      have : nxt P T (k * m + 1) = k * m + m + 1 := by omega
      rw [add_mul, one_mul, ← this]
      exact hsp.2.2.2 (by omega)
  have hsub : optPoints m n ⊆ P := by
    intro x hx
    rw [mem_opt] at hx
    rcases hx with rfl | ⟨k, hk2, hkn, rfl⟩
    · exact hP.1
    · exact hk k hk2 hkn
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, opt_card m n hm hn])).symm

end SwbAux

namespace SwbAux
open Finset SwitchbackExp.Design

lemma errTerm_path (m : ℕ) (P : Finset ℕ) (h1 : 1 ∈ P) (q : ℕ → ℝ) (Y : Outcomes) (t : ℕ)
    (ht : m + 1 ≤ t) (c : P → Bool) :
    errTerm m P q Y t (pathOf P c) = errT m P q Y t c := by
  unfold errTerm errT
  rw [onesInd_path P h1 m t ht, zerosInd_path P h1 m t ht]
  rw [Finset.prod_div_distrib, Finset.prod_const_one, Finset.prod_div_distrib,
    Finset.prod_const_one]
  ring

lemma expect_eq_E (P : Finset ℕ) (q : ℕ → ℝ) (g : Path → ℝ) :
    SwitchbackExp.Design.expect P q g = E P q (fun c => g (pathOf P c)) := rfl

lemma ec4_gen (m : ℕ) (P : Finset ℕ) (h1 : 1 ∈ P) (q : ℕ → ℝ)
    (hq : ∀ u ∈ P, 0 < q u ∧ q u < 1) (Y : Outcomes) (t t' : ℕ) (ht : m + 1 ≤ t)
    (ht' : m + 1 ≤ t') :
    SwitchbackExp.Design.expect P q (fun w => errTerm m P q Y t w * errTerm m P q Y t' w) =
      Y1 Y t * Y1 Y t' * (∏ u ∈ overlap P m t t', 1 / q u - 1)
      + Y0 Y t * Y0 Y t' * (∏ u ∈ overlap P m t t', 1 / (1 - q u) - 1)
      + (Y1 Y t * Y0 Y t' + Y0 Y t * Y1 Y t') *
        (if (overlap P m t t').Nonempty then 1 else 0) := by
  rw [expect_eq_E]
  simp_rw [errTerm_path m P h1 q Y t ht, errTerm_path m P h1 q Y t' ht']
  unfold errT overlap
  exact E_cov P _ _ (detPoints_sub P h1 m t ht) (detPoints_sub P h1 m t' ht') q hq _ _ _ _

lemma self_mem_D (P : Finset ℕ) (h1 : 1 ∈ P) (m t : ℕ) (ht : m + 1 ≤ t) :
    (detPoints P m t).Nonempty :=
  ⟨detPoint P t, Finset.mem_image.2 ⟨t, Finset.mem_Icc.2 ⟨by omega, le_rfl⟩, rfl⟩⟩

lemma ec3_gen (m : ℕ) (P : Finset ℕ) (h1 : 1 ∈ P) (q : ℕ → ℝ)
    (hq : ∀ u ∈ P, 0 < q u ∧ q u < 1) (Y : Outcomes) (t : ℕ) (ht : m + 1 ≤ t) :
    SwitchbackExp.Design.expect P q (fun w => errTerm m P q Y t w ^ 2)
      = (∏ u ∈ detPoints P m t, 1 / q u - 1) * Y1 Y t ^ 2 + 2 * Y1 Y t * Y0 Y t
        + (∏ u ∈ detPoints P m t, 1 / (1 - q u) - 1) * Y0 Y t ^ 2 := by
  simp_rw [sq]
  rw [ec4_gen m P h1 q hq Y t t ht ht]
  unfold overlap
  rw [Finset.inter_self, if_pos (self_mem_D P h1 m t ht)]
  ring

lemma prop1_gen (m T : ℕ) (P : Finset ℕ) (h1 : 1 ∈ P) (q : ℕ → ℝ)
    (hq : ∀ u ∈ P, 0 < q u ∧ q u < 1) (Y : Outcomes)
    (hNA : NonAnticipating T Y) (hC : Carryover m T Y) :
    SwitchbackExp.Design.expect P q (htEstimator m T P q Y) = tau m T Y := by
  rw [expect_eq_E]
  have h : ∀ c : P → Bool, htEstimator m T P q Y (pathOf P c) =
      tau m T Y + (1 / ((T : ℝ) - m)) * ∑ t ∈ Finset.Icc (m + 1) T, errT m P q Y t c := by
    intro c
    rw [← err_eq m T P h1 q Y hNA hC c]; ring
  simp_rw [h]
  have hz : ∀ t ∈ Finset.Icc (m + 1) T, E P q (fun c => errT m P q Y t c) = 0 := by
    intro t ht
    have hmt := (Finset.mem_Icc.1 ht).1
    have hD := detPoints_sub P h1 m t hmt
    have pos1 : 0 < ∏ u ∈ detPoints P m t, q u := Finset.prod_pos fun u hu => (hq u (hD hu)).1
    have pos0 : 0 < ∏ u ∈ detPoints P m t, (1 - q u) :=
      Finset.prod_pos fun u hu => by linarith [(hq u (hD hu)).2]
    have e1 := E_ind1 P _ hD q
    have e0 := E_ind0 P _ hD q
    have eone := E_one P q
    unfold E at e1 e0 eone ⊢
    unfold errT
    have key : ∀ c : P → Bool, coinProb P q c *
        (Y1 Y t * (ind1 P (detPoints P m t) c / ∏ u ∈ detPoints P m t, q u - 1) -
          Y0 Y t * (ind0 P (detPoints P m t) c / ∏ u ∈ detPoints P m t, (1 - q u) - 1)) =
        Y1 Y t / (∏ u ∈ detPoints P m t, q u) * (coinProb P q c * ind1 P (detPoints P m t) c)
        - Y0 Y t / (∏ u ∈ detPoints P m t, (1 - q u)) *
          (coinProb P q c * ind0 P (detPoints P m t) c)
        - (Y1 Y t - Y0 Y t) * (coinProb P q c * 1) := by
      intro c; field_simp; ring
    rw [Finset.sum_congr rfl fun c _ => key c]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [e1, e0, eone]
    field_simp
    ring
  unfold E
  have key2 : ∀ c : P → Bool, coinProb P q c * (tau m T Y + 1 / ((T : ℝ) - m) *
      ∑ t ∈ Finset.Icc (m + 1) T, errT m P q Y t c) =
      tau m T Y * coinProb P q c + 1 / ((T : ℝ) - m) *
        ∑ t ∈ Finset.Icc (m + 1) T, coinProb P q c * errT m P q Y t c := by
    intro c
    simp only [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun t _ => by ring
  rw [Finset.sum_congr rfl fun c _ => key2 c, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_comm]
  have eone := E_one P q
  unfold E at eone hz
  rw [Finset.sum_congr rfl hz]
  simp only [mul_one] at eone
  rw [eone]
  simp

lemma thm1_gen (m T : ℕ) (hmT : m < T) (B : ℝ) (hB : 0 < B) (P : Finset ℕ) (q : ℕ → ℝ)
    (hopt : IsMinimaxOptimal m T B P q) : ∀ t ∈ P, q t = 1 / 2 := by
  obtain ⟨hP, hq, h⟩ := hopt
  have hhalf : IsRegularProbs P half := fun t _ => by unfold half; norm_num
  have hL : (0 : ℝ) < (T : ℝ) - m := by
    have : (m : ℝ) < T := by exact_mod_cast hmT
    linarith
  have cpos : 0 < (1 / ((T : ℝ) - m)) ^ 2 * B ^ 2 := by positivity
  obtain ⟨Y', hY', hle⟩ := h P half hP hhalf (Yplus B) (admissible_plus m T B hB)
  have h2 := risk_le_plus m T P hP.1 half hhalf B hB Y' hY'
  rw [risk_plus m T P hP.1 q hq B] at hle
  rw [risk_plus m T P hP.1 half hhalf B] at h2
  have hF : F m T P q ≤ F m T P half := le_of_mul_le_mul_left (le_trans hle h2) cpos
  have hFP := F_half_le m T P hP.1 hP.2.1 q hq (by omega)
  exact hFP.2 (le_antisymm hF hFP.1)

lemma half_prod (O : Finset ℕ) : ∏ u ∈ O, 1 / half u = 2 ^ O.card := by
  unfold half; rw [Finset.prod_const]; norm_num

lemma half_prod' (O : Finset ℕ) : ∏ u ∈ O, 1 / (1 - half u) = 2 ^ O.card := by
  unfold half; rw [Finset.prod_const]; norm_num

end SwbAux

namespace SwbAux
open Finset SwitchbackExp.Design

lemma admissible_minus (m T : ℕ) (B : ℝ) (hB : 0 < B) : Admissible m T B (Yminus B) := by
  refine ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ => ?_⟩
  simp [Yminus, abs_of_pos hB]

lemma Cterm_minus (m : ℕ) (P : Finset ℕ) (q : ℕ → ℝ) (B : ℝ) (t t' : ℕ) :
    Cterm m P q (Yminus B) t t' = Cterm m P q (Yplus B) t t' := by
  unfold Cterm Y1 Y0 Yminus Yplus
  ring

lemma risk_minus (m T : ℕ) (P : Finset ℕ) (h1 : 1 ∈ P) (q : ℕ → ℝ)
    (hq : ∀ u ∈ P, 0 < q u ∧ q u < 1) (B : ℝ) :
    risk m T P q (Yminus B) = risk m T P q (Yplus B) := by
  rw [risk_formula m T P h1 q hq (Yminus B) (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl),
    risk_formula m T P h1 q hq (Yplus B) (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)]
  simp only [Cterm_minus]

lemma prod_inv_gt_one (O : Finset ℕ) (hO : O.Nonempty) (f : ℕ → ℝ)
    (hf : ∀ u ∈ O, 0 < f u ∧ f u < 1) : 1 < ∏ u ∈ O, 1 / f u := by
  rw [Finset.prod_div_distrib, Finset.prod_const_one]
  have hpos : 0 < ∏ u ∈ O, f u := Finset.prod_pos fun u hu => (hf u hu).1
  have hlt : ∏ u ∈ O, f u < ∏ u ∈ O, (1 : ℝ) := by
    obtain ⟨u, hu⟩ := hO
    exact Finset.prod_lt_prod (fun u hu => (hf u hu).1) (fun u hu => (hf u hu).2.le)
      ⟨u, hu, (hf u hu).2⟩
  rw [Finset.prod_const_one] at hlt
  rw [lt_div_iff₀ hpos]; linarith

lemma Cterm_lt (m T : ℕ) (P : Finset ℕ) (h1 : 1 ∈ P) (q : ℕ → ℝ)
    (hq : ∀ u ∈ P, 0 < q u ∧ q u < 1) (B : ℝ) (hB : 0 < B) (Y : Outcomes)
    (hY : Bounded B T Y) (t t' : ℕ) (ht : t ∈ Finset.Icc (m + 1) T)
    (ht' : t' ∈ Finset.Icc (m + 1) T) (hne : (overlap P m t t').Nonempty)
    (hs : Y1 Y t * Y1 Y t' < B * B ∨ Y0 Y t * Y0 Y t' < B * B ∨
      Y1 Y t * Y0 Y t' + Y0 Y t * Y1 Y t' < B * B + B * B) :
    Cterm m P q Y t t' < Cterm m P q (Yplus B) t t' := by
  rw [Finset.mem_Icc] at ht ht'
  have hO : overlap P m t t' ⊆ P := fun u hu =>
    detPoints_sub P h1 m t ht.1 (Finset.mem_inter.1 hu).1
  have k1 : 0 < ∏ u ∈ overlap P m t t', 1 / q u - 1 := by
    have := prod_inv_gt_one _ hne q (fun u hu => hq u (hO hu))
    linarith
  have k0 : 0 < ∏ u ∈ overlap P m t t', 1 / (1 - q u) - 1 := by
    have := prod_inv_gt_one _ hne (fun u => 1 - q u)
      (fun u hu => ⟨by linarith [(hq u (hO hu)).2], by linarith [(hq u (hO hu)).1]⟩)
    linarith
  have hab : ∀ x y : ℝ, |x| ≤ B → |y| ≤ B → x * y ≤ B * B := fun x y hx hy =>
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) hB.le)
  have a1 : |Y1 Y t| ≤ B := hY t (by omega) ht.2 _
  have a1' : |Y1 Y t'| ≤ B := hY t' (by omega) ht'.2 _
  have b1 : |Y0 Y t| ≤ B := hY t (by omega) ht.2 _
  have b1' : |Y0 Y t'| ≤ B := hY t' (by omega) ht'.2 _
  unfold Cterm
  have e1 : Y1 (Yplus B) t = B := rfl
  have e2 : Y1 (Yplus B) t' = B := rfl
  have e3 : Y0 (Yplus B) t = B := rfl
  have e4 : Y0 (Yplus B) t' = B := rfl
  rw [e1, e2, e3, e4, if_pos hne]
  have p1 := hab _ _ a1 a1'
  have p2 := hab _ _ b1 b1'
  have p3 := hab _ _ a1 b1'
  have p4 := hab _ _ b1 a1'
  rcases hs with h | h | h
  · have := mul_lt_mul_of_pos_right h k1
    have := mul_le_mul_of_nonneg_right p2 k0.le
    linarith
  · have := mul_le_mul_of_nonneg_right p1 k1.le
    have := mul_lt_mul_of_pos_right h k0
    linarith
  · have := mul_le_mul_of_nonneg_right p1 k1.le
    have := mul_le_mul_of_nonneg_right p2 k0.le
    linarith

lemma ivt (a : ℕ → ℝ) (lo hi t1 t2 : ℕ) (h1 : t1 ∈ Finset.Icc lo hi) (h2 : t2 ∈ Finset.Icc lo hi)
    (hne : a t1 ≠ a t2) : ∃ s, lo ≤ s ∧ s + 1 ≤ hi ∧ a s ≠ a (s + 1) := by
  by_contra hc
  push Not at hc
  have hconst : ∀ k, lo + k ≤ hi → a (lo + k) = a lo := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [← ih (by omega), ← add_assoc]
      exact (hc (lo + k) (by omega) (by omega)).symm
  rw [Finset.mem_Icc] at h1 h2
  have := hconst (t1 - lo) (by omega)
  have := hconst (t2 - lo) (by omega)
  rw [show lo + (t1 - lo) = t1 by omega] at *
  rw [show lo + (t2 - lo) = t2 by omega] at *
  exact hne (by simp_all)

lemma lemma1_gen (m T : ℕ) (hmT : m < T) (B : ℝ) (hB : 0 < B) (P : Finset ℕ) (q : ℕ → ℝ)
    (hP : IsRegularPoints T P) (hq : IsRegularProbs P q) (Y : Outcomes)
    (hY : Admissible m T B Y) :
    (Admissible m T B (Yplus B) ∧ Admissible m T B (Yminus B)) ∧
    risk m T P q Y ≤ risk m T P q (Yplus B) ∧ risk m T P q Y ≤ risk m T P q (Yminus B) ∧
    (1 ≤ m → (∃ t ∈ Finset.Icc (m + 1) T, Y1 Y t ≠ B ∨ Y0 Y t ≠ B) →
      (∃ t ∈ Finset.Icc (m + 1) T, Y1 Y t ≠ -B ∨ Y0 Y t ≠ -B) →
      risk m T P q Y < risk m T P q (Yplus B) ∧ risk m T P q Y < risk m T P q (Yminus B)) := by
  have hle := risk_le_plus m T P hP.1 q hq B hB Y hY
  have hmin := risk_minus m T P hP.1 q hq B
  refine ⟨⟨admissible_plus m T B hB, admissible_minus m T B hB⟩, hle, hmin ▸ hle, ?_⟩
  intro hm hplus hminus
  suffices h : risk m T P q Y < risk m T P q (Yplus B) from ⟨h, hmin ▸ h⟩
  have hL : (0 : ℝ) < (T : ℝ) - m := by
    have : (m : ℝ) < T := by exact_mod_cast hmT
    linarith
  rw [risk_formula m T P hP.1 q hq Y hY.1 hY.2.1,
    risk_formula m T P hP.1 q hq (Yplus B) (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)]
  apply mul_lt_mul_of_pos_left _ (by positivity)
  -- it suffices to find one strict pair
  suffices hpair : ∃ t ∈ Finset.Icc (m + 1) T, ∃ t' ∈ Finset.Icc (m + 1) T,
      Cterm m P q Y t t' < Cterm m P q (Yplus B) t t' by
    obtain ⟨t0, ht0, t0', ht0', hlt⟩ := hpair
    apply Finset.sum_lt_sum
    · exact fun t ht => Finset.sum_le_sum fun t' ht' =>
        Cterm_le m T P hP.1 q hq B hB Y hY.2.2 t t' ht ht'
    · refine ⟨t0, ht0, Finset.sum_lt_sum (fun t' ht' =>
        Cterm_le m T P hP.1 q hq B hB Y hY.2.2 t0 t' ht0 ht') ⟨t0', ht0', hlt⟩⟩
  have hbd : ∀ t ∈ Finset.Icc (m + 1) T, |Y1 Y t| ≤ B ∧ |Y0 Y t| ≤ B := fun t ht =>
    ⟨hY.2.2 t (by have := (Finset.mem_Icc.1 ht).1; omega) (Finset.mem_Icc.1 ht).2 _,
     hY.2.2 t (by have := (Finset.mem_Icc.1 ht).1; omega) (Finset.mem_Icc.1 ht).2 _⟩
  have hself : ∀ t ∈ Finset.Icc (m + 1) T, (overlap P m t t).Nonempty := fun t ht => by
    unfold overlap; rw [Finset.inter_self]
    exact self_mem_D P hP.1 m t (Finset.mem_Icc.1 ht).1
  have hBB : 0 < B * B := mul_pos hB hB
  by_cases hA : ∃ t ∈ Finset.Icc (m + 1) T, |Y1 Y t| < B
  · obtain ⟨t, ht, hlt⟩ := hA
    refine ⟨t, ht, t, ht, Cterm_lt m T P hP.1 q hq B hB Y hY.2.2 t t ht ht (hself t ht) ?_⟩
    left
    have : Y1 Y t * Y1 Y t = |Y1 Y t| * |Y1 Y t| := by rw [← abs_mul, abs_mul_self]
    rw [this]
    exact mul_self_lt_mul_self (abs_nonneg _) hlt
  push Not at hA
  by_cases hA0 : ∃ t ∈ Finset.Icc (m + 1) T, |Y0 Y t| < B
  · obtain ⟨t, ht, hlt⟩ := hA0
    refine ⟨t, ht, t, ht, Cterm_lt m T P hP.1 q hq B hB Y hY.2.2 t t ht ht (hself t ht) ?_⟩
    right; left
    have : Y0 Y t * Y0 Y t = |Y0 Y t| * |Y0 Y t| := by rw [← abs_mul, abs_mul_self]
    rw [this]
    exact mul_self_lt_mul_self (abs_nonneg _) hlt
  push Not at hA0
  have pm1 : ∀ t ∈ Finset.Icc (m + 1) T, Y1 Y t = B ∨ Y1 Y t = -B := fun t ht =>
    (abs_eq hB.le).1 (le_antisymm (hbd t ht).1 (hA t ht))
  have pm0 : ∀ t ∈ Finset.Icc (m + 1) T, Y0 Y t = B ∨ Y0 Y t = -B := fun t ht =>
    (abs_eq hB.le).1 (le_antisymm (hbd t ht).2 (hA0 t ht))
  by_cases hC : ∃ t ∈ Finset.Icc (m + 1) T, Y1 Y t ≠ Y0 Y t
  · obtain ⟨t, ht, hne⟩ := hC
    refine ⟨t, ht, t, ht, Cterm_lt m T P hP.1 q hq B hB Y hY.2.2 t t ht ht (hself t ht) ?_⟩
    right; right
    rcases pm1 t ht with h1 | h1 <;> rcases pm0 t ht with h0 | h0 <;> rw [h1, h0] at hne ⊢ <;>
      first | exact absurd rfl hne | nlinarith
  push Not at hC
  obtain ⟨t1, ht1, h1⟩ := hplus
  obtain ⟨t2, ht2, h2⟩ := hminus
  have ht1v : Y1 Y t1 = -B := by
    rcases pm1 t1 ht1 with h | h
    · exfalso; rw [← hC t1 ht1] at h1; rcases h1 with h1 | h1 <;> exact h1 h
    · exact h
  have ht2v : Y1 Y t2 = B := by
    rcases pm1 t2 ht2 with h | h
    · exact h
    · exfalso; rw [← hC t2 ht2] at h2; rcases h2 with h2 | h2 <;> exact h2 h
  obtain ⟨s, hs1, hs2, hsne⟩ := ivt (Y1 Y) (m + 1) T t1 t2 ht1 ht2 (by rw [ht1v, ht2v]; linarith)
  have hsI : s ∈ Finset.Icc (m + 1) T := Finset.mem_Icc.2 ⟨hs1, by omega⟩
  have hsI' : s + 1 ∈ Finset.Icc (m + 1) T := Finset.mem_Icc.2 ⟨by omega, hs2⟩
  have hov : (overlap P m s (s + 1)).Nonempty := by
    refine ⟨detPoint P s, Finset.mem_inter.2 ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.2 ⟨s, Finset.mem_Icc.2 ⟨by omega, le_rfl⟩, rfl⟩
    · exact Finset.mem_image.2 ⟨s, Finset.mem_Icc.2 ⟨by omega, by omega⟩, rfl⟩
  refine ⟨s, hsI, s + 1, hsI', Cterm_lt m T P hP.1 q hq B hB Y hY.2.2 s (s + 1) hsI hsI' hov ?_⟩
  left
  rcases pm1 s hsI with h | h <;> rcases pm1 (s + 1) hsI' with h' | h' <;> rw [h, h'] at hsne ⊢ <;>
    first | exact absurd rfl hsne | nlinarith

end SwbAux
open SwitchbackExp.Design in
theorem solution (m T : ℕ) (hmT : m < T) (P : Finset ℕ) (q : ℕ → ℝ)
    (hP : IsRegularPoints T P) (hq : IsRegularProbs P q) (Y : Outcomes)
    (hY1 : NonAnticipating T Y) (hY2 : Carryover m T Y) :
    SwitchbackExp.Design.expect P q (htEstimator m T P q Y) = tau m T Y :=
  SwbAux.prop1_gen m T P hP.1 q hq Y hY1 hY2
