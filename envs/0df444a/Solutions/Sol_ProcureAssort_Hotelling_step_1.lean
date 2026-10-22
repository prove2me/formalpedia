-- Prove2me | solution 1 for ProcureAssort.Hotelling.step_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T04:09:53.334652+00:00
-- url     : https://prove2.me/submissions/acec58fe-6b91-44a8-b9de-21bc7b01865c

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting
import Theorems.Thm_ProcureAssort_Hotelling_proposition_3_2
import Theorems.Thm_ProcureAssort_Hotelling_lemma_F_3

open ProcureAssort.Hotelling

namespace PS1

variable {n : ℕ}

noncomputable def leftPart (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) (k : Fin n) : ℝ :=
  if h : ((hotQ ℓ δ p).filter (· < k)).Nonempty then
    (p (((hotQ ℓ δ p).filter (· < k)).max' h) - p k
      + δ * |ℓ k - ℓ (((hotQ ℓ δ p).filter (· < k)).max' h)|) / (2 * δ)
  else ℓ k

noncomputable def rightPart (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) (k : Fin n) : ℝ :=
  if h : ((hotQ ℓ δ p).filter (k < ·)).Nonempty then
    (p (((hotQ ℓ δ p).filter (k < ·)).min' h) - p k
      + δ * |ℓ (((hotQ ℓ δ p).filter (k < ·)).min' h) - ℓ k|) / (2 * δ)
  else 1 - ℓ k

lemma mem_hotQ' (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) (i : Fin n) :
    i ∈ hotQ ℓ δ p ↔ ∀ j, p i - p j ≤ δ * |ℓ j - ℓ i| := by
  unfold hotQ; simp

lemma hd_eq (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) (k : Fin n) (hk : k ∈ hotQ ℓ δ p) :
    hotDemand ℓ δ p k = leftPart ℓ δ p k + rightPart ℓ δ p k := by
  unfold hotDemand leftPart rightPart
  rw [if_pos hk]

lemma hd_out (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) (k : Fin n) (hk : k ∉ hotQ ℓ δ p) :
    hotDemand ℓ δ p k = 0 := by
  unfold hotDemand; rw [if_neg hk]

lemma leftPart_nonneg (ℓ : Fin n → ℝ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (δ : ℝ) (hδ : 0 < δ)
    (p : Fin n → ℝ) (k : Fin n) (hk : k ∈ hotQ ℓ δ p) : 0 ≤ leftPart ℓ δ p k := by
  unfold leftPart
  split_ifs with h
  · have := (mem_hotQ' ℓ δ p k).mp hk (((hotQ ℓ δ p).filter (· < k)).max' h)
    rw [abs_sub_comm] at this
    exact div_nonneg (by linarith) (by linarith)
  · exact hℓ0 k

lemma rightPart_nonneg (ℓ : Fin n → ℝ) (hℓ1 : ∀ i, ℓ i ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (p : Fin n → ℝ) (k : Fin n) (hk : k ∈ hotQ ℓ δ p) : 0 ≤ rightPart ℓ δ p k := by
  unfold rightPart
  split_ifs with h
  · have := (mem_hotQ' ℓ δ p k).mp hk (((hotQ ℓ δ p).filter (k < ·)).min' h)
    exact div_nonneg (by linarith) (by linarith)
  · linarith [hℓ1 k]

lemma hd_nonneg (ℓ : Fin n → ℝ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (p : Fin n → ℝ) (k : Fin n) : 0 ≤ hotDemand ℓ δ p k := by
  by_cases hk : k ∈ hotQ ℓ δ p
  · rw [hd_eq ℓ δ p k hk]
    linarith [leftPart_nonneg ℓ hℓ0 δ hδ p k hk, rightPart_nonneg ℓ hℓ1 δ hδ p k hk]
  · rw [hd_out ℓ δ p k hk]

/-- Key lemma: lowering the price of `m` can only kill the demand of `j ≠ m` if `m`'s
delivered price at `ℓ j` reaches `p j`. -/
lemma key (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (p p' : Fin n → ℝ) (m j : Fin n) (hjm : j ≠ m)
    (hle : p' m ≤ p m) (heq : ∀ k, k ≠ m → p' k = p k)
    (hpos : 0 < hotDemand ℓ δ p j) (h : p j < p' m + δ * |ℓ j - ℓ m|) :
    0 < hotDemand ℓ δ p' j := by
  classical
  have hjQ : j ∈ hotQ ℓ δ p := by
    by_contra hc; rw [hd_out ℓ δ p j hc] at hpos; exact lt_irrefl _ hpos
  have hpj : p' j = p j := heq j hjm
  have hjQ' : j ∈ hotQ ℓ δ p' := by
    rw [mem_hotQ']
    intro i
    by_cases him : i = m
    · subst him; rw [hpj, abs_sub_comm]; linarith
    · rw [hpj, heq i him]; exact (mem_hotQ' ℓ δ p j).mp hjQ i
  have hsub : ∀ k ∈ hotQ ℓ δ p', k ≠ m → k ∈ hotQ ℓ δ p := by
    intro k hk hkm
    rw [mem_hotQ'] at hk ⊢
    intro i
    have h1 := hk i
    have h2 : p' i ≤ p i := by
      by_cases him : i = m
      · subst him; exact hle
      · rw [heq i him]
    rw [heq k hkm] at h1
    linarith
  rw [hd_eq ℓ δ p j hjQ] at hpos
  rw [hd_eq ℓ δ p' j hjQ']
  have hl0 := leftPart_nonneg ℓ hℓ0 δ hδ p j hjQ
  have hr0 := rightPart_nonneg ℓ hℓ1 δ hδ p j hjQ
  have hl0' := leftPart_nonneg ℓ hℓ0 δ hδ p' j hjQ'
  have hr0' := rightPart_nonneg ℓ hℓ1 δ hδ p' j hjQ'
  have h2δ : 0 < 2 * δ := by linarith
  rcases (show 0 < leftPart ℓ δ p j ∨ 0 < rightPart ℓ δ p j by
      by_contra hc; push Not at hc; linarith) with hl | hr
  · suffices 0 < leftPart ℓ δ p' j by linarith
    unfold leftPart at hl ⊢
    split_ifs at ⊢ with h'
    · set L' := ((hotQ ℓ δ p').filter (· < j)).max' h' with hL'
      have hL'm := Finset.mem_filter.mp (Finset.max'_mem _ h')
      rw [← hL'] at hL'm
      by_cases hLm : L' = m
      · rw [hLm, hpj]
        apply div_pos _ h2δ
        linarith
      · have hL'Q := hsub L' hL'm.1 hLm
        have hne : ((hotQ ℓ δ p).filter (· < j)).Nonempty :=
          ⟨L', Finset.mem_filter.mpr ⟨hL'Q, hL'm.2⟩⟩
        rw [dif_pos hne] at hl
        set L := ((hotQ ℓ δ p).filter (· < j)).max' hne with hL
        have hLm' := Finset.mem_filter.mp (Finset.max'_mem _ hne)
        rw [← hL] at hLm'
        have hLL : L' ≤ L := Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hL'Q, hL'm.2⟩)
        have hact := (mem_hotQ' ℓ δ p L).mp hLm'.1 L'
        have e1 : ℓ L' ≤ ℓ L := hℓ.monotone hLL
        have e2 : ℓ L < ℓ j := hℓ hLm'.2
        rw [abs_of_nonpos (by linarith)] at hact
        rw [abs_of_pos (by linarith)] at hl
        rw [abs_of_pos (show 0 < ℓ j - ℓ L' by linarith), hpj, heq L' hLm]
        apply div_pos _ h2δ
        have := (div_pos_iff_of_pos_right h2δ).mp hl
        linarith
    · split_ifs at hl with hh
      · have hLm' := Finset.mem_filter.mp (Finset.max'_mem _ hh)
        have := hℓ hLm'.2
        linarith [hℓ0 (((hotQ ℓ δ p).filter (· < j)).max' hh)]
      · exact hl
  · suffices 0 < rightPart ℓ δ p' j by linarith
    unfold rightPart at hr ⊢
    split_ifs at ⊢ with h'
    · set R' := ((hotQ ℓ δ p').filter (j < ·)).min' h' with hR'
      have hR'm := Finset.mem_filter.mp (Finset.min'_mem _ h')
      rw [← hR'] at hR'm
      by_cases hRm : R' = m
      · rw [hRm, hpj]
        apply div_pos _ h2δ
        rw [abs_sub_comm] at h
        linarith
      · have hR'Q := hsub R' hR'm.1 hRm
        have hne : ((hotQ ℓ δ p).filter (j < ·)).Nonempty :=
          ⟨R', Finset.mem_filter.mpr ⟨hR'Q, hR'm.2⟩⟩
        rw [dif_pos hne] at hr
        set R := ((hotQ ℓ δ p).filter (j < ·)).min' hne with hR
        have hRm' := Finset.mem_filter.mp (Finset.min'_mem _ hne)
        rw [← hR] at hRm'
        have hRR : R ≤ R' := Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hR'Q, hR'm.2⟩)
        have hact := (mem_hotQ' ℓ δ p R).mp hRm'.1 R'
        have e1 : ℓ R ≤ ℓ R' := hℓ.monotone hRR
        have e2 : ℓ j < ℓ R := hℓ hRm'.2
        rw [abs_of_nonneg (by linarith)] at hact
        rw [abs_of_pos (by linarith)] at hr
        rw [abs_of_pos (show 0 < ℓ R' - ℓ j by linarith), hpj, heq R' hRm]
        apply div_pos _ h2δ
        have := (div_pos_iff_of_pos_right h2δ).mp hr
        linarith
    · split_ifs at hr with hh
      · have hRm' := Finset.mem_filter.mp (Finset.min'_mem _ hh)
        have := hℓ hRm'.2
        linarith [hℓ1 (((hotQ ℓ δ p).filter (j < ·)).min' hh)]
      · exact hr

end PS1


open ProcureAssort.Hotelling

namespace PS1

variable {n : ℕ}

lemma adjacent_symm' (Q : Finset (Fin n)) (i j : Fin n) : Adjacent Q i j → Adjacent Q j i := by
  rintro ⟨hi, hj, hne, h⟩
  exact ⟨hj, hi, hne.symm, by rwa [min_comm, max_comm]⟩

lemma pathA_symm (Q : Finset (Fin n)) (i j : Fin n) : pathA Q i j = pathA Q j i := by
  classical
  unfold pathA
  by_cases hij : i = j
  · subst hij; rfl
  · have h1 : Adjacent Q i j ↔ Adjacent Q j i := ⟨adjacent_symm' Q i j, adjacent_symm' Q j i⟩
    simp only [hij, Ne.symm hij, if_false, h1, and_comm]

lemma pathA_row' (Q : Finset (Fin n)) (i : Fin n) (hi : i ∈ Q) (w : Fin n → ℝ) :
    ∑ j ∈ Q, pathA Q i j * w j = ∑ j ∈ Q.filter (fun k => Adjacent Q i k), (w j - w i) := by
  classical
  have h1 : ∀ j ∈ Q, pathA Q i j * w j =
      (if i = j then -(((Q.filter (fun k => Adjacent Q i k)).card : ℕ) : ℝ) * w i else 0) +
        (if Adjacent Q i j then w j else 0) := by
    intro j hj
    unfold pathA
    rw [if_pos ⟨hi, hj⟩]
    by_cases hij : i = j
    · subst hij
      have : ¬ Adjacent Q i i := fun h => h.2.2.1 rfl
      simp [this]
    · simp [hij]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_ite_eq Q i, if_pos hi,
    ← Finset.sum_filter, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

lemma adj_left (Q : Finset (Fin n)) (k : Fin n) (hk : k ∈ Q) (w : Fin n → ℝ) :
    ∑ j ∈ (Q.filter (fun x => Adjacent Q k x)).filter (· < k), w j =
      if h : (Q.filter (· < k)).Nonempty then w ((Q.filter (· < k)).max' h) else 0 := by
  classical
  split_ifs with h
  · set L := (Q.filter (· < k)).max' h with hL
    have hLm := Finset.mem_filter.mp (Finset.max'_mem _ h)
    rw [← hL] at hLm
    have : (Q.filter (fun x => Adjacent Q k x)).filter (· < k) = {L} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      constructor
      · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hLm.1, hk, hLm.1, ?_, ?_⟩, hLm.2⟩
        · exact (ne_of_lt hLm.2).symm
        · intro m hm ⟨h1, h2⟩
          rw [min_eq_right hLm.2.le] at h1
          rw [max_eq_left hLm.2.le] at h2
          have : m ≤ L := Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hm, h2⟩)
          exact absurd h1 (not_lt.mpr this)
      · intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_filter.mp hj
        obtain ⟨hjQ, hadj⟩ := Finset.mem_filter.mp hj1
        have hjL : j ≤ L := Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hjQ, hj2⟩)
        rcases eq_or_lt_of_le hjL with e | e
        · exact e
        · exfalso
          apply hadj.2.2.2 L hLm.1
          rw [min_eq_right hj2.le, max_eq_left hj2.le]
          exact ⟨e, hLm.2⟩
    rw [this, Finset.sum_singleton]
  · rw [Finset.sum_eq_zero]
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_filter.mp hj
    exact absurd ⟨j, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj1).1, hj2⟩⟩ h

lemma adj_right (Q : Finset (Fin n)) (k : Fin n) (hk : k ∈ Q) (w : Fin n → ℝ) :
    ∑ j ∈ (Q.filter (fun x => Adjacent Q k x)).filter (fun x => ¬ x < k), w j =
      if h : (Q.filter (k < ·)).Nonempty then w ((Q.filter (k < ·)).min' h) else 0 := by
  classical
  have hgt : ∀ j ∈ (Q.filter (fun x => Adjacent Q k x)).filter (fun x => ¬ x < k), k < j := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_filter.mp hj
    have hadj := (Finset.mem_filter.mp hj1).2
    exact lt_of_le_of_ne (not_lt.mp hj2) hadj.2.2.1
  split_ifs with h
  · set R := (Q.filter (k < ·)).min' h with hR
    have hRm := Finset.mem_filter.mp (Finset.min'_mem _ h)
    rw [← hR] at hRm
    have : (Q.filter (fun x => Adjacent Q k x)).filter (fun x => ¬ x < k) = {R} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      constructor
      · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hRm.1, hk, hRm.1, ?_, ?_⟩,
          not_lt.mpr hRm.2.le⟩
        · exact ne_of_lt hRm.2
        · intro m hm ⟨h1, h2⟩
          rw [min_eq_left hRm.2.le] at h1
          rw [max_eq_right hRm.2.le] at h2
          have : R ≤ m := Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hm, h1⟩)
          exact absurd h2 (not_lt.mpr this)
      · intro j hj
        have hkj := hgt j hj
        obtain ⟨hj1, _⟩ := Finset.mem_filter.mp hj
        obtain ⟨hjQ, hadj⟩ := Finset.mem_filter.mp hj1
        have hRj : R ≤ j := Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hjQ, hkj⟩)
        rcases eq_or_lt_of_le hRj with e | e
        · exact e.symm
        · exfalso
          apply hadj.2.2.2 R hRm.1
          rw [min_eq_left hkj.le, max_eq_right hkj.le]
          exact ⟨hRm.2, e⟩
    rw [this, Finset.sum_singleton]
  · rw [Finset.sum_eq_zero]
    intro j hj
    exact absurd ⟨j, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp
      (Finset.mem_filter.mp hj).1).1, hgt j hj⟩⟩ h

lemma adj_sum (Q : Finset (Fin n)) (k : Fin n) (hk : k ∈ Q) (w : Fin n → ℝ) :
    ∑ j ∈ Q.filter (fun x => Adjacent Q k x), w j =
      (if h : (Q.filter (· < k)).Nonempty then w ((Q.filter (· < k)).max' h) else 0) +
      (if h : (Q.filter (k < ·)).Nonempty then w ((Q.filter (k < ·)).min' h) else 0) := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (· < k), adj_left Q k hk w, adj_right Q k hk w]

/-- The constant term of the Hotelling demand of an active supplier. -/
noncomputable def Bc (ℓ : Fin n → ℝ) (δ : ℝ) (Q : Finset (Fin n)) (k : Fin n) : ℝ :=
  (if h : (Q.filter (· < k)).Nonempty then δ * |ℓ k - ℓ ((Q.filter (· < k)).max' h)|
    else 2 * δ * ℓ k) +
  (if h : (Q.filter (k < ·)).Nonempty then δ * |ℓ ((Q.filter (k < ·)).min' h) - ℓ k|
    else 2 * δ * (1 - ℓ k))

lemma rep (ℓ : Fin n → ℝ) (δ : ℝ) (hδ : 0 < δ) (p : Fin n → ℝ) (k : Fin n)
    (hk : k ∈ hotQ ℓ δ p) :
    2 * δ * hotDemand ℓ δ p k = Bc ℓ δ (hotQ ℓ δ p) k +
      ∑ j ∈ hotQ ℓ δ p, pathA (hotQ ℓ δ p) k j * p j := by
  classical
  rw [pathA_row' _ k hk, adj_sum _ k hk, hd_eq ℓ δ p k hk]
  unfold leftPart rightPart Bc
  have hδ' : δ ≠ 0 := hδ.ne'
  split_ifs <;> field_simp <;> ring

end PS1


namespace PS1

variable {n : ℕ}

lemma quad3 (q2 q1 q0 x1 x2 x3 : ℝ) (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (e1 : q2 * x1 ^ 2 + q1 * x1 + q0 = 0) (e2 : q2 * x2 ^ 2 + q1 * x2 + q0 = 0)
    (e3 : q2 * x3 ^ 2 + q1 * x3 + q0 = 0) : q2 = 0 := by
  have a : q2 * (x1 + x2) + q1 = 0 := by
    have : (x1 - x2) * (q2 * (x1 + x2) + q1) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) h12
    · exact h
  have b : q2 * (x1 + x3) + q1 = 0 := by
    have : (x1 - x3) * (q2 * (x1 + x3) + q1) = 0 := by linear_combination e1 - e3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) h13
    · exact h
  have : q2 * (x2 - x3) = 0 := by linear_combination a - b
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) h23

/-- the affine demand `X_k(θ) = A_k + Σ_j P_kj V_j(θ_j)` -/
def Xf (A : Fin n → ℝ) (P : Fin n → Fin n → ℝ) (V : Fin n → ℝ → ℝ) (θ : Fin n → ℝ)
    (k : Fin n) : ℝ :=
  A k + ∑ j, P k j * V j (θ j)

lemma X_update (A : Fin n → ℝ) (P : Fin n → Fin n → ℝ) (V : Fin n → ℝ → ℝ)
    (β : Fin n → ℝ) (i : Fin n) (s : ℝ) (k : Fin n) :
    Xf A P V (Function.update β i s) k =
      A k + P k i * V i s + ∑ j ∈ Finset.univ.erase i, P k j * V j (β j) := by
  unfold Xf
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
  have : ∑ j ∈ Finset.univ.erase i, P k j * V j (Function.update β i s j) =
      ∑ j ∈ Finset.univ.erase i, P k j * V j (β j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [this]; ring

lemma F_update (A : Fin n → ℝ) (P : Fin n → Fin n → ℝ) (V G : Fin n → ℝ → ℝ)
    (β : Fin n → ℝ) (i : Fin n) (s : ℝ) :
    ∑ k, G k (Function.update β i s k) * Xf A P V (Function.update β i s) k =
      G i s * ((A i + ∑ j ∈ Finset.univ.erase i, P i j * V j (β j)) + P i i * V i s) +
      (∑ k ∈ Finset.univ.erase i, G k (β k) *
          (A k + ∑ j ∈ Finset.univ.erase i, P k j * V j (β j))) +
      (∑ k ∈ Finset.univ.erase i, G k (β k) * P k i) * V i s := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self, X_update]
  have : ∑ k ∈ Finset.univ.erase i, G k (Function.update β i s k) *
        Xf A P V (Function.update β i s) k =
      ∑ k ∈ Finset.univ.erase i, (G k (β k) *
          (A k + ∑ j ∈ Finset.univ.erase i, P k j * V j (β j)) +
        G k (β k) * P k i * V i s) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk), X_update]
    ring
  rw [this, Finset.sum_add_distrib, Finset.sum_mul]
  ring

theorem abs_step (W : Fin n → Finset ℝ) (G V : Fin n → ℝ → ℝ) (A : Fin n → ℝ)
    (P : Fin n → Fin n → ℝ)
    (hW3 : ∀ i, 2 < (W i).card) (hV : ∀ i, Set.InjOn (V i) (W i))
    (hdiag : ∀ i, P i i ≠ 0) (hnb : ∀ i, ∃ j, j ≠ i ∧ P i j ≠ 0)
    (hker : ∀ a : Fin n → ℝ, (∀ i, ∑ k, a k * P k i = 0) → ∀ i j, a i = a j)
    (hsum : ∀ θ : Fin n → ℝ, (∀ i, θ i ∈ W i) → ∑ k, Xf A P V θ k ≠ 0)
    (hF : ∀ θ : Fin n → ℝ, (∀ i, θ i ∈ W i) → ∑ k, G k (θ k) * Xf A P V θ k = 0) :
    ∀ i, ∀ c ∈ W i, G i c = 0 := by
  classical
  have hWne : ∀ i, (W i).Nonempty := fun i =>
    Finset.card_pos.mp (by have := hW3 i; omega)
  set β : Fin n → ℝ := fun i => (W i).min' (hWne i) with hβdef
  have hβ : ∀ i, β i ∈ W i := fun i => Finset.min'_mem _ _
  have hupd : ∀ β : Fin n → ℝ, (∀ i, β i ∈ W i) → ∀ i, ∀ s ∈ W i,
      ∀ k, Function.update β i s k ∈ W k := by
    intro β hβ i s hs k
    by_cases hk : k = i
    · subst hk; rw [Function.update_self]; exact hs
    · rw [Function.update_of_ne hk]; exact hβ k
  -- the single-coordinate equation
  have hE : ∀ β : Fin n → ℝ, (∀ i, β i ∈ W i) → ∀ i, ∀ s ∈ W i,
      G i s * ((A i + ∑ j ∈ Finset.univ.erase i, P i j * V j (β j)) + P i i * V i s) +
      (∑ k ∈ Finset.univ.erase i, G k (β k) *
          (A k + ∑ j ∈ Finset.univ.erase i, P k j * V j (β j))) +
      (∑ k ∈ Finset.univ.erase i, G k (β k) * P k i) * V i s = 0 := by
    intro β hβ i s hs
    rw [← F_update]
    exact hF _ (hupd β hβ i s hs)
  -- Step A + B: `G i` is constant on `W i`
  have hconst : ∀ i, ∀ s ∈ W i, G i s = G i (β i) := by
    intro i
    obtain ⟨j, hji, hPij⟩ := hnb i
    obtain ⟨t, ht, htne⟩ := Finset.exists_mem_ne (show 1 < (W j).card by have := hW3 j; omega)
      (β j)
    have hVt : V j t ≠ V j (β j) := fun h => htne (hV j ht (hβ j) h)
    set β' := Function.update β j t with hβ'
    have hβ'W : ∀ k, β' k ∈ W k := hupd β hβ j t ht
    set α := A i + ∑ j ∈ Finset.univ.erase i, P i j * V j (β j)
    set α' := A i + ∑ j ∈ Finset.univ.erase i, P i j * V j (β' j)
    have hαα : α' - α = P i j * (V j t - V j (β j)) := by
      simp only [α, α']
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib,
        Finset.sum_eq_single_of_mem j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)]
      · rw [hβ', Function.update_self]; ring
      · intro k _ hkj
        rw [hβ', Function.update_of_ne hkj]; ring
    have he : α' - α ≠ 0 := by
      rw [hαα]; exact mul_ne_zero hPij (sub_ne_zero.mpr hVt)
    set γ := ∑ k ∈ Finset.univ.erase i, G k (β k) *
          (A k + ∑ j ∈ Finset.univ.erase i, P k j * V j (β j))
    set γ' := ∑ k ∈ Finset.univ.erase i, G k (β' k) *
          (A k + ∑ j ∈ Finset.univ.erase i, P k j * V j (β' j))
    set κ := ∑ k ∈ Finset.univ.erase i, G k (β k) * P k i
    set κ' := ∑ k ∈ Finset.univ.erase i, G k (β' k) * P k i
    have haff : ∀ s ∈ W i, G i s = -(γ' - γ) / (α' - α) + (-(κ' - κ) / (α' - α)) * V i s := by
      intro s hs
      have e1 := hE β hβ i s hs
      have e2 := hE β' hβ'W i s hs
      field_simp
      linear_combination e2 - e1
    set a := -(γ' - γ) / (α' - α)
    set k0 := -(κ' - κ) / (α' - α)
    have hk0 : k0 = 0 := by
      obtain ⟨s1, s2, s3, h1, h2, h3, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp (hW3 i)
      have q : ∀ s ∈ W i, (k0 * P i i) * V i s ^ 2 + (a * P i i + k0 * α + κ) * V i s +
          (a * α + γ) = 0 := by
        intro s hs
        have := hE β hβ i s hs
        rw [haff s hs] at this
        linear_combination this
      have := quad3 _ _ _ _ _ _ (fun h => h12 (hV i h1 h2 h)) (fun h => h13 (hV i h1 h3 h))
        (fun h => h23 (hV i h2 h3 h)) (q s1 h1) (q s2 h2) (q s3 h3)
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (hdiag i)
    intro s hs
    rw [haff s hs, haff (β i) (hβ i), hk0]; ring
  -- Step C: the constants are in the kernel
  set a : Fin n → ℝ := fun k => G k (β k) with ha
  have hrow : ∀ i, ∑ k, a k * P k i = 0 := by
    intro i
    obtain ⟨s1, h1, hne⟩ := Finset.exists_mem_ne (show 1 < (W i).card by have := hW3 i; omega)
      (β i)
    have hVne : V i s1 ≠ V i (β i) := fun h => hne (hV i h1 (hβ i) h)
    have e1 := hE β hβ i s1 h1
    have e2 := hE β hβ i (β i) (hβ i)
    rw [hconst i s1 h1] at e1
    have : (G i (β i) * P i i + ∑ k ∈ Finset.univ.erase i, G k (β k) * P k i) *
        (V i s1 - V i (β i)) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h | h
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      exact h
    · exact absurd (sub_eq_zero.mp h) hVne
  have hall := hker a hrow
  -- Step D
  intro i c hc
  rw [hconst i c hc]
  have h0 := hF β hβ
  have : ∑ k, G k (β k) * Xf A P V β k = a i * ∑ k, Xf A P V β k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show a k * _ = _
    rw [hall k i]
  rw [this] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd h (hsum β hβ)

end PS1


open ProcureAssort.Hotelling

namespace PS1

variable {n : ℕ}

lemma cstar_le (ℓ : Fin n → ℝ) (hn : 2 ≤ n) (i : Fin n) (h : i.val + 1 < n) :
    cstar ℓ hn ≤ ℓ ⟨i.val + 1, h⟩ - ℓ i := by
  unfold cstar
  exact Finset.inf'_le _ (Finset.mem_univ (⟨i.val, by omega⟩ : Fin (n - 1)))

lemma cstar_pos (ℓ : Fin n → ℝ) (hn : 2 ≤ n) (hℓ : StrictMono ℓ) : 0 < cstar ℓ hn := by
  obtain ⟨i, hi⟩ : ∃ i : Fin (n - 1), cstar ℓ hn =
      ℓ ⟨i.val + 1, by omega⟩ - ℓ ⟨i.val, by omega⟩ := by
    unfold cstar
    exact (Finset.exists_mem_eq_inf' _ _).imp fun i h => h.2
  rw [hi]
  apply sub_pos.mpr
  apply hℓ
  rw [Fin.lt_def]
  simp

lemma cstar_gap (ℓ : Fin n → ℝ) (hn : 2 ≤ n) (hℓ : StrictMono ℓ) (i j : Fin n) (hij : i < j) :
    cstar ℓ hn ≤ ℓ j - ℓ i := by
  have hlt : i.val < j.val := hij
  have h1 := cstar_le ℓ hn i (by omega)
  have h2 : ℓ ⟨i.val + 1, by omega⟩ ≤ ℓ j := hℓ.monotone (by rw [Fin.le_def]; simp; omega)
  linarith

lemma cstar_abs (ℓ : Fin n → ℝ) (hn : 2 ≤ n) (hℓ : StrictMono ℓ) (i j : Fin n) (hij : i ≠ j) :
    cstar ℓ hn ≤ |ℓ j - ℓ i| := by
  rcases lt_or_gt_of_ne hij with h | h
  · have := cstar_gap ℓ hn hℓ i j h
    rw [abs_of_pos (by linarith [cstar_pos ℓ hn hℓ])]; exact this
  · have := cstar_gap ℓ hn hℓ j i h
    rw [abs_of_neg (by linarith [cstar_pos ℓ hn hℓ])]; linarith

lemma chain_close (ℓ : Fin n → ℝ) (δ : ℝ) (v : Fin n → ℝ)
    (hv : ∀ i : Fin n, ∀ h : i.val + 1 < n, |v ⟨i.val + 1, h⟩ - v i| ≤ δ * (ℓ ⟨i.val + 1, h⟩ - ℓ i) / 4) :
    ∀ i j : Fin n, i ≤ j → |v j - v i| ≤ δ * (ℓ j - ℓ i) / 4 := by
  intro i
  suffices H : ∀ m (hm : m < n), i.val ≤ m →
      |v ⟨m, hm⟩ - v i| ≤ δ * (ℓ ⟨m, hm⟩ - ℓ i) / 4 by
    intro j hij
    exact H j.val j.isLt hij
  intro m
  induction m with
  | zero =>
    intro hm him
    have : (⟨0, hm⟩ : Fin n) = i := Fin.ext (by simp; omega)
    rw [this]; simp
  | succ m ih =>
    intro hm him
    rcases Nat.eq_or_lt_of_le him with e | e
    · have : (⟨m + 1, hm⟩ : Fin n) = i := Fin.ext (by simp; omega)
      rw [this]; simp
    · have h1 := ih (by omega) (by omega)
      have h2 := hv ⟨m, by omega⟩ hm
      calc |v ⟨m + 1, hm⟩ - v i|
          ≤ |v ⟨m + 1, hm⟩ - v ⟨m, by omega⟩| + |v ⟨m, by omega⟩ - v i| := abs_sub_le _ _ _
        _ ≤ δ * (ℓ ⟨m + 1, hm⟩ - ℓ ⟨m, by omega⟩) / 4 + δ * (ℓ ⟨m, by omega⟩ - ℓ i) / 4 :=
            add_le_add h2 h1
        _ = δ * (ℓ ⟨m + 1, hm⟩ - ℓ i) / 4 := by ring

lemma succ_lem (S : Finset ℝ) (v : ℝ → ℝ) (hv : StrictMonoOn v S) (g : ℝ)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ c ∈ S, ¬ (a < c ∧ c < b)) → v b - v a ≤ g)
    (c : ℝ) (hc : c ∈ S) (h : (S.filter (c < ·)).Nonempty) :
    ∃ s ∈ S, c < s ∧ 0 < v s - v c ∧ v s - v c ≤ g ∧ ∀ d ∈ S, c < d → s ≤ d := by
  have hm := Finset.mem_filter.mp (Finset.min'_mem _ h)
  refine ⟨_, hm.1, hm.2, sub_pos.mpr (hv hc hm.1 hm.2), hgap c hc _ hm.1 hm.2 ?_, ?_⟩
  · intro d hd ⟨h1, h2⟩
    have := Finset.min'_le (S.filter (c < ·)) d (Finset.mem_filter.mpr ⟨hd, h1⟩)
    exact absurd h2 (not_lt.mpr this)
  · intro d hd h1
    exact Finset.min'_le (S.filter (c < ·)) d (Finset.mem_filter.mpr ⟨hd, h1⟩)

lemma pred_lem (S : Finset ℝ) (v : ℝ → ℝ) (hv : StrictMonoOn v S) (g : ℝ)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ c ∈ S, ¬ (a < c ∧ c < b)) → v b - v a ≤ g)
    (c : ℝ) (hc : c ∈ S) (h : (S.filter (· < c)).Nonempty) :
    ∃ s ∈ S, s < c ∧ 0 < v c - v s ∧ v c - v s ≤ g ∧ ∀ d ∈ S, d < c → d ≤ s := by
  have hm := Finset.mem_filter.mp (Finset.max'_mem _ h)
  refine ⟨_, hm.1, hm.2, sub_pos.mpr (hv hm.1 hc hm.2), hgap _ hm.1 c hc hm.2 ?_, ?_⟩
  · intro d hd ⟨h1, h2⟩
    have := Finset.le_max' (S.filter (· < c)) d (Finset.mem_filter.mpr ⟨hd, h2⟩)
    exact absurd h1 (not_lt.mpr this)
  · intro d hd h1
    exact Finset.le_max' (S.filter (· < c)) d (Finset.mem_filter.mpr ⟨hd, h1⟩)

lemma window_card (S : Finset ℝ) (v : ℝ → ℝ) (hv : StrictMonoOn v S) (g : ℝ)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ c ∈ S, ¬ (a < c ∧ c < b)) → v b - v a ≤ g)
    (c0 : ℝ) (hc0 : c0 ∈ S) (h3 : 3 ≤ S.card) :
    2 < (S.filter (fun c => |v c - v c0| ≤ 2 * g)).card := by
  classical
  rw [Finset.two_lt_card_iff]
  have mem : ∀ c ∈ S, |v c - v c0| ≤ 2 * g → c ∈ S.filter (fun c => |v c - v c0| ≤ 2 * g) :=
    fun c hc h => Finset.mem_filter.mpr ⟨hc, h⟩
  have hc0m : c0 ∈ S.filter (fun c => |v c - v c0| ≤ 2 * g) := mem c0 hc0 (by
    have := hgap
    simp only [sub_self, abs_zero]
    -- g ≥ 0 follows from any consecutive pair; get one
    by_contra hneg
    push Not at hneg
    have hcard : 1 < S.card := by omega
    obtain ⟨d, hd, hne⟩ := Finset.exists_mem_ne hcard c0
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨s, hs, -, hpos, hle, -⟩ := succ_lem S v hv g hgap d hd
        ⟨c0, Finset.mem_filter.mpr ⟨hc0, hlt⟩⟩
      linarith
    · obtain ⟨s, hs, -, hpos, hle, -⟩ := succ_lem S v hv g hgap c0 hc0
        ⟨d, Finset.mem_filter.mpr ⟨hd, hlt⟩⟩
      linarith)
  by_cases hb : (S.filter (· < c0)).Nonempty
  · obtain ⟨p, hp, hpc, hp1, hp2, hmax⟩ := pred_lem S v hv g hgap c0 hc0 hb
    by_cases ha : (S.filter (c0 < ·)).Nonempty
    · obtain ⟨s, hs, hcs, hs1, hs2, -⟩ := succ_lem S v hv g hgap c0 hc0 ha
      refine ⟨p, c0, s, mem p hp ?_, hc0m, mem s hs ?_, hpc.ne, (hpc.trans hcs).ne, hcs.ne⟩
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos hs1]; linarith
    · have hpb : (S.filter (· < p)).Nonempty := by
        by_contra hpb
        have hsub : S ⊆ {p, c0} := by
          intro d hd
          rcases lt_trichotomy d c0 with h | h | h
          · rcases lt_trichotomy d p with h' | h' | h'
            · exact absurd ⟨d, Finset.mem_filter.mpr ⟨hd, h'⟩⟩ hpb
            · simp [h']
            · exact absurd (hmax d hd h) (not_le.mpr h')
          · simp [h]
          · exact absurd ⟨d, Finset.mem_filter.mpr ⟨hd, h⟩⟩ ha
        have := (Finset.card_le_card hsub).trans (Finset.card_le_two)
        omega
      obtain ⟨q, hq, hqp, hq1, hq2, -⟩ := pred_lem S v hv g hgap p hp hpb
      refine ⟨q, p, c0, mem q hq ?_, mem p hp ?_, hc0m, hqp.ne, (hqp.trans hpc).ne, hpc.ne⟩
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_neg (by linarith)]; linarith
  · have ha : (S.filter (c0 < ·)).Nonempty := by
      by_contra ha
      have hsub : S ⊆ {c0} := by
        intro d hd
        rcases lt_trichotomy d c0 with h | h | h
        · exact absurd ⟨d, Finset.mem_filter.mpr ⟨hd, h⟩⟩ hb
        · simp [h]
        · exact absurd ⟨d, Finset.mem_filter.mpr ⟨hd, h⟩⟩ ha
      have := Finset.card_le_card hsub
      simp at this
      omega
    obtain ⟨s, hs, hcs, hs1, hs2, hmin⟩ := succ_lem S v hv g hgap c0 hc0 ha
    have hsa : (S.filter (s < ·)).Nonempty := by
      by_contra hsa
      have hsub : S ⊆ {c0, s} := by
        intro d hd
        rcases lt_trichotomy d c0 with h | h | h
        · exact absurd ⟨d, Finset.mem_filter.mpr ⟨hd, h⟩⟩ hb
        · simp [h]
        · rcases lt_trichotomy d s with h' | h' | h'
          · exact absurd (hmin d hd h) (not_le.mpr h')
          · simp [h']
          · exact absurd ⟨d, Finset.mem_filter.mpr ⟨hd, h'⟩⟩ hsa
      have := (Finset.card_le_card hsub).trans (Finset.card_le_two)
      omega
    obtain ⟨t, ht, hst, ht1, ht2, -⟩ := succ_lem S v hv g hgap s hs hsa
    refine ⟨c0, s, t, hc0m, mem s hs ?_, mem t ht ?_, hcs.ne, (hcs.trans hst).ne, hst.ne⟩
    · rw [abs_of_pos hs1]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

end PS1


open ProcureAssort.Hotelling

namespace PS1

variable {n : ℕ}

lemma all_active (ℓ : Fin n → ℝ) (δ : ℝ) (hδ : 0 < δ) (p : Fin n → ℝ)
    (hstr : ∀ i j, i ≠ j → |p i - p j| < δ * |ℓ j - ℓ i|) : hotQ ℓ δ p = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  rw [mem_hotQ']
  intro j
  by_cases hij : i = j
  · subst hij; rw [sub_self, sub_self, abs_zero, mul_zero]
  · exact (le_abs_self _).trans (hstr i j hij).le

lemma all_pos (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (hn : 2 ≤ n) (p : Fin n → ℝ)
    (hstr : ∀ i j, i ≠ j → |p i - p j| < δ * |ℓ j - ℓ i|) (k : Fin n) :
    0 < hotDemand ℓ δ p k := by
  classical
  have hQ := all_active ℓ δ hδ p hstr
  have hk : k ∈ hotQ ℓ δ p := by rw [hQ]; exact Finset.mem_univ k
  rw [hd_eq ℓ δ p k hk]
  have hl0 := leftPart_nonneg ℓ hℓ0 δ hδ p k hk
  have hr0 := rightPart_nonneg ℓ hℓ1 δ hδ p k hk
  have h2δ : 0 < 2 * δ := by linarith
  obtain ⟨j, hjk⟩ : ∃ j : Fin n, j ≠ k := by
    by_cases h0 : k.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at h0; simp at h0⟩
    · exact ⟨⟨0, by omega⟩, fun h => by rw [← h] at h0; simp at h0⟩
  rcases lt_or_gt_of_ne hjk with h | h
  · suffices 0 < leftPart ℓ δ p k by linarith
    have hne : ((hotQ ℓ δ p).filter (· < k)).Nonempty :=
      ⟨j, Finset.mem_filter.mpr ⟨by rw [hQ]; exact Finset.mem_univ j, h⟩⟩
    unfold leftPart
    rw [dif_pos hne]
    have hLm := Finset.mem_filter.mp (Finset.max'_mem _ hne)
    have := hstr _ k (ne_of_lt hLm.2)
    apply div_pos _ h2δ
    have := neg_abs_le (p (((hotQ ℓ δ p).filter (· < k)).max' hne) - p k)
    linarith
  · suffices 0 < rightPart ℓ δ p k by linarith
    have hne : ((hotQ ℓ δ p).filter (k < ·)).Nonempty :=
      ⟨j, Finset.mem_filter.mpr ⟨by rw [hQ]; exact Finset.mem_univ j, h⟩⟩
    unfold rightPart
    rw [dif_pos hne]
    have hRm := Finset.mem_filter.mp (Finset.min'_mem _ hne)
    have h5 := hstr _ k (ne_of_gt hRm.2)
    rw [abs_sub_comm (ℓ k)] at h5
    apply div_pos _ h2δ
    have := neg_abs_le (p (((hotQ ℓ δ p).filter (k < ·)).min' hne) - p k)
    linarith

lemma nb_exists (hn : 2 ≤ n) (i : Fin n) : ∃ j, Adjacent Finset.univ i j := by
  by_cases h0 : i.val = 0
  · refine ⟨⟨1, by omega⟩, Finset.mem_univ _, Finset.mem_univ _, ?_, ?_⟩
    · intro h; rw [h] at h0; simp at h0
    · intro m _ ⟨h1, h2⟩
      have hlt : i < ⟨1, by omega⟩ := by rw [Fin.lt_def]; simp; omega
      rw [min_eq_left hlt.le] at h1
      rw [max_eq_right hlt.le] at h2
      rw [Fin.lt_def] at h1 h2
      simp at h2
      omega
  · refine ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, Finset.mem_univ _, ?_, ?_⟩
    · intro h; have := congrArg Fin.val h; simp at this; omega
    · intro m _ ⟨h1, h2⟩
      have hlt : (⟨i.val - 1, by omega⟩ : Fin n) < i := by rw [Fin.lt_def]; simp; omega
      rw [min_eq_right hlt.le] at h1
      rw [max_eq_left hlt.le] at h2
      rw [Fin.lt_def] at h1 h2
      simp at h1
      omega

lemma pathA_diag_ne (hn : 2 ≤ n) (i : Fin n) : pathA Finset.univ i i ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := nb_exists hn i
  unfold pathA
  rw [if_pos ⟨Finset.mem_univ _, Finset.mem_univ _⟩, if_pos rfl]
  have : 0 < (Finset.univ.filter (fun k => Adjacent Finset.univ i k)).card :=
    Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  have : (0 : ℝ) < ((Finset.univ.filter (fun k => Adjacent Finset.univ i k)).card : ℝ) := by
    exact_mod_cast this
  linarith

lemma pathA_nb (hn : 2 ≤ n) (i : Fin n) : ∃ j, j ≠ i ∧ pathA Finset.univ i j ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := nb_exists hn i
  refine ⟨j, hj.2.2.1.symm, ?_⟩
  unfold pathA
  rw [if_pos ⟨Finset.mem_univ _, Finset.mem_univ _⟩, if_neg hj.2.2.1, if_pos hj]
  norm_num

lemma pathA_ker' (Q : Finset (Fin n)) (w : Fin n → ℝ)
    (h : ∀ i ∈ Q, ∑ j ∈ Q, pathA Q i j * w j = 0) (hne : Q.Nonempty) :
    ∀ i ∈ Q, w i = w (Q.min' hne) := by
  classical
  have hrow : ∀ i ∈ Q, ∑ j ∈ Q.filter (fun k => Adjacent Q i k), (w j - w i) = 0 := by
    intro i hi; rw [← pathA_row' Q i hi]; exact h i hi
  set F : Fin n → Fin n → ℝ := fun i j => if Adjacent Q i j then w i * (w j - w i) else 0
  have hS : ∑ i ∈ Q, ∑ j ∈ Q, F i j = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have : ∑ j ∈ Q, F i j = w i * ∑ j ∈ Q.filter (fun k => Adjacent Q i k), (w j - w i) := by
      rw [Finset.mul_sum, Finset.sum_filter]
    rw [this, hrow i hi, mul_zero]
  have hS' : ∑ i ∈ Q, ∑ j ∈ Q, F j i = 0 := by rw [Finset.sum_comm]; exact hS
  have hsq : ∑ i ∈ Q, ∑ j ∈ Q, (if Adjacent Q i j then (w j - w i) ^ 2 else 0) = 0 := by
    have : ∀ i ∈ Q, ∀ j ∈ Q, (if Adjacent Q i j then (w j - w i) ^ 2 else 0) = -(F i j + F j i) := by
      intro i _ j _
      simp only [F]
      by_cases hij : Adjacent Q i j
      · rw [if_pos hij, if_pos hij, if_pos (adjacent_symm' Q i j hij)]; ring
      · have : ¬ Adjacent Q j i := fun h => hij (adjacent_symm' Q j i h)
        rw [if_neg hij, if_neg hij, if_neg this]; ring
    rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => this i hi j hj]
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, hS, hS']
    ring
  have hadj : ∀ i ∈ Q, ∀ j ∈ Q, Adjacent Q i j → w j = w i := by
    intro i hi j hj hij
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs <;> positivity)).mp hsq i hi
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by
      split_ifs <;> positivity)).mp h0 j hj
    rw [if_pos hij] at h1
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
    linarith
  intro i
  induction hk : i.val using Nat.strong_induction_on generalizing i with
  | _ k ih =>
  intro hi
  by_cases hlt : (Q.filter (· < i)).Nonempty
  · set L := (Q.filter (· < i)).max' hlt with hL
    have hLm := Finset.mem_filter.mp (Finset.max'_mem _ hlt)
    rw [← hL] at hLm
    have hAdj : Adjacent Q L i := by
      refine ⟨hLm.1, hi, ne_of_lt hLm.2, fun k hk ⟨h1, h2⟩ => ?_⟩
      rw [min_eq_left hLm.2.le] at h1
      rw [max_eq_right hLm.2.le] at h2
      have : k ≤ L := Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hk, h2⟩)
      exact absurd h1 (not_lt.mpr this)
    rw [hadj L hLm.1 i hi hAdj]
    exact ih L.val (hk ▸ hLm.2) L rfl hLm.1
  · have : Q.min' hne = i := by
      apply le_antisymm (Finset.min'_le _ _ hi)
      by_contra hc
      push Not at hc
      exact hlt ⟨_, Finset.mem_filter.mpr ⟨Finset.min'_mem _ hne, hc⟩⟩
    rw [this]

end PS1


open ProcureAssort.Hotelling PS1

theorem solution
    (n : ℕ) (hn : 2 ≤ n)
    (Θ : Fin n → Finset ℝ) (hΘ : ∀ i, ∀ c ∈ Θ i, 0 < c)
    (f : Fin n → ℝ → ℝ) (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (hf1 : ∀ i, ∑ c ∈ Θ i, f i c = 1)
    (hreg : ∀ i, StrictMonoOn (virtualCost Θ f i) ((Θ i : Finset ℝ) : Set ℝ))
    (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ)
    (h1 : ∃ θ : Profile Θ, ∀ i : Fin n, ∀ h : i.val + 1 < n,
      |virtualCost Θ f ⟨i.val + 1, h⟩ (θ ⟨i.val + 1, h⟩) - virtualCost Θ f i (θ i)|
        ≤ δ * (ℓ ⟨i.val + 1, h⟩ - ℓ i) / 4)
    (h2 : ∀ i, 3 ≤ (Θ i).card ∧ ∀ a ∈ Θ i, ∀ b ∈ Θ i, a < b → (∀ c ∈ Θ i, ¬ (a < c ∧ c < b)) →
      virtualCost Θ f i b - virtualCost Θ f i a ≤ δ * cstar ℓ hn / 8)
    (a : Profile Θ → Fin n → ℝ) (b : Fin n → ℝ → ℝ)
    (h14 : ∀ θ : Profile Θ, ∀ j ∈ activeSet Θ f ℓ δ θ,
      (∑ i ∈ activeSet Θ f ℓ δ θ, a θ i * pathA (activeSet Θ f ℓ δ θ) i j)
        + b j (θ j) * probOthers f j θ * xstar Θ f ℓ δ θ j = 0) :
    ∀ i, ∀ c ∈ Θ i, (∃ θ : Profile Θ, (θ i : ℝ) = c ∧ 0 < xstar Θ f ℓ δ θ i) → b i c = 0 := by
  classical
  obtain ⟨θs, hθs⟩ := h1
  have hc : 0 < cstar ℓ hn := cstar_pos ℓ hn hℓ
  have hF3 := lemma_F_3 n hn Θ hΘ f hf0 hf1 hreg ℓ hℓ hℓ0 hℓ1 δ hδ a b h14
  obtain ⟨-, hopt, -, -, -⟩ := proposition_3_2 n hn Θ hΘ f hf0 hf1 hreg ℓ hℓ hℓ0 hℓ1 δ hδ
  have hxnn : ∀ θ k, 0 ≤ xstar Θ f ℓ δ θ k := fun θ k => (hopt θ).1.1 k
  have hxsum : ∀ θ, ∑ k, xstar Θ f ℓ δ θ k = 1 := fun θ => (hopt θ).1.2
  -- monotonicity of own demand in own cost
  have hmono : ∀ (θ : Profile Θ) (i : Fin n) (bb : ↥(Θ i)), (θ i : ℝ) ≤ bb →
      xstar Θ f ℓ δ (Function.update θ i bb) i ≤ xstar Θ f ℓ δ θ i := by
    intro θ i bb hb
    rcases eq_or_lt_of_le hb with h | h
    · have : Function.update θ i bb = θ := by
        rw [Function.update_eq_self_iff]; exact Subtype.ext h.symm
      rw [this]
    · set θ' := Function.update θ i bb
      set V := vvec Θ f θ
      set V' := vvec Θ f θ'
      set y := xstar Θ f ℓ δ θ
      set y' := xstar Θ f ℓ δ θ'
      have hvi : V i < V' i := by
        simp only [V, V', vvec, θ', Function.update_self]
        exact hreg i (θ i).2 bb.2 h
      have hsum : ∀ z : Fin n → ℝ, ∑ j, V' j * z j - ∑ j, V j * z j = (V' i - V i) * z i := by
        intro z
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
        · ring
        · intro j _ hj
          simp only [V, V', vvec, θ', Function.update_of_ne hj]; ring
        · simp
      obtain ⟨hy, hyo⟩ := hopt θ
      obtain ⟨hy', hyo'⟩ := hopt θ'
      have h1 := hyo y' hy'
      have h2 := hyo' y hy
      unfold CS at h1 h2
      have e1 := hsum y
      have e2 := hsum y'
      have : (V' i - V i) * y' i ≤ (V' i - V i) * y i := by linarith
      exact le_of_mul_le_mul_left this (by linarith)
  -- closeness of the reference profile
  have hvs := chain_close ℓ δ (fun k => virtualCost Θ f k (θs k)) hθs
  -- the window
  set W : Fin n → Finset ℝ := fun k => (Θ k).filter
    (fun x => |virtualCost Θ f k x - virtualCost Θ f k (θs k)| ≤ 2 * (δ * cstar ℓ hn / 8)) with hW
  have hWsub : ∀ k, W k ⊆ Θ k := fun k => Finset.filter_subset _ _
  have hθsW : ∀ k, (θs k : ℝ) ∈ W k := fun k => Finset.mem_filter.mpr ⟨(θs k).2, by
    rw [sub_self, abs_zero]; positivity⟩
  have hW3 : ∀ k, 2 < (W k).card := fun k =>
    window_card (Θ k) (virtualCost Θ f k) (hreg k) (δ * cstar ℓ hn / 8) (h2 k).2 (θs k) (θs k).2
      (h2 k).1
  have hWne : ∀ k, (W k).Nonempty := fun k => Finset.card_pos.mp (by have := hW3 k; omega)
  -- strict activity on the window
  have hstr : ∀ θ : Profile Θ, (∀ k, (θ k : ℝ) ∈ W k) →
      ∀ i j, i ≠ j → |vvec Θ f θ i - vvec Θ f θ j| < δ * |ℓ j - ℓ i| := by
    intro θ hθ
    have hlt : ∀ i j, i < j → |vvec Θ f θ i - vvec Θ f θ j| < δ * |ℓ j - ℓ i| := by
      intro i j hij
      have hi := (Finset.mem_filter.mp (hθ i)).2
      have hj := (Finset.mem_filter.mp (hθ j)).2
      have hij' := hvs i j hij.le
      have hgap := cstar_gap ℓ hn hℓ i j hij
      have hℓij : ℓ i < ℓ j := hℓ hij
      beta_reduce at hij'
      rw [abs_of_pos (show 0 < ℓ j - ℓ i by linarith)]
      simp only [vvec]
      have t1 := abs_sub_le (virtualCost Θ f i (θ i)) (virtualCost Θ f i (θs i))
        (virtualCost Θ f j (θ j))
      have t2 := abs_sub_le (virtualCost Θ f i (θs i)) (virtualCost Θ f j (θs j))
        (virtualCost Θ f j (θ j))
      rw [abs_sub_comm (virtualCost Θ f i (θs i)) (virtualCost Θ f j (θs j)),
        abs_sub_comm (virtualCost Θ f j (θs j)) (virtualCost Θ f j (θ j))] at t2
      have t3 := mul_le_mul_of_nonneg_left hgap hδ.le
      have t4 := mul_pos hδ hc
      linarith
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hlt i j h
    · rw [abs_sub_comm, abs_sub_comm (ℓ j)]; exact hlt j i h
  have hact : ∀ θ : Profile Θ, (∀ k, (θ k : ℝ) ∈ W k) → activeSet Θ f ℓ δ θ = Finset.univ :=
    fun θ hθ => all_active ℓ δ hδ _ (hstr θ hθ)
  have hposW : ∀ θ : Profile Θ, (∀ k, (θ k : ℝ) ∈ W k) → ∀ k, 0 < xstar Θ f ℓ δ θ k :=
    fun θ hθ k => all_pos ℓ hℓ hℓ0 hℓ1 δ hδ hn _ (hstr θ hθ) k
  -- profile from a window point
  have mkP : ∀ θ : Fin n → ℝ, (∀ k, θ k ∈ W k) →
      ∃ θp : Profile Θ, (∀ k, (θp k : ℝ) = θ k) := fun θ hθ =>
    ⟨fun k => ⟨θ k, hWsub k (hθ k)⟩, fun k => rfl⟩
  have hX : ∀ θp : Profile Θ, (∀ k, (θp k : ℝ) ∈ W k) → ∀ k,
      Xf (Bc ℓ δ Finset.univ) (pathA Finset.univ) (fun k => virtualCost Θ f k)
        (fun k => (θp k : ℝ)) k = 2 * δ * xstar Θ f ℓ δ θp k := by
    intro θp hθ k
    have hQ := hact θp hθ
    unfold activeSet at hQ
    have hk : k ∈ hotQ ℓ δ (vvec Θ f θp) := by rw [hQ]; exact Finset.mem_univ k
    unfold xstar
    rw [rep ℓ δ hδ _ k hk, hQ]
    rfl
  -- Step 1.a
  have h1a : ∀ i, ∀ x ∈ W i, b i x / f i x = 0 := by
    apply abs_step W (fun k x => b k x / f k x) (fun k => virtualCost Θ f k)
      (Bc ℓ δ Finset.univ) (pathA Finset.univ) hW3
    · intro i
      exact (hreg i).injOn.mono (by intro x hx; exact hWsub i hx)
    · exact pathA_diag_ne hn
    · exact pathA_nb hn
    · intro w hw i j
      have hk := pathA_ker' Finset.univ w (fun i _ => by
        rw [← hw i]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [pathA_symm]; ring) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      rw [hk i (Finset.mem_univ _), hk j (Finset.mem_univ _)]
    · intro θ hθ
      obtain ⟨θp, hθp⟩ := mkP θ hθ
      have hθp' : (fun k => (θp k : ℝ)) = θ := funext hθp
      have hθW : ∀ k, (θp k : ℝ) ∈ W k := fun k => by rw [hθp]; exact hθ k
      rw [← hθp', Finset.sum_congr rfl fun k _ => hX θp hθW k, ← Finset.mul_sum, hxsum]
      positivity
    · intro θ hθ
      obtain ⟨θp, hθp⟩ := mkP θ hθ
      have hθp' : (fun k => (θp k : ℝ)) = θ := funext hθp
      have hθW : ∀ k, (θp k : ℝ) ∈ W k := fun k => by rw [hθp]; exact hθ k
      rw [← hθp']
      simp only
      rw [Finset.sum_congr rfl fun k _ => by rw [hX θp hθW k]]
      have := hF3 θp
      rw [hact θp hθW] at this
      calc ∑ k, b k (θp k) / f k (θp k) * (2 * δ * xstar Θ f ℓ δ θp k)
          = 2 * δ * ∑ k, b k (θp k) / f k (θp k) * xstar Θ f ℓ δ θp k := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
        _ = 0 := by rw [this, mul_zero]
  -- Step 1.b, low costs
  have hlo : ∀ k, ∀ x ∈ Θ k, x ≤ (W k).min' (hWne k) → b k x / f k x = 0 := by
    intro k x hx hxlo
    have hlom := Finset.min'_mem (W k) (hWne k)
    set θ2 : Profile Θ := Function.update θs k ⟨x, hx⟩ with hθ2
    have hθ1 : Function.update θ2 k ⟨(W k).min' (hWne k), hWsub k hlom⟩ =
        Function.update θs k ⟨(W k).min' (hWne k), hWsub k hlom⟩ := by
      rw [hθ2, Function.update_idem]
    have hθ1W : ∀ j, ((Function.update θs k ⟨(W k).min' (hWne k), hWsub k hlom⟩) j : ℝ) ∈ W j := by
      intro j
      by_cases hjk : j = k
      · subst hjk; rw [Function.update_self]; exact hlom
      · rw [Function.update_of_ne hjk]; exact hθsW j
    have hpos1 := hposW _ hθ1W k
    have hle := hmono θ2 k ⟨(W k).min' (hWne k), hWsub k hlom⟩ (by
      rw [hθ2, Function.update_self]; exact hxlo)
    rw [hθ1] at hle
    have hpos2 : 0 < xstar Θ f ℓ δ θ2 k := lt_of_lt_of_le hpos1 hle
    have hkQ : k ∈ activeSet Θ f ℓ δ θ2 := by
      by_contra hc
      have : xstar Θ f ℓ δ θ2 k = 0 := hd_out ℓ δ _ k hc
      linarith
    have := hF3 θ2
    rw [Finset.sum_eq_single_of_mem k hkQ] at this
    · rw [hθ2, Function.update_self] at this
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · rw [← hθ2] at h; linarith
    · intro j _ hjk
      rw [hθ2, Function.update_of_ne hjk, h1a j _ (hθsW j), zero_mul]
  -- everything up to the top of the window is known
  have hknown : ∀ k, ∀ x ∈ Θ k, x ≤ (W k).max' (hWne k) → b k x / f k x = 0 := by
    intro k x hx hxhi
    by_cases hxW : x ∈ W k
    · exact h1a k x hxW
    · apply hlo k x hx
      by_contra hlt
      push Not at hlt
      apply hxW
      have hlom := Finset.min'_mem (W k) (hWne k)
      have him := Finset.max'_mem (W k) (hWne k)
      have e1 := (hreg k).monotoneOn (hWsub k hlom) hx hlt.le
      have e2 := (hreg k).monotoneOn hx (hWsub k him) hxhi
      have f1 := (Finset.mem_filter.mp hlom).2
      have f2 := (Finset.mem_filter.mp him).2
      refine Finset.mem_filter.mpr ⟨hx, abs_le.mpr ⟨?_, ?_⟩⟩
      · linarith [neg_abs_le (virtualCost Θ f k ((W k).min' (hWne k)) -
          virtualCost Θ f k (θs k))]
      · linarith [le_abs_self (virtualCost Θ f k ((W k).max' (hWne k)) -
          virtualCost Θ f k (θs k))]
  -- the minimal-counterexample induction
  have hmain : ∀ N, ∀ θ : Profile Θ,
      (∑ k, ((Θ k).filter (· < (θ k : ℝ))).card) = N →
      ∀ j, 0 < xstar Θ f ℓ δ θ j → b j (θ j) / f j (θ j) = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro θ hN j hxj
    by_contra hgj
    have hhi : ∀ m, b m (θ m) / f m (θ m) ≠ 0 → (W m).max' (hWne m) < θ m := fun m hm =>
      lt_of_not_ge fun h => hm (hknown m _ (θ m).2 h)
    have hkill : ∀ m j0, m ≠ j0 → 0 < xstar Θ f ℓ δ θ j0 → b j0 (θ j0) / f j0 (θ j0) ≠ 0 →
        (W m).max' (hWne m) < θ m →
        ∃ d ∈ Θ m, virtualCost Θ f m (θ m) - virtualCost Θ f m d ≤ δ * cstar ℓ hn / 8 ∧
          virtualCost Θ f m d + δ * |ℓ j0 - ℓ m| ≤ virtualCost Θ f j0 (θ j0) := by
      intro m j0 hmj hx0 hg0 hmhi
      have hmaxm := Finset.max'_mem (W m) (hWne m)
      obtain ⟨d, hd, hdlt, hdpos, hdle, -⟩ := pred_lem (Θ m) (virtualCost Θ f m) (hreg m)
        (δ * cstar ℓ hn / 8) (h2 m).2 (θ m) (θ m).2
        ⟨_, Finset.mem_filter.mpr ⟨hWsub m hmaxm, hmhi⟩⟩
      refine ⟨d, hd, hdle, ?_⟩
      set θ' : Profile Θ := Function.update θ m ⟨d, hd⟩ with hθ'
      have hmeas : (∑ k, ((Θ k).filter (· < (θ' k : ℝ))).card) < N := by
        rw [← hN]
        apply Finset.sum_lt_sum
        · intro k _
          by_cases hkm : k = m
          · subst hkm
            rw [hθ', Function.update_self]
            apply Finset.card_le_card
            intro e he
            rw [Finset.mem_filter] at he ⊢
            exact ⟨he.1, he.2.trans hdlt⟩
          · rw [hθ', Function.update_of_ne hkm]
        · refine ⟨m, Finset.mem_univ _, ?_⟩
          rw [hθ', Function.update_self]
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset]
          · exact ⟨d, Finset.mem_filter.mpr ⟨hd, hdlt⟩, fun h => lt_irrefl d
              (Finset.mem_filter.mp h).2⟩
          · intro e he
            rw [Finset.mem_filter] at he ⊢
            exact ⟨he.1, he.2.trans hdlt⟩
      have hθ'j0 : θ' j0 = θ j0 := by rw [hθ', Function.update_of_ne hmj.symm]
      have hnot : ¬ 0 < xstar Θ f ℓ δ θ' j0 := by
        intro hp
        have := ih _ hmeas θ' rfl j0 hp
        rw [hθ'j0] at this
        exact hg0 this
      by_contra hcon
      push Not at hcon
      apply hnot
      apply key ℓ hℓ hℓ0 hℓ1 δ hδ (vvec Θ f θ) (vvec Θ f θ') m j0 hmj.symm
      · simp only [vvec, hθ', Function.update_self]; linarith
      · intro k hk; simp only [vvec, hθ', Function.update_of_ne hk]
      · exact hx0
      · simp only [vvec, hθ', Function.update_self]; exact hcon
    have hjQ : j ∈ activeSet Θ f ℓ δ θ := by
      by_contra hc
      have : xstar Θ f ℓ δ θ j = 0 := hd_out ℓ δ _ j hc
      linarith
    obtain ⟨j', hj'Q, hj'j, hj'⟩ : ∃ j' ∈ activeSet Θ f ℓ δ θ, j' ≠ j ∧
        b j' (θ j') / f j' (θ j') * xstar Θ f ℓ δ θ j' ≠ 0 := by
      by_contra hall
      push Not at hall
      have := hF3 θ
      rw [Finset.sum_eq_single_of_mem j hjQ (fun k hk hkj => hall k hk hkj)] at this
      exact mul_ne_zero hgj hxj.ne' this
    have hg' : b j' (θ j') / f j' (θ j') ≠ 0 := left_ne_zero_of_mul hj'
    have hx' : 0 < xstar Θ f ℓ δ θ j' :=
      lt_of_le_of_ne (hxnn θ j') (Ne.symm (right_ne_zero_of_mul hj'))
    obtain ⟨d', -, hd'1, hd'2⟩ := hkill j' j hj'j hxj hgj (hhi j' hg')
    obtain ⟨d, -, hd1, hd2⟩ := hkill j j' hj'j.symm hx' hg' (hhi j hgj)
    have hcs := cstar_abs ℓ hn hℓ j' j hj'j
    rw [abs_sub_comm (ℓ j') (ℓ j)] at hd2
    have : δ * cstar ℓ hn ≤ δ * |ℓ j - ℓ j'| := mul_le_mul_of_nonneg_left hcs hδ.le
    have : 0 < δ * cstar ℓ hn := mul_pos hδ hc
    linarith
  intro i x hx ⟨θ, hθx, hpos⟩
  have := hmain _ θ rfl i hpos
  rw [hθx] at this
  rcases div_eq_zero_iff.mp this with h | h
  · exact h
  · exact absurd h (hf0 i x hx).ne'
