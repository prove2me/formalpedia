-- Prove2me | solution 1 for ReluMIP.Ideal.fm_projection_eq_system7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T03:18:25.462474+00:00
-- url     : https://prove2.me/submissions/32602977-15af-4bbc-83de-15cf86d2e679

import Mathlib
import Definitions.Def_ReluMIP_Ideal_Setting

namespace ReluMIP.Ideal

lemma wLb_le {η : ℕ} (w L U x : Fin η → ℝ) (hx : x ∈ box L U) (i : Fin η) :
    w i * Lbrev w L U i ≤ w i * x i := by
  obtain ⟨h1, h2⟩ := hx i
  unfold Lbrev
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left h1 h
  · exact mul_le_mul_of_nonpos_left h2 (le_of_lt (not_le.mp h))

lemma le_wUb {η : ℕ} (w L U x : Fin η → ℝ) (hx : x ∈ box L U) (i : Fin η) :
    w i * x i ≤ w i * Ubrev w L U i := by
  obtain ⟨h1, h2⟩ := hx i
  unfold Ubrev
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left h2 h
  · exact mul_le_mul_of_nonpos_left h1 (le_of_lt (not_le.mp h))

/-- Core inequality (7c) for any index set. -/
lemma rhs7c_le {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (x : Fin η → ℝ) (y z : ℝ)
    (h6a : affineFn w b x ≤ y) (hx : x ∈ box L U) (hy : 0 ≤ y) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (I : Finset (Fin η)) : rhs7c w b L U I x z ≤ y := by
  have hsplit : ∀ f : Fin η → ℝ, ∑ i ∈ Finset.univ \ I, f i + ∑ i ∈ I, f i = ∑ i, f i :=
    fun f => Finset.sum_sdiff (Finset.subset_univ I)
  set XI := ∑ i ∈ I, w i * x i
  set XJ := ∑ i ∈ Finset.univ \ I, w i * x i
  set UI := ∑ i ∈ I, w i * Ubrev w L U i
  set LJ := ∑ i ∈ Finset.univ \ I, w i * Lbrev w L U i
  have hXI : XI ≤ UI := Finset.sum_le_sum fun i _ => le_wUb w L U x hx i
  have hXJ : LJ ≤ XJ := Finset.sum_le_sum fun i _ => wLb_le w L U x hx i
  have hwx : ∑ i, w i * x i = XI + XJ := by rw [← hsplit]; ring
  have hr : rhs7c w b L U I x z = XI - UI * (1 - z) + (b + LJ) * z := by
    unfold rhs7c
    have : ∑ i ∈ I, w i * (x i - Ubrev w L U i * (1 - z)) =
        ∑ i ∈ I, (w i * x i - w i * Ubrev w L U i * (1 - z)) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [this, Finset.sum_sub_distrib, ← Finset.sum_mul]
  unfold affineFn at h6a
  rw [hr]
  rcases le_or_gt 0 (b + LJ + UI) with h | h
  · have := mul_nonneg (sub_nonneg.mpr hz1) h
    nlinarith
  · have := mul_nonpos_of_nonneg_of_nonpos hz0 h.le
    nlinarith

lemma mul_max_nonpos (a b c : ℝ) (ha : a ≤ 0) : a * max b c = min (a * b) (a * c) := by
  rcases le_total b c with h | h
  · rw [max_eq_right h, min_eq_right (mul_le_mul_of_nonpos_left h ha)]
  · rw [max_eq_left h, min_eq_left (mul_le_mul_of_nonpos_left h ha)]

lemma mul_min_nonpos (a b c : ℝ) (ha : a ≤ 0) : a * min b c = max (a * b) (a * c) := by
  rcases le_total b c with h | h
  · rw [min_eq_left h, max_eq_left (mul_le_mul_of_nonpos_left h ha)]
  · rw [min_eq_right h, max_eq_right (mul_le_mul_of_nonpos_left h ha)]

/-- Core lemma: every point of the LP relaxation of (6) admits a split `x¹ = u` (scaled copy)
as in (5). -/
lemma exists_split {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (x : Fin η → ℝ) (y z : ℝ)
    (h : (x, y, z) ∈ relax6 w b L U) :
    ∃ u : Fin η → ℝ, (∀ i, L i * z ≤ u i ∧ u i ≤ U i * z) ∧
      (∀ i, L i * (1 - z) ≤ x i - u i ∧ x i - u i ≤ U i * (1 - z)) ∧
      ∑ i, w i * u i + b * z = y := by
  obtain ⟨h6a, h6b, hx, hy, hz0, hz1⟩ := h
  simp only at h6a h6b hx hy hz0 hz1
  have hsplit : ∀ (I : Finset (Fin η)) (f : Fin η → ℝ),
      ∑ i ∈ Finset.univ \ I, f i + ∑ i ∈ I, f i = ∑ i, f i :=
    fun I f => Finset.sum_sdiff (Finset.subset_univ I)
  set lo : Fin η → ℝ := fun i => max (L i * z) (x i - U i * (1 - z)) with hlo
  set hi : Fin η → ℝ := fun i => min (U i * z) (x i - L i * (1 - z)) with hhi
  have hlohi : ∀ i, lo i ≤ hi i := by
    intro i
    obtain ⟨h1, h2⟩ := hx i
    simp only [hlo, hhi, max_le_iff, le_min_iff]
    have hLU := h1.trans h2
    have e1 := mul_le_mul_of_nonneg_right hLU hz0
    have e2 := mul_le_mul_of_nonneg_right hLU (sub_nonneg.mpr hz1)
    refine ⟨⟨e1, ?_⟩, ?_, ?_⟩ <;> nlinarith
  set umax : Fin η → ℝ := fun i => if 0 ≤ w i then hi i else lo i with humax
  set umin : Fin η → ℝ := fun i => if 0 ≤ w i then lo i else hi i with humin
  have cmax : ∀ i, w i * umax i =
      min (w i * Ubrev w L U i * z) (w i * (x i - Lbrev w L U i * (1 - z))) := by
    intro i
    simp only [humax, hhi, hlo, Ubrev, Lbrev]
    split_ifs with hw
    · rw [mul_min_of_nonneg _ _ hw, mul_assoc]
    · rw [mul_max_nonpos _ _ _ (le_of_lt (not_le.mp hw)), mul_assoc]
  have cmin : ∀ i, w i * umin i =
      max (w i * Lbrev w L U i * z) (w i * (x i - Ubrev w L U i * (1 - z))) := by
    intro i
    simp only [humin, hhi, hlo, Ubrev, Lbrev]
    split_ifs with hw
    · rw [mul_max_of_nonneg _ _ hw, mul_assoc]
    · rw [mul_min_nonpos _ _ _ (le_of_lt (not_le.mp hw)), mul_assoc]
  -- upper bound from (6b)
  have hM : y - b * z ≤ ∑ i, w i * umax i := by
    set I := (supp w).filter (fun i => w i * (x i - Lbrev w L U i * (1 - z)) ≤
      w i * Ubrev w L U i * z) with hI
    have h := h6b I (Finset.filter_subset _ _)
    unfold rhs6b at h
    rw [add_mul, Finset.sum_mul] at h
    simp only [cmax]
    rw [← hsplit I]
    have hA : ∑ i ∈ I, min (w i * Ubrev w L U i * z) (w i * (x i - Lbrev w L U i * (1 - z))) =
        ∑ i ∈ I, w i * (x i - Lbrev w L U i * (1 - z)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hI, Finset.mem_filter] at hi
      exact min_eq_right hi.2
    have hB : ∑ i ∈ Finset.univ \ I,
          min (w i * Ubrev w L U i * z) (w i * (x i - Lbrev w L U i * (1 - z))) =
        ∑ i ∈ Finset.univ \ I, w i * Ubrev w L U i * z := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_sdiff, hI, Finset.mem_filter] at hi
      by_cases hs : i ∈ supp w
      · exact min_eq_left (le_of_lt (not_le.mp fun h' => hi.2 ⟨hs, h'⟩))
      · have : w i = 0 := by simpa [supp] using hs
        simp [this]
    rw [hA, hB]
    linarith
  -- lower bound from (7c)
  have hm : ∑ i, w i * umin i ≤ y - b * z := by
    set I := Finset.univ.filter (fun i => w i * Lbrev w L U i * z ≤
      w i * (x i - Ubrev w L U i * (1 - z))) with hI
    have h := rhs7c_le w b L U x y z h6a hx hy hz0 hz1 I
    unfold rhs7c at h
    rw [add_mul, Finset.sum_mul] at h
    simp only [cmin]
    rw [← hsplit I]
    have hA : ∑ i ∈ I, max (w i * Lbrev w L U i * z) (w i * (x i - Ubrev w L U i * (1 - z))) =
        ∑ i ∈ I, w i * (x i - Ubrev w L U i * (1 - z)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hI, Finset.mem_filter] at hi
      exact max_eq_right hi.2
    have hB : ∑ i ∈ Finset.univ \ I,
          max (w i * Lbrev w L U i * z) (w i * (x i - Ubrev w L U i * (1 - z))) =
        ∑ i ∈ Finset.univ \ I, w i * Lbrev w L U i * z := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_sdiff, hI, Finset.mem_filter] at hi
      exact max_eq_left (le_of_lt (not_le.mp fun h' => hi.2 ⟨Finset.mem_univ _, h'⟩))
    rw [hA, hB]
    linarith
  -- interpolate
  set m := ∑ i, w i * umin i
  set M := ∑ i, w i * umax i
  obtain ⟨t, ht0, ht1, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ m + t * (M - m) = y - b * z := by
    rcases eq_or_lt_of_le (hm.trans hM) with he | hlt
    · exact ⟨0, le_refl _, zero_le_one, by linarith⟩
    · refine ⟨(y - b * z - m) / (M - m), div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).mpr (by linarith), ?_⟩
      field_simp
      ring
  have hbox : ∀ i, lo i ≤ umin i ∧ umin i ≤ hi i ∧ lo i ≤ umax i ∧ umax i ≤ hi i := by
    intro i
    simp only [humin, humax]
    split_ifs <;> exact ⟨by linarith [hlohi i], by linarith [hlohi i], by linarith [hlohi i],
      by linarith [hlohi i]⟩
  refine ⟨fun i => umin i + t * (umax i - umin i), ?_, ?_, ?_⟩
  · intro i
    obtain ⟨a1, a2, a3, a4⟩ := hbox i
    have b1 := le_max_left (L i * z) (x i - U i * (1 - z))
    have b2 := min_le_left (U i * z) (x i - L i * (1 - z))
    have p1 := mul_nonneg ht0 (sub_nonneg.mpr a3)
    have p2 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr a1)
    have p3 := mul_nonneg ht0 (sub_nonneg.mpr a4)
    have p4 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr a2)
    simp only [hlo, hhi] at *
    constructor <;> nlinarith
  · intro i
    obtain ⟨a1, a2, a3, a4⟩ := hbox i
    have b1 := le_max_right (L i * z) (x i - U i * (1 - z))
    have b2 := min_le_right (U i * z) (x i - L i * (1 - z))
    have p1 := mul_nonneg ht0 (sub_nonneg.mpr a3)
    have p2 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr a1)
    have p3 := mul_nonneg ht0 (sub_nonneg.mpr a4)
    have p4 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr a2)
    simp only [hlo, hhi] at *
    constructor <;> nlinarith
  · have : ∑ i, w i * (umin i + t * (umax i - umin i)) = m + t * (M - m) := by
      simp only [m, M, mul_add, Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, ht]
    ring

lemma scaled_bounds {η : ℕ} (w L U : Fin η → ℝ) (v : Fin η → ℝ) (c : ℝ)
    (hv : ∀ i, L i * c ≤ v i ∧ v i ≤ U i * c) (i : Fin η) :
    w i * Lbrev w L U i * c ≤ w i * v i ∧ w i * v i ≤ w i * Ubrev w L U i * c := by
  obtain ⟨h1, h2⟩ := hv i
  unfold Lbrev Ubrev
  split_ifs with h
  · constructor
    · rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 h
    · rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 h
  · have h' : w i ≤ 0 := le_of_lt (not_le.mp h)
    constructor
    · rw [mul_assoc]; exact mul_le_mul_of_nonpos_left h2 h'
    · rw [mul_assoc]; exact mul_le_mul_of_nonpos_left h1 h'

lemma relax5_subset_relax6 {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) :
    relax5 w b L U ⊆ relax6 w b L U := by
  rintro ⟨x, y, z⟩ ⟨x0, x1, y0, y1, hx, hy, hy0, h5b, hy1, hy1p, h0, h1, hz0, hz1⟩
  simp only at *
  subst hx hy hy0
  have hsplit : ∀ (I : Finset (Fin η)) (f : Fin η → ℝ),
      ∑ i ∈ Finset.univ \ I, f i + ∑ i ∈ I, f i = ∑ i, f i :=
    fun I f => Finset.sum_sdiff (Finset.subset_univ I)
  refine ⟨?_, ?_, ?_, ?_, hz0, hz1⟩
  · simp only [affineFn, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    linarith
  · intro I _
    simp only [rhs6b]
    rw [add_mul, Finset.sum_mul]
    have e1 : ∑ i ∈ I, w i * x1 i ≤ ∑ i ∈ I, w i * ((x0 + x1) i - Lbrev w L U i * (1 - z)) :=
      Finset.sum_le_sum fun i _ => by
        have := (scaled_bounds w L U x0 (1 - z) h0 i).1
        simp only [Pi.add_apply]
        nlinarith
    have e2 : ∑ i ∈ Finset.univ \ I, w i * x1 i ≤
        ∑ i ∈ Finset.univ \ I, w i * Ubrev w L U i * z :=
      Finset.sum_le_sum fun i _ => (scaled_bounds w L U x1 z h1 i).2
    have := hsplit I (fun i => w i * x1 i)
    linarith
  · intro i
    obtain ⟨a1, a2⟩ := h0 i
    obtain ⟨b1, b2⟩ := h1 i
    simp only [Pi.add_apply]
    constructor <;> nlinarith
  · linarith

lemma relax6_subset_relax5 {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) :
    relax6 w b L U ⊆ relax5 w b L U := by
  rintro ⟨x, y, z⟩ hp
  obtain ⟨u, hu1, hu0, huy⟩ := exists_split w b L U x y z hp
  obtain ⟨h6a, _, _, hy, hz0, hz1⟩ := hp
  simp only at *
  refine ⟨x - u, u, 0, y, by simp, by simp, rfl, ?_, huy.symm, hy, hu0, hu1, hz0, hz1⟩
  unfold affineFn at h6a
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  linarith

theorem relax5_eq_relax6 {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) :
    relax5 w b L U = relax6 w b L U :=
  Set.Subset.antisymm (relax5_subset_relax6 w b L U) (relax6_subset_relax5 w b L U)

theorem system7_eq_relax6 {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) :
    system7 w b L U = relax6 w b L U := by
  apply Set.Subset.antisymm
  · exact fun p hp => hp.1
  · rintro ⟨x, y, z⟩ hp
    obtain ⟨h6a, _, hx, hy, hz0, hz1⟩ := id hp
    exact ⟨hp, fun I _ => rhs7c_le w b L U x y z h6a hx hy hz0 hz1 I⟩

end ReluMIP.Ideal

open ReluMIP.Ideal in
theorem solution {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
    (hLU : ∀ i, L i < U i) :
    relax5 w b L U = system7 w b L U := by
  rw [relax5_eq_relax6, system7_eq_relax6]
