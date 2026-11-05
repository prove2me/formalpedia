-- Prove2me | solution 1 for ReluMIP.Ideal.relax6_eq_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T03:14:25.054856+00:00
-- url     : https://prove2.me/submissions/53f72117-68fd-4291-88dc-732e7f0b2866

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

lemma mem_relax6_zero {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (x : Fin η → ℝ)
    (hx : x ∈ box L U) (hf : affineFn w b x ≤ 0) : (x, (0 : ℝ), (0 : ℝ)) ∈ relax6 w b L U := by
  refine ⟨hf, ?_, hx, le_refl _, le_refl _, zero_le_one⟩
  intro I _
  simp only [rhs6b, sub_zero, mul_one, mul_zero, add_zero]
  exact Finset.sum_nonneg fun i _ => by
    have := wLb_le w L U x hx i
    nlinarith

lemma mem_relax6_one {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (x : Fin η → ℝ)
    (hx : x ∈ box L U) (hf : 0 ≤ affineFn w b x) :
    (x, affineFn w b x, (1 : ℝ)) ∈ relax6 w b L U := by
  refine ⟨le_refl _, ?_, hx, hf, zero_le_one, le_refl _⟩
  intro I _
  simp only [rhs6b, sub_self, mul_zero, sub_zero, mul_one]
  have hs : ∑ i ∈ Finset.univ \ I, w i * x i + ∑ i ∈ I, w i * x i = ∑ i, w i * x i :=
    Finset.sum_sdiff (Finset.subset_univ I)
  have : ∑ i ∈ Finset.univ \ I, w i * x i ≤ ∑ i ∈ Finset.univ \ I, w i * Ubrev w L U i :=
    Finset.sum_le_sum fun i _ => le_wUb w L U x hx i
  unfold affineFn
  linarith

lemma relax6_zero {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (x : Fin η → ℝ) (y : ℝ)
    (h : (x, y, (0 : ℝ)) ∈ relax6 w b L U) : y = 0 := by
  obtain ⟨_, h6b, _, hy, _⟩ := h
  have := h6b ∅ (Finset.empty_subset _)
  simp [rhs6b] at this
  linarith

lemma relax6_one {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (x : Fin η → ℝ) (y : ℝ)
    (h : (x, y, (1 : ℝ)) ∈ relax6 w b L U) : y = affineFn w b x := by
  obtain ⟨h6a, h6b, _, _, _⟩ := h
  have := h6b (supp w) (subset_refl _)
  simp only [rhs6b, sub_self, mul_zero, sub_zero, mul_one] at this
  have h0 : ∑ i ∈ Finset.univ \ supp w, w i * Ubrev w L U i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have : w i = 0 := by simpa [supp] using hi
      simp [this]
  have h1 : ∑ i ∈ supp w, w i * x i = ∑ i, w i * x i :=
    Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
      have : w i = 0 := by simpa [supp] using hi
      simp [this]
  simp only at h6a
  unfold affineFn at *
  linarith

lemma convex_relax6 {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) :
    Convex ℝ (relax6 w b L U) := by
  rintro ⟨x, y, z⟩ ⟨h6a, h6b, hx, hy, hz0, hz1⟩ ⟨x', y', z'⟩ ⟨h6a', h6b', hx', hy', hz0', hz1'⟩
    a c ha hc hac
  obtain rfl : c = 1 - a := by linarith
  simp only at *
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  have hf : affineFn w b (a • x + (1 - a) • x') =
      a * affineFn w b x + (1 - a) * affineFn w b x' := by
    unfold affineFn
    have : ∑ i, w i * (a • x + (1 - a) • x') i =
        a * ∑ i, w i * x i + (1 - a) * ∑ i, w i * x' i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)
    rw [this]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf]; nlinarith
  · intro I hI
    have e : rhs6b w b L U I (a • x + (1 - a) • x') (a * z + (1 - a) * z') =
        a * rhs6b w b L U I x z + (1 - a) * rhs6b w b L U I x' z' := by
      unfold rhs6b
      have : ∑ i ∈ I, w i * ((a • x + (1 - a) • x') i -
            Lbrev w L U i * (1 - (a * z + (1 - a) * z'))) =
          a * ∑ i ∈ I, w i * (x i - Lbrev w L U i * (1 - z)) +
            (1 - a) * ∑ i ∈ I, w i * (x' i - Lbrev w L U i * (1 - z')) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)
      rw [this]; ring
    rw [e]
    have := h6b I hI
    have := h6b' I hI
    nlinarith
  · intro i
    obtain ⟨p1, p2⟩ := hx i
    obtain ⟨q1, q2⟩ := hx' i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor <;> nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

theorem relax6_eq_convexHull_aux {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) :
    relax6 w b L U = convexHull ℝ {p | p ∈ relax6 w b L U ∧ (p.2.2 = 0 ∨ p.2.2 = 1)} := by
  apply Set.Subset.antisymm
  · rintro ⟨x, y, z⟩ hp
    set S := {p : (Fin η → ℝ) × ℝ × ℝ | p ∈ relax6 w b L U ∧ (p.2.2 = 0 ∨ p.2.2 = 1)}
    have hz0 : 0 ≤ z := hp.2.2.2.2.1
    have hz1 : z ≤ 1 := hp.2.2.2.2.2
    rcases eq_or_lt_of_le hz0 with h0 | h0
    · exact subset_convexHull ℝ S ⟨hp, Or.inl h0.symm⟩
    rcases eq_or_lt_of_le hz1 with h1 | h1
    · exact subset_convexHull ℝ S ⟨hp, Or.inr h1⟩
    obtain ⟨u, hu1, hu0, huy⟩ := exists_split w b L U x y z hp
    have hx := hp.2.2.1
    have h6a := hp.1
    simp only at hx h6a
    have h1z : 0 < 1 - z := by linarith
    set x0 : Fin η → ℝ := fun i => (x i - u i) / (1 - z) with hx0
    set x1 : Fin η → ℝ := fun i => u i / z with hx1
    have hx0b : x0 ∈ box L U := fun i => by
      simp only [hx0]
      rw [le_div_iff₀ h1z, div_le_iff₀ h1z]
      exact hu0 i
    have hx1b : x1 ∈ box L U := fun i => by
      simp only [hx1]
      rw [le_div_iff₀ h0, div_le_iff₀ h0]
      exact hu1 i
    have hf1 : affineFn w b x1 * z = y := by
      unfold affineFn
      rw [← huy, add_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by simp only [hx1]; field_simp
    have hf0 : affineFn w b x0 * (1 - z) = affineFn w b x - y := by
      unfold affineFn at *
      rw [← huy, add_mul, Finset.sum_mul]
      have : ∑ i, w i * x0 i * (1 - z) = ∑ i, w i * x i - ∑ i, w i * u i := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by simp only [hx0]; field_simp
      rw [this]; ring
    have hy : 0 ≤ y := hp.2.2.2.1
    have hm0 : (x0, (0 : ℝ), (0 : ℝ)) ∈ S := by
      refine ⟨mem_relax6_zero w b L U x0 hx0b ?_, Or.inl rfl⟩
      by_contra hc
      push Not at hc
      have := mul_pos hc h1z
      linarith
    have hm1 : (x1, affineFn w b x1, (1 : ℝ)) ∈ S := by
      refine ⟨mem_relax6_one w b L U x1 hx1b ?_, Or.inr rfl⟩
      by_contra hc
      push Not at hc
      have := mul_neg_of_neg_of_pos hc h0
      linarith
    have key := convex_convexHull ℝ S (subset_convexHull ℝ S hm0) (subset_convexHull ℝ S hm1)
      h1z.le h0.le (by ring)
    convert key using 1
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_zero, zero_add, mul_one]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx0, hx1]
      field_simp
      ring
    · rw [← hf1]; ring
    · ring
  · exact (convexHull_min (fun p hp => hp.1) (convex_relax6 w b L U))

end ReluMIP.Ideal

open ReluMIP.Ideal in
theorem solution {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
    (hLU : ∀ i, L i < U i) :
    relax6 w b L U = convexHull ℝ {p | p ∈ relax6 w b L U ∧ (p.2.2 = 0 ∨ p.2.2 = 1)} :=
  relax6_eq_convexHull_aux w b L U
