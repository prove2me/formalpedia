-- Prove2me | solution 1 for PolygonalArcEndpointDiskCappedTaperChartTransport
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T16:30:52.891304+00:00
-- url     : https://prove2.me/submissions/70de328b-f31e-4633-b607-539b7746d180

import Mathlib
import Definitions.Def_PlanarRot90

set_option autoImplicit false

open Set
open Classical

namespace P1fd11df1

abbrev E2 := EuclideanSpace ℝ (Fin 2)

lemma nsq (v : E2) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

lemma comp0 (x y : ℝ) (d : E2) : (x • d + y • PlanarRot90 d) 0 = x * d 0 - y * d 1 := by
  simp [PlanarRot90]
  ring

lemma comp1 (x y : ℝ) (d : E2) : (x • d + y • PlanarRot90 d) 1 = x * d 1 + y * d 0 := by
  simp [PlanarRot90]

lemma nsq_comb (x y : ℝ) (d : E2) :
    ‖x • d + y • PlanarRot90 d‖ ^ 2 = (x ^ 2 + y ^ 2) * ‖d‖ ^ 2 := by
  rw [nsq, nsq, comp0, comp1]
  ring

lemma comb_eq_zero (x y : ℝ) (d : E2) (hd : d ≠ 0) (h : x • d + y • PlanarRot90 d = 0) :
    x = 0 ∧ y = 0 := by
  have h1 := nsq_comb x y d
  rw [h, norm_zero] at h1
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hd2 : 0 < ‖d‖ ^ 2 := by positivity
  have hxy : x ^ 2 + y ^ 2 = 0 := by
    have : (x ^ 2 + y ^ 2) * ‖d‖ ^ 2 = 0 := by rw [← h1]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hd2.ne'
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

lemma conv_lt (s u v : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hu : 0 < u) (hv : 0 < v) :
    0 < s * u + (1 - s) * v := by
  rcases hs.eq_or_lt with h | h
  · subst h; simpa using hv
  · nlinarith [mul_pos h hu, mul_nonneg (sub_nonneg.2 hs1) hv.le]


lemma convL (a K : ℝ) :
    Convex ℝ {z : E2 | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧ z 1 < K * z 0} := by
  intro x hx y hy s t hs ht hst
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  have e0 : (s • x + t • y) 0 = s * x 0 + t * y 0 := by simp
  have e1 : (s • x + t • y) 1 = s * x 1 + t * y 1 := by simp
  have ht' : t = 1 - s := by linarith
  subst ht'
  have hs1 : s ≤ 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [e0, e1]
  · nlinarith [conv_lt s _ _ hs hs1 hx1 hy1]
  · have h := conv_lt s (a ^ 2 - (x 0 ^ 2 + x 1 ^ 2)) (a ^ 2 - (y 0 ^ 2 + y 1 ^ 2)) hs hs1
      (by linarith) (by linarith)
    have h2 : 0 ≤ s * (1 - s) * ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) :=
      mul_nonneg (mul_nonneg hs ht) (by positivity)
    nlinarith [h, h2]
  · nlinarith [conv_lt s _ _ hs hs1 hx3 hy3]
  · nlinarith [conv_lt s (K * x 0 - x 1) (K * y 0 - y 1) hs hs1 (by linarith) (by linarith)]

lemma convR (a K : ℝ) :
    Convex ℝ {z : E2 | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧ z 1 < 0} := by
  intro x hx y hy s t hs ht hst
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  have e0 : (s • x + t • y) 0 = s * x 0 + t * y 0 := by simp
  have e1 : (s • x + t • y) 1 = s * x 1 + t * y 1 := by simp
  have ht' : t = 1 - s := by linarith
  subst ht'
  have hs1 : s ≤ 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [e0, e1]
  · nlinarith [conv_lt s _ _ hs hs1 hx1 hy1]
  · have h := conv_lt s (a ^ 2 - (x 0 ^ 2 + x 1 ^ 2)) (a ^ 2 - (y 0 ^ 2 + y 1 ^ 2)) hs hs1
      (by linarith) (by linarith)
    have h2 : 0 ≤ s * (1 - s) * ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) :=
      mul_nonneg (mul_nonneg hs ht) (by positivity)
    nlinarith [h, h2]
  · nlinarith [conv_lt s (x 1 + K * x 0) (y 1 + K * y 0) hs hs1 (by linarith) (by linarith)]
  · nlinarith [conv_lt s (-x 1) (-y 1) hs hs1 (by linarith) (by linarith)]

lemma neL (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    ({z : E2 | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧ z 1 < K * z 0}).Nonempty := by
  obtain ⟨x0, hx0, hx0K⟩ : ∃ x0 : ℝ, 0 < x0 ∧ x0 * (1 + K) = a / 2 :=
    ⟨a / (2 * (1 + K)), by positivity, by field_simp⟩
  refine ⟨WithLp.toLp 2 ![x0, K * x0 / 2], ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact hx0
  · nlinarith [mul_pos hK hx0, mul_pos (mul_pos hK hK) (mul_pos hx0 hx0)]
  · positivity
  · nlinarith [mul_pos hK hx0]

lemma neR (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    ({z : E2 | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧ z 1 < 0}).Nonempty := by
  obtain ⟨x0, hx0, hx0K⟩ : ∃ x0 : ℝ, 0 < x0 ∧ x0 * (1 + K) = a / 2 :=
    ⟨a / (2 * (1 + K)), by positivity, by field_simp⟩
  refine ⟨WithLp.toLp 2 ![x0, -(K * x0 / 2)], ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact hx0
  · nlinarith [mul_pos hK hx0, mul_pos (mul_pos hK hK) (mul_pos hx0 hx0)]
  · nlinarith [mul_pos hK hx0]
  · nlinarith [mul_pos hK hx0]

lemma openC (a K : ℝ) :
    IsOpen {z : E2 | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧ z 1 < K * z 0} := by
  apply IsOpen.and (isOpen_lt continuous_const (by fun_prop))
  apply IsOpen.and (isOpen_lt (by fun_prop) continuous_const)
  exact IsOpen.and (isOpen_lt (by fun_prop) (by fun_prop)) (isOpen_lt (by fun_prop) (by fun_prop))

lemma openL (a K : ℝ) :
    IsOpen {z : E2 | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧ z 1 < K * z 0} := by
  apply IsOpen.and (isOpen_lt continuous_const (by fun_prop))
  apply IsOpen.and (isOpen_lt (by fun_prop) continuous_const)
  exact IsOpen.and (isOpen_lt continuous_const (by fun_prop)) (isOpen_lt (by fun_prop) (by fun_prop))

lemma openR (a K : ℝ) :
    IsOpen {z : E2 | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧ z 1 < 0} := by
  apply IsOpen.and (isOpen_lt continuous_const (by fun_prop))
  apply IsOpen.and (isOpen_lt (by fun_prop) continuous_const)
  exact IsOpen.and (isOpen_lt (by fun_prop) (by fun_prop)) (isOpen_lt (by fun_prop) continuous_const)

lemma disjLR (a K : ℝ) :
    Disjoint {z : E2 | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧ z 1 < K * z 0}
      {z : E2 | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧ z 1 < 0} := by
  rw [Set.disjoint_left]
  intro z hL hR
  exact lt_irrefl _ (lt_trans hR.2.2.2 hL.2.2.1)

lemma GsubC (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    {z : E2 | 0 < z 0 ∧ z 0 < a ∧ z 1 = 0} ⊆
      {z : E2 | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧ z 1 < K * z 0} := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [h3]; nlinarith
  · rw [h3]; nlinarith [mul_pos hK h1]
  · rw [h3]; nlinarith [mul_pos hK h1]

lemma CdiffG (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    {z : E2 | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧ z 1 < K * z 0} \
      {z : E2 | 0 < z 0 ∧ z 0 < a ∧ z 1 = 0} =
      {z : E2 | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧ z 1 < K * z 0} ∪
      {z : E2 | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧ z 1 < 0} := by
  ext z
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, hG⟩
    have hz1 : z 1 ≠ 0 := by
      intro h0
      apply hG
      refine ⟨h1, ?_, h0⟩
      nlinarith [sq_nonneg (z 1)]
    rcases lt_or_gt_of_ne hz1 with h | h
    · exact Or.inr ⟨h1, h2, h3, h⟩
    · exact Or.inl ⟨h1, h2, h, h4⟩
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
    · refine ⟨⟨h1, h2, by nlinarith [mul_pos hK h1], h4⟩, ?_⟩
      rintro ⟨_, _, h0⟩; rw [h0] at h3; exact lt_irrefl 0 h3
    · refine ⟨⟨h1, h2, h3, by nlinarith [mul_pos hK h1]⟩, ?_⟩
      rintro ⟨_, _, h0⟩; rw [h0] at h4; exact lt_irrefl 0 h4

lemma ball_bound (d : E2) (a r x y : ℝ) (hr : 0 < r) (hdn : 0 < ‖d‖) (had : a * ‖d‖ = r)
    (h : x ^ 2 + y ^ 2 < a ^ 2) : ‖x • d + y • PlanarRot90 d‖ < r := by
  have h1 := nsq_comb x y d
  have h2 : ‖x • d + y • PlanarRot90 d‖ ^ 2 < r ^ 2 := by
    rw [h1, ← had, mul_pow]
    exact mul_lt_mul_of_pos_right h (pow_pos hdn 2)
  by_contra hc
  have hc' := not_lt.mp hc
  nlinarith [norm_nonneg (x • d + y • PlanarRot90 d)]

end P1fd11df1

set_option maxHeartbeats 1000000 in
theorem solution
    (p0 p1 : EuclideanSpace ℝ (Fin 2)) (r K : ℝ)
    (hp : p1 ≠ p0) (hr : 0 < r) (hK : 0 < K) :
    let d : EuclideanSpace ℝ (Fin 2) := p1 - p0
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p0 + z 0 • d + z 1 • PlanarRot90 d
    let a : ℝ := r / dist p0 p1
    let C : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧
        z 1 < K * z 0}
    let L : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧
        z 1 < K * z 0}
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧
        z 1 < 0}
    let G : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 < a ∧ z 1 = 0}
    0 < a ∧
      IsOpen C ∧ IsOpen L ∧ IsOpen R ∧
      IsConnected L ∧ IsConnected R ∧
      IsConnected (chart '' L) ∧ IsConnected (chart '' R) ∧
      Disjoint L R ∧ Disjoint (chart '' L) (chart '' R) ∧
      (0 : EuclideanSpace ℝ (Fin 2)) ∉ C ∧ G ⊆ C ∧ C \ G = L ∪ R ∧
      (∀ z : EuclideanSpace ℝ (Fin 2),
        z 0 ^ 2 + z 1 ^ 2 < a ^ 2 → chart z ∈ Metric.ball p0 r) ∧
      chart '' C ⊆ Metric.ball p0 r ∧
      p0 ∉ chart '' C ∧
      (∀ {t : ℝ}, 0 < t →
        chart (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)) ≠ p0) ∧
      ((AffineMap.lineMap p0 p1) '' Set.Ioo (0 : ℝ) a ⊆ chart '' G) ∧
      chart '' C \ chart '' G = chart '' L ∪ chart '' R := by
  intro d chart a C L R G
  have hd : d ≠ 0 := sub_ne_zero.mpr hp
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hdist : dist p0 p1 = ‖d‖ := by
    rw [dist_eq_norm, ← norm_neg]; simp [d]
  have ha : 0 < a := by
    show 0 < r / dist p0 p1
    rw [hdist]; positivity
  have had : a * ‖d‖ = r := by
    show r / dist p0 p1 * ‖d‖ = r
    rw [hdist]; field_simp
  have hchart_sub : ∀ z : P1fd11df1.E2, chart z - p0 = z 0 • d + z 1 • PlanarRot90 d := by
    intro z; simp only [chart]; abel
  have hchart_diff : ∀ z w : P1fd11df1.E2, chart z - chart w =
      (z 0 - w 0) • d + (z 1 - w 1) • PlanarRot90 d := by
    intro z w; simp only [chart, sub_smul]; abel
  have hinj : Function.Injective chart := by
    intro z w h
    have h0 := hchart_diff z w
    rw [h, sub_self] at h0
    obtain ⟨h1, h2⟩ := P1fd11df1.comb_eq_zero _ _ d hd h0.symm
    ext i
    fin_cases i
    · simp only [Fin.zero_eta]; linarith
    · simp only [Fin.mk_one]; linarith
  have hcont : Continuous chart := by
    simp only [chart]; fun_prop
  have hball : ∀ z : P1fd11df1.E2, z 0 ^ 2 + z 1 ^ 2 < a ^ 2 → chart z ∈ Metric.ball p0 r := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm, hchart_sub]
    exact P1fd11df1.ball_bound d a r _ _ hr hdn had hz
  have hzero : ∀ z : P1fd11df1.E2, chart z = p0 → z 0 = 0 ∧ z 1 = 0 := by
    intro z hz
    have h := hchart_sub z
    rw [hz, sub_self] at h
    exact P1fd11df1.comb_eq_zero _ _ d hd h.symm
  have hLconn : IsConnected L := ⟨P1fd11df1.neL a K ha hK, (P1fd11df1.convL a K).isPreconnected⟩
  have hRconn : IsConnected R := ⟨P1fd11df1.neR a K ha hK, (P1fd11df1.convR a K).isPreconnected⟩
  have hLR : Disjoint L R := P1fd11df1.disjLR a K
  have hCG : C \ G = L ∪ R := P1fd11df1.CdiffG a K ha hK
  refine ⟨ha, P1fd11df1.openC a K, P1fd11df1.openL a K, P1fd11df1.openR a K, hLconn, hRconn,
    hLconn.image _ hcont.continuousOn, hRconn.image _ hcont.continuousOn,
    hLR, (Set.disjoint_image_iff hinj).2 hLR, ?_, P1fd11df1.GsubC a K ha hK, hCG, hball, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h1, -⟩
    simp at h1
  · rintro _ ⟨z, hz, rfl⟩
    exact hball z hz.2.1
  · rintro ⟨z, hz, hcz⟩
    have h0 := (hzero z hcz).1
    have h1 : (0 : ℝ) < z 0 := hz.1
    rw [h0] at h1
    exact lt_irrefl _ h1
  · intro t ht hct
    have h0 := (hzero _ hct).1
    simp at h0
    linarith
  · rintro _ ⟨t, ⟨ht0, hta⟩, rfl⟩
    refine ⟨WithLp.toLp 2 ![t, 0], ⟨?_, ?_, ?_⟩, ?_⟩
    · simpa using ht0
    · simpa using hta
    · simp
    · simp only [chart, d, Matrix.cons_val_zero, Matrix.cons_val_one,
        zero_smul, add_zero, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      abel
  · rw [← Set.image_sdiff hinj, hCG, Set.image_union]
