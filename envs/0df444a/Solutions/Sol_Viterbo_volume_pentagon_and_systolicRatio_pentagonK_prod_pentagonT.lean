-- Prove2me | solution 1 for Viterbo.volume_pentagon_and_systolicRatio_pentagonK_prod_pentagonT
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:51:26.81772+00:00
-- url     : https://prove2.me/submissions/0b526c46-d7b0-46e5-86df-73af5664e664
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
import Theorems.Thm_Viterbo_cEHZ_pentagonK_prod_pentagonT
import Mathlib

section
section
open MeasureTheory Set

namespace Viterbo.VolTri

abbrev P2 := EuclideanSpace ℝ (Fin 2)

/-- the closed standard triangle -/
def tri0 : Set P2 := {p | 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 0 + p 1 ≤ 1}

def toProd : P2 → ℝ × ℝ := fun p => (p 0, p 1)

theorem toProd_mp : MeasurePreserving toProd (volume : Measure P2) (volume : Measure (ℝ × ℝ)) :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

theorem vol_tri0 : volume tri0 = ENNReal.ofReal (1 / 2) := by
  set S : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ 1} with hS
  have h : tri0 = toProd ⁻¹' S := rfl
  have hm : MeasurableSet S := by
    have : S = {q : ℝ × ℝ | 0 ≤ q.1} ∩ ({q : ℝ × ℝ | 0 ≤ q.2} ∩ {q : ℝ × ℝ | q.1 + q.2 ≤ 1}) := rfl
    rw [this]
    refine (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le (measurable_fst.add measurable_snd) measurable_const))
  rw [h, toProd_mp.measure_preimage hm.nullMeasurableSet]
  rw [Measure.volume_eq_prod, Measure.prod_apply hm]
  have hslice : ∀ x : ℝ, volume (Prod.mk x ⁻¹' S) =
      (Icc (0:ℝ) 1).indicator (fun x => ENNReal.ofReal (1 - x)) x := by
    intro x
    by_cases hx : x ∈ Icc (0:ℝ) 1
    · have : Prod.mk x ⁻¹' S = Icc 0 (1 - x) := by
        ext y; simp only [hS, mem_preimage, mem_setOf_eq, mem_Icc]
        constructor
        · rintro ⟨_, a, b⟩; exact ⟨a, by linarith⟩
        · rintro ⟨a, b⟩; exact ⟨hx.1, a, by linarith⟩
      rw [this, indicator_of_mem hx, Real.volume_Icc]; simp
    · have : Prod.mk x ⁻¹' S = ∅ := by
        ext y; simp only [hS, mem_preimage, mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨a, b, c⟩; exact hx ⟨a, by linarith⟩
      rw [this, indicator_of_notMem hx]; simp
  simp_rw [hslice]
  rw [lintegral_indicator measurableSet_Icc]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    rw [intervalIntegral.integral_sub (by simp) (by simp)]
    simp
    norm_num
  · exact (continuous_const.sub continuous_id).integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simp [hx.2]


theorem convex_tri0 : Convex ℝ tri0 := by
  intro x hx y hy a b ha hb hab
  obtain ⟨x0, x1, x2⟩ := hx
  obtain ⟨y0, y1, y2⟩ := hy
  simp only [tri0, mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨by positivity, by positivity, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left x2 ha, mul_le_mul_of_nonneg_left y2 hb]

/-- the linear map with columns a, b -/
noncomputable def colMap (a b : P2) : P2 →ₗ[ℝ] P2 :=
  Matrix.toEuclideanLin !![a 0, b 0; a 1, b 1]

theorem colMap_apply (a b p : P2) : colMap a b p = p 0 • a + p 1 • b := by
  ext i; fin_cases i <;> simp [colMap, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem det_colMap (a b : P2) : LinearMap.det (colMap a b) = a 0 * b 1 - a 1 * b 0 := by
  unfold colMap
  rw [Matrix.toEuclideanLin_eq_toLin, LinearMap.det_toLin]
  simp [Matrix.det_fin_two]; ring

theorem hull_eq (a b : P2) : convexHull ℝ {0, a, b} = colMap a b '' tri0 := by
  apply Subset.antisymm
  · apply convexHull_min
    · intro x hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, ⟨le_refl _, le_refl _, by simp⟩, by simp⟩
      · refine ⟨!₂[1, 0], ⟨by simp, by simp, by simp⟩, ?_⟩
        rw [colMap_apply]; simp
      · refine ⟨!₂[0, 1], ⟨by simp, by simp, by simp⟩, ?_⟩
        rw [colMap_apply]; simp
    · exact convex_tri0.linear_image _
  · rintro _ ⟨p, ⟨h0, h1, h2⟩, rfl⟩
    rw [colMap_apply]
    have := (convex_convexHull ℝ ({0, a, b} : Set P2)).sum_mem (t := Finset.univ)
      (w := ![1 - p 0 - p 1, p 0, p 1]) (z := ![0, a, b])
      (by intro i _; fin_cases i <;> simp <;> linarith)
      (by simp [Fin.sum_univ_three]; ring)
      (by intro i _; fin_cases i <;> exact subset_convexHull ℝ _ (by simp))
    simpa [Fin.sum_univ_three] using this

theorem vol_hull (a b : P2) :
    volume (convexHull ℝ {0, a, b}) = ENNReal.ofReal (|a 0 * b 1 - a 1 * b 0| / 2) := by
  rw [hull_eq, Measure.addHaar_image_linearMap, det_colMap, vol_tri0, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1; ring

end Viterbo.VolTri

end
end

section
section
open MeasureTheory Set

namespace Viterbo.VolFan
open Viterbo.VolTri

def det2 (a b : P2) : ℝ := a 0 * b 1 - a 1 * b 0

theorem mem_hull_of (u w x : P2) (hD : 0 < det2 u w) (h1 : 0 ≤ det2 u x) (h2 : 0 ≤ det2 x w)
    (h3 : 0 ≤ det2 (w - u) (x - u)) : x ∈ convexHull ℝ {0, u, w} := by
  rw [hull_eq]
  refine ⟨!₂[det2 x w / det2 u w, det2 u x / det2 u w], ⟨?_, ?_, ?_⟩, ?_⟩
  · simpa using div_nonneg h2 hD.le
  · simpa using div_nonneg h1 hD.le
  · simp only [det2] at *
    simp only [PiLp.sub_apply] at h3
    have : (x 0 * w 1 - x 1 * w 0) / (u 0 * w 1 - u 1 * w 0) + (u 0 * x 1 - u 1 * x 0) / (u 0 * w 1 - u 1 * w 0) ≤ 1 := by
      rw [← add_div, div_le_one hD]; nlinarith
    simpa using this
  · rw [colMap_apply]
    have hD' : det2 u w ≠ 0 := hD.ne'
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, WithLp.ofLp_toLp]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD']
    fin_cases i <;> simp [det2] <;> ring

theorem line_null (v : P2) (hv : v ≠ 0) : volume {x : P2 | det2 v x = 0} = 0 := by
  let ℓ : P2 →ₗ[ℝ] ℝ :=
    { toFun := fun x => det2 v x
      map_add' := by intro x y; simp [det2]; ring
      map_smul' := by intro c x; simp [det2]; ring }
  have hℓ : ℓ ≠ 0 := by
    intro h
    apply hv
    have h0 := LinearMap.congr_fun h !₂[1, 0]
    have h1 := LinearMap.congr_fun h !₂[0, 1]
    simp [ℓ, det2] at h0 h1
    ext i; fin_cases i <;> simp [h0, h1]
  have : {x : P2 | det2 v x = 0} = (LinearMap.ker ℓ : Set P2) := by
    ext x; simp [ℓ]
  rw [this]
  apply Measure.addHaar_submodule
  intro htop
  apply hℓ
  ext x
  have : x ∈ LinearMap.ker ℓ := by rw [htop]; trivial
  simpa using this

end Viterbo.VolFan

end
end

section
section
open MeasureTheory Set

namespace Viterbo.VolPent
open Viterbo.VolTri Viterbo.VolFan Viterbo

noncomputable def V : ℕ → P2 := pentagonVertex
noncomputable def c1 : ℝ := Real.cos (2 * Real.pi / 5)
noncomputable def s1 : ℝ := Real.sin (2 * Real.pi / 5)
noncomputable def c2 : ℝ := Real.cos (4 * Real.pi / 5)
noncomputable def s2 : ℝ := Real.sin (4 * Real.pi / 5)

theorem V_zero (k : ℕ) : V k 0 = Real.cos (2 * Real.pi * k / 5) := by simp [V, pentagonVertex]
theorem V_one (k : ℕ) : V k 1 = Real.sin (2 * Real.pi * k / 5) := by simp [V, pentagonVertex]

theorem V_add_five (k : ℕ) : V (k + 5) = V k := by
  ext i; fin_cases i
  · simp only [Fin.zero_eta, V_zero]
    have : 2 * Real.pi * ((k + 5 : ℕ) : ℝ) / 5 = 2 * Real.pi * k / 5 + 2 * Real.pi := by push_cast; ring
    rw [this, Real.cos_add_two_pi]
  · simp only [Fin.mk_one, V_one]
    have : 2 * Real.pi * ((k + 5 : ℕ) : ℝ) / 5 = 2 * Real.pi * k / 5 + 2 * Real.pi := by push_cast; ring
    rw [this, Real.sin_add_two_pi]

theorem V_rec0 (k : ℕ) : V (k + 2) 0 + V k 0 = 2 * c1 * V (k + 1) 0 := by
  simp only [V_zero, c1]
  have h1 : 2 * Real.pi * ((k + 2 : ℕ) : ℝ) / 5 = 2 * Real.pi * ((k + 1 : ℕ) : ℝ) / 5 + 2 * Real.pi / 5 := by push_cast; ring
  have h2 : 2 * Real.pi * (k : ℝ) / 5 = 2 * Real.pi * ((k + 1 : ℕ) : ℝ) / 5 - 2 * Real.pi / 5 := by push_cast; ring
  rw [h1, h2, Real.cos_add, Real.cos_sub]; ring

theorem V_rec1 (k : ℕ) : V (k + 2) 1 + V k 1 = 2 * c1 * V (k + 1) 1 := by
  simp only [V_one, c1]
  have h1 : 2 * Real.pi * ((k + 2 : ℕ) : ℝ) / 5 = 2 * Real.pi * ((k + 1 : ℕ) : ℝ) / 5 + 2 * Real.pi / 5 := by push_cast; ring
  have h2 : 2 * Real.pi * (k : ℝ) / 5 = 2 * Real.pi * ((k + 1 : ℕ) : ℝ) / 5 - 2 * Real.pi / 5 := by push_cast; ring
  rw [h1, h2, Real.sin_add, Real.sin_sub]; ring

theorem det_VV (k : ℕ) : det2 (V k) (V (k + 1)) = s1 := by
  simp only [det2, V_zero, V_one, s1]
  have : 2 * Real.pi * ((k + 1 : ℕ) : ℝ) / 5 = 2 * Real.pi * k / 5 + 2 * Real.pi / 5 := by push_cast; ring
  rw [this, Real.sin_add, Real.cos_add]
  linear_combination (Real.sin (2 * Real.pi / 5)) * Real.cos_sq_add_sin_sq (2 * Real.pi * k / 5)

theorem V_ne_zero (k : ℕ) : V k ≠ 0 := by
  intro h
  have h0 := V_zero k
  have h1 := V_one k
  rw [h] at h0 h1
  have := Real.cos_sq_add_sin_sq (2 * Real.pi * k / 5)
  simp [← h0, ← h1] at this

theorem c1_val : c1 = (Real.sqrt 5 - 1) / 4 := by
  have h := Real.cos_pi_div_five
  have : 2 * Real.pi / 5 = 2 * (Real.pi / 5) := by ring
  rw [c1, this, Real.cos_two_mul, h]
  have h5 := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  nlinarith

theorem c2_val : c2 = -((1 + Real.sqrt 5) / 4) := by
  rw [c2, ← Real.cos_pi_div_five]
  have : 4 * Real.pi / 5 = Real.pi - Real.pi / 5 := by ring
  rw [this, Real.cos_pi_sub]

theorem s1_pos : 0 < s1 := by
  apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [Real.pi_pos]

theorem s2_pos : 0 < s2 := by
  apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [Real.pi_pos]

theorem s1_sq : s1 ^ 2 = 1 - c1 ^ 2 := by
  have := Real.sin_sq_add_cos_sq (2 * Real.pi / 5)
  simp only [s1, c1]; linarith

theorem s2_sq : s2 ^ 2 = 1 - c2 ^ 2 := by
  have := Real.sin_sq_add_cos_sq (4 * Real.pi / 5)
  simp only [s2, c2]; linarith

theorem sqrt5_bounds : 2.23606 < Real.sqrt 5 ∧ Real.sqrt 5 < 2.23607 := by
  constructor
  · apply Real.lt_sqrt_of_sq_lt; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem c1_b : 0.309015 < c1 ∧ c1 < 0.3090175 := by
  have := sqrt5_bounds; rw [c1_val]; constructor <;> linarith

theorem c2_b : -0.8090175 < c2 ∧ c2 < -0.809015 := by
  have := sqrt5_bounds; rw [c2_val]; constructor <;> linarith

theorem s1_b : 0.951 < s1 ∧ s1 < 0.9511 := by
  have h := s1_sq; have := s1_pos; have := c1_b
  constructor <;> nlinarith

theorem s2_b : 0.5877 < s2 ∧ s2 < 0.5879 := by
  have h := s2_sq; have := s2_pos; have := c2_b
  constructor <;> nlinarith

/-- explicit vertices -/
theorem V0 : V 0 = !₂[1, 0] := by
  ext i; fin_cases i <;> simp [V_zero, V_one]
theorem V1 : V 1 = !₂[c1, s1] := by
  ext i; fin_cases i <;> simp [V_zero, V_one, c1, s1]
theorem V2 : V 2 = !₂[c2, s2] := by
  ext i; fin_cases i <;> simp [V_zero, V_one, c2, s2] <;> (congr 1; ring)
theorem V3 : V 3 = !₂[c2, -s2] := by
  ext i; fin_cases i
  · simp only [Fin.zero_eta, V_zero, c2]
    have : 2 * Real.pi * ((3:ℕ):ℝ) / 5 = 2 * Real.pi - 4 * Real.pi / 5 := by push_cast; ring
    rw [this, Real.cos_two_pi_sub]; simp
  · simp only [Fin.mk_one, V_one, s2]
    have : 2 * Real.pi * ((3:ℕ):ℝ) / 5 = 2 * Real.pi - 4 * Real.pi / 5 := by push_cast; ring
    rw [this, Real.sin_two_pi_sub]; simp
theorem V4 : V 4 = !₂[c1, -s1] := by
  ext i; fin_cases i
  · simp only [Fin.zero_eta, V_zero, c1]
    have : 2 * Real.pi * ((4:ℕ):ℝ) / 5 = 2 * Real.pi - 2 * Real.pi / 5 := by push_cast; ring
    rw [this, Real.cos_two_pi_sub]; simp
  · simp only [Fin.mk_one, V_one, s1]
    have : 2 * Real.pi * ((4:ℕ):ℝ) / 5 = 2 * Real.pi - 2 * Real.pi / 5 := by push_cast; ring
    rw [this, Real.sin_two_pi_sub]; simp
theorem V5 : V 5 = V 0 := by simpa using V_add_five 0


theorem V_mem (k : ℕ) (hk : k < 5) : V k ∈ pentagonK :=
  subset_convexHull ℝ _ ⟨k, by simpa using hk, rfl⟩

theorem V_mem' (k : ℕ) (hk : k ≤ 5) : V k ∈ pentagonK := by
  rcases Nat.lt_or_ge k 5 with h | h
  · exact V_mem k h
  · have : k = 5 := by omega
    subst this; rw [V5]; exact V_mem 0 (by norm_num)

theorem zero_mem : (0 : P2) ∈ pentagonK := by
  have hc : 1 + 2 * c1 + 2 * c2 = 0 := by rw [c1_val, c2_val]; ring
  have := (convex_convexHull ℝ (V '' (Finset.range 5 : Set ℕ))).sum_mem (t := Finset.range 5)
    (w := fun _ => (1 / 5 : ℝ)) (z := V) (by intros; norm_num)
    (by simp) (by intro i hi; exact V_mem i (by simpa using hi))
  have h0 : (∑ i ∈ Finset.range 5, (1 / 5 : ℝ) • V i) = (0 : P2) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, V0, V1, V2, V3, V4]
    ext i
    fin_cases i
    · simp; linarith
    · simp
  rw [h0] at this
  exact this

theorem S_sub (k : ℕ) (hk : k < 5) : convexHull ℝ {0, V k, V (k + 1)} ⊆ pentagonK := by
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact zero_mem
  · exact V_mem k hk
  · exact V_mem' (k + 1) hk

theorem S_cone (k : ℕ) (x : P2) (hx : x ∈ convexHull ℝ {0, V k, V (k + 1)}) :
    0 ≤ det2 (V k) x ∧ det2 (V (k + 1)) x ≤ 0 := by
  rw [hull_eq] at hx
  obtain ⟨p, ⟨h0, h1, h2⟩, rfl⟩ := hx
  rw [colMap_apply]
  have hd := det_VV k
  unfold det2 at hd ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hs := s1_pos
  constructor
  · have : V k 0 * (p 0 * V k 1 + p 1 * V (k + 1) 1) - V k 1 * (p 0 * V k 0 + p 1 * V (k + 1) 0) =
        p 1 * s1 := by rw [← hd]; ring
    rw [this]; positivity
  · have : V (k + 1) 0 * (p 0 * V k 1 + p 1 * V (k + 1) 1) - V (k + 1) 1 * (p 0 * V k 0 + p 1 * V (k + 1) 0) =
        -(p 0 * s1) := by rw [← hd]; ring
    rw [this]; have := mul_nonneg h0 hs.le; linarith

theorem f_rec (k : ℕ) (x : P2) :
    det2 (V (k + 2)) x + det2 (V k) x = 2 * c1 * det2 (V (k + 1)) x := by
  simp only [det2]
  linear_combination (x 1) * V_rec0 k - (x 0) * V_rec1 k

theorem two_step (k : ℕ) (x : P2) (h1 : 0 ≤ det2 (V k) x) (h2 : det2 (V (k + 1)) x ≤ 0)
    (h3 : 0 ≤ det2 (V (k + 2)) x) : det2 (V k) x = 0 := by
  have := f_rec k x
  have hc : 0 < c1 := by have := c1_b; linarith
  nlinarith [mul_nonneg hc.le (neg_nonneg.mpr h2)]

theorem S_inter_null (i j : ℕ) (hi : i < 5) (hj : j < 5) (hij : i < j) :
    volume (convexHull ℝ {0, V i, V (i + 1)} ∩ convexHull ℝ {0, V j, V (j + 1)}) = 0 := by
  have key : ∀ a : ℕ, (∀ x, x ∈ convexHull ℝ {0, V i, V (i + 1)} → x ∈ convexHull ℝ {0, V j, V (j + 1)} →
      det2 (V a) x = 0) → volume (convexHull ℝ {0, V i, V (i + 1)} ∩ convexHull ℝ {0, V j, V (j + 1)}) = 0 := by
    intro a h
    exact measure_mono_null (fun x hx => h x hx.1 hx.2) (line_null (V a) (V_ne_zero a))
  have p5 : ∀ x, det2 (V 5) x = det2 (V 0) x := fun x => by rw [V5]
  have p6 : ∀ x, det2 (V 6) x = det2 (V 1) x := fun x => by
    have := V_add_five 1; simp at this; rw [this]
  interval_cases i <;> interval_cases j <;> first | omega | skip
  · apply key 1; intro x h h'
    exact le_antisymm (S_cone 0 x h).2 (S_cone 1 x h').1
  · apply key 0; intro x h h'
    exact two_step 0 x (S_cone 0 x h).1 (S_cone 0 x h).2 (S_cone 2 x h').1
  · apply key 3; intro x h h'
    refine two_step 3 x (S_cone 3 x h').1 (S_cone 3 x h').2 ?_
    have := (S_cone 0 x h).1; rw [show (3 + 2 : ℕ) = 5 from rfl, p5]; exact this
  · apply key 0; intro x h h'
    have h1 := (S_cone 0 x h).1
    have h2 := (S_cone 4 x h').2
    rw [show (4 + 1 : ℕ) = 5 from rfl, p5] at h2
    exact le_antisymm h2 h1
  · apply key 2; intro x h h'
    exact le_antisymm (S_cone 1 x h).2 (S_cone 2 x h').1
  · apply key 1; intro x h h'
    exact two_step 1 x (S_cone 1 x h).1 (S_cone 1 x h).2 (S_cone 3 x h').1
  · apply key 4; intro x h h'
    refine two_step 4 x (S_cone 4 x h').1 ?_ ?_
    · have := (S_cone 4 x h').2; rwa [show (4 + 1 : ℕ) = 5 from rfl] at this
    · rw [show (4 + 2 : ℕ) = 6 from rfl, p6]; exact (S_cone 1 x h).1
  · apply key 3; intro x h h'
    exact le_antisymm (S_cone 2 x h).2 (S_cone 3 x h').1
  · apply key 2; intro x h h'
    exact two_step 2 x (S_cone 2 x h).1 (S_cone 2 x h).2 (S_cone 4 x h').1
  · apply key 4; intro x h h'
    exact le_antisymm (S_cone 3 x h).2 (S_cone 4 x h').1


def Pset : Set P2 := {x | ∀ k ∈ Finset.range 5, 0 ≤ det2 (V (k + 1) - V k) (x - V k)}

theorem Pset_convex : Convex ℝ Pset := by
  intro x hx y hy a b ha hb hab k hk
  have h1 := hx k hk
  have h2 := hy k hk
  have : det2 (V (k + 1) - V k) (a • x + b • y - V k) =
      a * det2 (V (k + 1) - V k) (x - V k) + b * det2 (V (k + 1) - V k) (y - V k) := by
    obtain rfl : b = 1 - a := by linarith
    simp only [det2, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [this]
  positivity

theorem vert_in_P (k j : ℕ) (hk : k < 5) (hj : j < 5) :
    0 ≤ det2 (V (k + 1) - V k) (V j - V k) := by
  have := c1_b; have := c2_b; have := s1_b; have := s2_b
  interval_cases k <;> interval_cases j <;>
    simp only [Nat.reduceAdd, V0, V1, V2, V3, V4, V5, det2, PiLp.sub_apply] <;>
    simp <;>
    nlinarith [c1_b.1, c1_b.2, c2_b.1, c2_b.2, s1_b.1, s1_b.2, s2_b.1, s2_b.2]

theorem K_sub_P : pentagonK ⊆ Pset := by
  apply convexHull_min _ Pset_convex
  rintro _ ⟨j, hj, rfl⟩ k hk
  exact vert_in_P k j (by simpa using hk) (by simpa using hj)

theorem f_sum (x : P2) : det2 (V 0) x + det2 (V 1) x + det2 (V 2) x + det2 (V 3) x + det2 (V 4) x = 0 := by
  have r0 := f_rec 0 x
  have r1 := f_rec 1 x
  have r2 := f_rec 2 x
  have r3 := f_rec 3 x
  have r4 := f_rec 4 x
  have p5 : det2 (V 5) x = det2 (V 0) x := by rw [V5]
  have p6 : det2 (V 6) x = det2 (V 1) x := by
    have := V_add_five 1; simp at this; rw [this]
  simp only [Nat.reduceAdd] at r0 r1 r2 r3 r4
  have hc : c1 < 1 := by have := c1_b; linarith
  have : (1 - c1) * (det2 (V 0) x + det2 (V 1) x + det2 (V 2) x + det2 (V 3) x + det2 (V 4) x) = 0 := by
    linear_combination (1 / 2) * (r0 + r1 + r2 + r3 + r4) - (1 / 2) * (1 - 2 * c1) * p5 - (1 / 2) * p6
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact h

theorem cover (x : P2) (hx : x ∈ Pset) : ∃ k, k < 5 ∧ x ∈ convexHull ℝ {0, V k, V (k + 1)} := by
  have hs := f_sum x
  have p5 : det2 (V 5) x = det2 (V 0) x := by rw [V5]
  have : ∃ k, k < 5 ∧ 0 ≤ det2 (V k) x ∧ det2 (V (k + 1)) x ≤ 0 := by
    by_contra h
    push_neg at h
    have i0 : det2 (V 0) x < 0 ∨ 0 < det2 (V 1) x := by
      by_cases a : 0 ≤ det2 (V 0) x
      · right; by_contra b; exact absurd (h 0 (by norm_num) a) (by simpa using not_lt.mp b)
      · left; linarith [not_le.mp a]
    have i1 : det2 (V 1) x < 0 ∨ 0 < det2 (V 2) x := by
      by_cases a : 0 ≤ det2 (V 1) x
      · right; by_contra b; exact absurd (h 1 (by norm_num) a) (by simpa using not_lt.mp b)
      · left; linarith [not_le.mp a]
    have i2 : det2 (V 2) x < 0 ∨ 0 < det2 (V 3) x := by
      by_cases a : 0 ≤ det2 (V 2) x
      · right; by_contra b; exact absurd (h 2 (by norm_num) a) (by simpa using not_lt.mp b)
      · left; linarith [not_le.mp a]
    have i3 : det2 (V 3) x < 0 ∨ 0 < det2 (V 4) x := by
      by_cases a : 0 ≤ det2 (V 3) x
      · right; by_contra b; exact absurd (h 3 (by norm_num) a) (by simpa using not_lt.mp b)
      · left; linarith [not_le.mp a]
    have i4 : det2 (V 4) x < 0 ∨ 0 < det2 (V 5) x := by
      by_cases a : 0 ≤ det2 (V 4) x
      · right; by_contra b; exact absurd (h 4 (by norm_num) a) (by simpa using not_lt.mp b)
      · left; linarith [not_le.mp a]
    rcases i0 with a0 | a0 <;> rcases i1 with a1 | a1 <;> rcases i2 with a2 | a2 <;>
      rcases i3 with a3 | a3 <;> rcases i4 with a4 | a4 <;> linarith
  obtain ⟨k, hk, h1, h2⟩ := this
  refine ⟨k, hk, mem_hull_of (V k) (V (k + 1)) x ?_ h1 ?_ ?_⟩
  · rw [det_VV]; exact s1_pos
  · have : det2 x (V (k + 1)) = -det2 (V (k + 1)) x := by simp only [det2]; ring
    rw [this]; linarith
  · exact hx k (by simpa using hk)

theorem K_eq_union : pentagonK = ⋃ k ∈ Finset.range 5, convexHull ℝ {0, V k, V (k + 1)} := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨k, hk, hxk⟩ := cover x (K_sub_P hx)
    simp only [mem_iUnion]
    exact ⟨k, by simpa using hk, hxk⟩
  · intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨k, hk, hxk⟩ := hx
    exact S_sub k (by simpa using hk) hxk

theorem volume_pentagonK : volume pentagonK = ENNReal.ofReal (5 / 2 * Real.sin (2 * Real.pi / 5)) := by
  rw [K_eq_union, measure_biUnion_finset₀]
  · have : ∀ k ∈ Finset.range 5, volume (convexHull ℝ {0, V k, V (k + 1)}) = ENNReal.ofReal (s1 / 2) := by
      intro k _
      have hd := det_VV k
      unfold det2 at hd
      rw [vol_hull, hd, abs_of_pos s1_pos]
    rw [Finset.sum_congr rfl this]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [show ((5 : ℕ) : ENNReal) = ENNReal.ofReal 5 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; simp only [s1]; ring
  · intro i hi j hj hij
    simp only [Finset.coe_range, mem_Iio] at hi hj
    rcases lt_or_gt_of_ne hij with h | h
    · exact S_inter_null i j hi hj h
    · show volume (_ ∩ _) = 0
      rw [inter_comm]; exact S_inter_null j i hj hi h
  · intro k _
    exact ((Set.toFinite ({0, V k, V (k + 1)} : Set P2)).isCompact_convexHull ℝ).isClosed.measurableSet.nullMeasurableSet

end Viterbo.VolPent

end
end

section
section
open MeasureTheory Set

namespace Viterbo.Vol3
open Viterbo.VolTri Viterbo.VolFan Viterbo.VolPent Viterbo

noncomputable def rotMap : P2 →ₗ[ℝ] P2 := colMap !₂[0, -1] !₂[1, 0]

theorem rotMap_V (k : ℕ) : rotMap (V k) = rotatedVertex k := by
  rw [rotMap, colMap_apply]
  have h : -(Real.pi / 2) + 2 * Real.pi * k / 5 = 2 * Real.pi * k / 5 - Real.pi / 2 := by ring
  ext i
  fin_cases i
  · simp [rotatedVertex, V_one, h, Real.cos_sub_pi_div_two]
  · simp [rotatedVertex, V_zero, h, Real.sin_sub_pi_div_two]

theorem T_eq : pentagonT = rotMap '' pentagonK := by
  rw [pentagonT, pentagonK, LinearMap.image_convexHull, ← Set.image_comp]
  congr 1
  ext x
  simp only [mem_image, Function.comp, Finset.coe_range, mem_Iio]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, by rw [← rotMap_V]; rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, by rw [← rotMap_V]; rfl⟩

theorem det_rotMap : LinearMap.det rotMap = 1 := by
  rw [rotMap, det_colMap]; simp

theorem volume_pentagonT : volume pentagonT = ENNReal.ofReal (5 / 2 * Real.sin (2 * Real.pi / 5)) := by
  rw [T_eq, Measure.addHaar_image_linearMap, det_rotMap]
  simp [volume_pentagonK]

theorem alg : (2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5))) ^ 2 /
    (2 * ((5 / 2 * Real.sin (2 * Real.pi / 5)) * (5 / 2 * Real.sin (2 * Real.pi / 5)))) =
    (Real.sqrt 5 + 3) / 5 := by
  have h5 := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hC := Real.cos_pi_div_five
  have hh : Real.cos (Real.pi / 10) ^ 2 = (1 + Real.cos (Real.pi / 5)) / 2 := by
    have : Real.pi / 5 = 2 * (Real.pi / 10) := by ring
    rw [this, Real.cos_two_mul]; ring
  have hs := s1_sq
  have hc1 := c1_val
  have hs1 : Real.sin (2 * Real.pi / 5) ^ 2 = (5 + Real.sqrt 5) / 8 := by
    have : s1 = Real.sin (2 * Real.pi / 5) := rfl
    rw [← this, hs, hc1]; nlinarith
  have hpos : 0 < Real.sqrt 5 := by positivity
  have e1 : (2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5))) ^ 2 =
      (25 + 10 * Real.sqrt 5) / 4 := by
    have : (2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5))) ^ 2 =
        4 * Real.cos (Real.pi / 10) ^ 2 * (1 + Real.cos (Real.pi / 5)) ^ 2 := by ring
    rw [this, hh, hC]; nlinarith
  have e2 : 2 * ((5 / 2 * Real.sin (2 * Real.pi / 5)) * (5 / 2 * Real.sin (2 * Real.pi / 5))) =
      25 * (5 + Real.sqrt 5) / 16 := by
    have : 2 * ((5 / 2 * Real.sin (2 * Real.pi / 5)) * (5 / 2 * Real.sin (2 * Real.pi / 5))) =
        25 / 2 * Real.sin (2 * Real.pi / 5) ^ 2 := by ring
    rw [this, hs1]; ring
  rw [e1, e2]
  have : (5 + Real.sqrt 5) ≠ 0 := by positivity
  field_simp
  nlinarith

theorem volume_prod : volume (pentagonK ×ˢ pentagonT : Set (OAI.SymmetricPolar.Phase 2)) =
    ENNReal.ofReal (5 / 2 * Real.sin (2 * Real.pi / 5)) * ENNReal.ofReal (5 / 2 * Real.sin (2 * Real.pi / 5)) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, volume_pentagonK, volume_pentagonT]

theorem final :
    volume pentagonK = ENNReal.ofReal (5 / 2 * Real.sin (2 * Real.pi / 5)) ∧
      volume pentagonT = ENNReal.ofReal (5 / 2 * Real.sin (2 * Real.pi / 5)) ∧
      systolicRatio (pentagonK ×ˢ pentagonT) = ENNReal.ofReal ((Real.sqrt 5 + 3) / 5) ∧
      1 < systolicRatio (pentagonK ×ˢ pentagonT) := by
  have h3 : systolicRatio (pentagonK ×ˢ pentagonT) = ENNReal.ofReal ((Real.sqrt 5 + 3) / 5) := by
    rw [systolicRatio, Viterbo.cEHZ_pentagonK_prod_pentagonT, volume_prod]
    have hA : 0 < 5 / 2 * Real.sin (2 * Real.pi / 5) := by
      have := s1_pos; unfold s1 at this; positivity
    have hc0 : 0 ≤ 2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5)) := by
      have h1 : 0 ≤ Real.cos (Real.pi / 10) :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have h2 := Real.neg_one_le_cos (Real.pi / 5)
      have : 0 ≤ 1 + Real.cos (Real.pi / 5) := by linarith
      positivity
    rw [← alg, ← ENNReal.ofReal_pow hc0]
    rw [← ENNReal.ofReal_mul hA.le, show ((Nat.factorial 2 : ℕ) : ENNReal) = ENNReal.ofReal 2 by simp [Nat.factorial],
      ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_div_of_pos (by positivity)]
  refine ⟨volume_pentagonK, volume_pentagonT, h3, ?_⟩
  rw [h3, ENNReal.one_lt_ofReal]
  have h5 := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have : 2 < Real.sqrt 5 := by
    apply Real.lt_sqrt_of_sq_lt; norm_num
  linarith

end Viterbo.Vol3

theorem Viterbo.volume_pentagon_and_systolicRatio_pentagonK_prod_pentagonT :
    MeasureTheory.volume Viterbo.pentagonK = ENNReal.ofReal (5 / 2 * Real.sin (2 * Real.pi / 5)) ∧
      MeasureTheory.volume Viterbo.pentagonT = ENNReal.ofReal (5 / 2 * Real.sin (2 * Real.pi / 5)) ∧
      Viterbo.systolicRatio (Viterbo.pentagonK ×ˢ Viterbo.pentagonT) = ENNReal.ofReal ((Real.sqrt 5 + 3) / 5) ∧
      1 < Viterbo.systolicRatio (Viterbo.pentagonK ×ˢ Viterbo.pentagonT) :=
  Viterbo.Vol3.final

end
end

section
open MeasureTheory
open Viterbo

theorem solution :
    volume pentagonK = ENNReal.ofReal (5 / 2 * Real.sin (2 * Real.pi / 5)) ∧
      volume pentagonT = ENNReal.ofReal (5 / 2 * Real.sin (2 * Real.pi / 5)) ∧
      systolicRatio (pentagonK ×ˢ pentagonT) = ENNReal.ofReal ((Real.sqrt 5 + 3) / 5) ∧
      1 < systolicRatio (pentagonK ×ˢ pentagonT) := by
  apply Viterbo.volume_pentagon_and_systolicRatio_pentagonK_prod_pentagonT <;> assumption

end
