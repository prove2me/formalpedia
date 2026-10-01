-- Prove2me | solution 1 for WangZahlKakeya.KTCW_le_wolff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T11:01:06.024034+00:00
-- url     : https://prove2.me/submissions/9918f16d-ce16-43fa-ba37-bec5165ac89c

import Mathlib
import Definitions.Def_WangZahlKakeya_wolff

/-! d4fe49d1 KTCW_le_wolff. Tube-volume helpers copied from scratch/probe/66585d34.lean. -/

set_option autoImplicit false

namespace WZTubeVolAux

open MeasureTheory Metric Set WangZahlKakeya

/-- Membership in a closed ball about the origin of `E3`, in coordinates. -/
lemma mem_closedBall_zero_E3 {δ : ℝ} (hδ : 0 ≤ δ) (y : E3) :
    y ∈ closedBall (0 : E3) δ ↔ y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 ≤ δ ^ 2 := by
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_le_left hδ]
  simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

/-- Membership in a closed ball about the origin of the Euclidean plane, in coordinates. -/
lemma mem_closedBall_zero_E2 {δ : ℝ} (hδ : 0 ≤ δ) (z : Fin 2 → ℝ) :
    WithLp.toLp 2 z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) δ ↔ z 0 ^ 2 + z 1 ^ 2 ≤ δ ^ 2 := by
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_le_left hδ]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- Membership in the reference tube, in coordinates. -/
lemma mem_tube_iff {δ : ℝ} (hδ : 0 ≤ δ) (x : E3) :
    x ∈ tube 0 (EuclideanSpace.single 0 (1 : ℝ)) δ ↔
      ∃ t ∈ Icc (0 : ℝ) 1, (x 0 - t) ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≤ δ ^ 2 := by
  unfold tube
  simp only [mem_iUnion, exists_prop, zero_add]
  refine exists_congr fun t => and_congr Iff.rfl ?_
  rw [mem_closedBall, dist_eq_norm, EuclideanSpace.norm_eq, Real.sqrt_le_left hδ]
  simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

/-- The coordinate splitting `E3 → ℝ × ℝ²` is measure preserving. -/
lemma split_mp :
    MeasurePreserving
      (Prod.map id (WithLp.toLp 2) ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) ∘
        (WithLp.ofLp : E3 → (Fin 3 → ℝ)))
      (volume : Measure E3) (volume : Measure (ℝ × EuclideanSpace ℝ (Fin 2))) := by
  have h1 := PiLp.volume_preserving_ofLp (Fin 3)
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_toLp (Fin 2))
  exact h3.comp (h2.comp h1)

lemma split_apply (x : E3) :
    (Prod.map id (WithLp.toLp 2) ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) ∘
        (WithLp.ofLp : E3 → (Fin 3 → ℝ))) x = (x 0, WithLp.toLp 2 (fun j : Fin 2 => x j.succ)) := by
  simp [MeasurableEquiv.piFinSuccAbove_apply]
  rfl

end WZTubeVolAux

namespace WZTubeVolAux2

open MeasureTheory Metric Set WangZahlKakeya

theorem tubeVol_comparable' (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    3 * δ ^ 2 ≤ WangZahlKakeya.tubeVol δ ∧ WangZahlKakeya.tubeVol δ ≤ 8 * δ ^ 2 := by
  have hδ0 : 0 ≤ δ := hδ.le
  set e : E3 := EuclideanSpace.single 0 (1 : ℝ) with he
  set F := (Prod.map id (WithLp.toLp 2) ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) ∘
        (WithLp.ofLp : E3 → (Fin 3 → ℝ))) with hF
  -- the solid cylinder `[0,1] × disc(δ)`
  set Cyl : Set E3 := F ⁻¹' (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin 2)) δ) with hCyl
  have mem_Cyl : ∀ x : E3, x ∈ Cyl ↔ (0 ≤ x 0 ∧ x 0 ≤ 1) ∧ x 1 ^ 2 + x 2 ^ 2 ≤ δ ^ 2 := by
    intro x
    rw [hCyl, mem_preimage, hF, WZTubeVolAux.split_apply, mem_prod, mem_Icc, WZTubeVolAux.mem_closedBall_zero_E2 hδ0]
    rfl
  have vol_Cyl : volume Cyl = ENNReal.ofReal (Real.pi * δ ^ 2) := by
    rw [hCyl, WZTubeVolAux.split_mp.measure_preimage
      (measurableSet_Icc.prod measurableSet_closedBall).nullMeasurableSet,
      Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
      EuclideanSpace.volume_closedBall_fin_two]
    rw [← ENNReal.ofReal_pow hδ0, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have vol_ball : volume (closedBall (0 : E3) δ) = ENNReal.ofReal (Real.pi * 4 / 3 * δ ^ 3) := by
    rw [EuclideanSpace.volume_closedBall_fin_three, ← ENNReal.ofReal_pow hδ0,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have tube_eq : WangZahlKakeya.tubeVol δ = (volume (tube 0 e δ)).toReal := rfl
  -- the two end caps
  set Bm : Set E3 := {x : E3 | x 0 < 0} ∩ closedBall (0 : E3) δ with hBm
  set Bp' : Set E3 := {x : E3 | 0 < x 0} ∩ closedBall (0 : E3) δ with hBp'
  set Bp : Set E3 := (fun x => x + (-e)) ⁻¹' Bp' with hBp
  have hBp'meas : MeasurableSet Bp' := by
    refine MeasurableSet.inter ?_ measurableSet_closedBall
    exact (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hdisj : Disjoint Bm Bp' := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have a := hx1.1
    have b := hx2.1
    simp only [mem_ofPred_eq] at a b
    linarith
  have caps : volume Bm + volume Bp ≤ ENNReal.ofReal (Real.pi * 4 / 3 * δ ^ 3) := by
    rw [hBp, measure_preimage_add_right, ← measure_union hdisj hBp'meas, ← vol_ball]
    exact measure_mono (union_subset inter_subset_right inter_subset_right)
  -- tube is covered
  have cover : tube 0 e δ ⊆ Cyl ∪ Bm ∪ Bp := by
    intro x hx
    rw [he, WZTubeVolAux.mem_tube_iff hδ0] at hx
    obtain ⟨t, ⟨ht0, ht1⟩, hxt⟩ := hx
    rcases lt_or_ge (x 0) 0 with h0 | h0
    · left; right
      refine ⟨h0, ?_⟩
      rw [WZTubeVolAux.mem_closedBall_zero_E3 hδ0]
      nlinarith
    rcases lt_or_ge 1 (x 0) with h1 | h1
    · right
      rw [hBp, mem_preimage]
      have c0 : (x + -e) 0 = x 0 - 1 := by simp [he]; ring
      have c1 : (x + -e) 1 = x 1 := by simp [he]
      have c2 : (x + -e) 2 = x 2 := by simp [he]
      refine ⟨?_, ?_⟩
      · show 0 < (x + -e) 0
        rw [c0]; linarith
      · rw [WZTubeVolAux.mem_closedBall_zero_E3 hδ0, c0, c1, c2]
        nlinarith
    · left; left
      rw [mem_Cyl]
      exact ⟨⟨h0, h1⟩, by nlinarith⟩
  have inner : Cyl ⊆ tube 0 e δ := by
    intro x hx
    rw [mem_Cyl] at hx
    rw [he, WZTubeVolAux.mem_tube_iff hδ0]
    exact ⟨x 0, ⟨hx.1.1, hx.1.2⟩, by nlinarith [hx.2]⟩
  have upper : volume (tube 0 e δ) ≤
      ENNReal.ofReal (Real.pi * δ ^ 2 + Real.pi * 4 / 3 * δ ^ 3) := by
    calc volume (tube 0 e δ) ≤ volume (Cyl ∪ Bm ∪ Bp) := measure_mono cover
      _ ≤ volume (Cyl ∪ Bm) + volume Bp := measure_union_le _ _
      _ ≤ volume Cyl + volume Bm + volume Bp := by gcongr; exact measure_union_le _ _
      _ = volume Cyl + (volume Bm + volume Bp) := by rw [add_assoc]
      _ ≤ ENNReal.ofReal (Real.pi * δ ^ 2) + ENNReal.ofReal (Real.pi * 4 / 3 * δ ^ 3) := by
          rw [vol_Cyl]; exact add_le_add_right caps _
      _ = ENNReal.ofReal (Real.pi * δ ^ 2 + Real.pi * 4 / 3 * δ ^ 3) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  have fin : volume (tube 0 e δ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top upper
  have lower : ENNReal.ofReal (Real.pi * δ ^ 2) ≤ volume (tube 0 e δ) := by
    rw [← vol_Cyl]; exact measure_mono inner
  rw [tube_eq]
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  have hd2 : 0 < δ ^ 2 := by positivity
  have hd3 : δ ^ 3 ≤ δ ^ 2 := by
    have : δ ^ 3 = δ ^ 2 * δ := by ring
    rw [this]; nlinarith
  constructor
  · have := (ENNReal.ofReal_le_iff_le_toReal fin).mp lower
    calc 3 * δ ^ 2 ≤ Real.pi * δ ^ 2 := by nlinarith
      _ ≤ _ := this
  · refine le_trans (ENNReal.toReal_le_of_le_ofReal (by positivity) upper) ?_
    nlinarith [mul_le_mul_of_nonneg_left hd3 Real.pi_pos.le]

end WZTubeVolAux2


namespace WZKTWAux

open MeasureTheory Metric Set WangZahlKakeya
open scoped ENNReal

lemma closedBall_subset_tube (p w : E3) (δ : ℝ) : closedBall p δ ⊆ tube p w δ := by
  intro x hx
  simp only [tube, mem_iUnion, exists_prop]
  exact ⟨0, ⟨le_refl _, zero_le_one⟩, by simpa using hx⟩

lemma delta_le_one {δ : ℝ} {p v : E3} (hv : ‖v‖ = 1) (hsub : tube p v δ ⊆ closedBall (0 : E3) 1)
    (hδ : 0 ≤ δ) : δ ≤ 1 := by
  have h1 : p + δ • v ∈ closedBall (0 : E3) 1 := by
    apply hsub; apply closedBall_subset_tube
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hv, Real.norm_eq_abs,
      abs_of_nonneg hδ, mul_one]
  have h2 : p - δ • v ∈ closedBall (0 : E3) 1 := by
    apply hsub; apply closedBall_subset_tube
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hv,
      Real.norm_eq_abs, abs_of_nonneg hδ, mul_one]
  rw [mem_closedBall_zero_iff] at h1 h2
  have h3 : ‖(p + δ • v) - (p - δ • v)‖ = 2 * δ := by
    rw [add_sub_sub_cancel, ← two_smul ℝ (δ • v), smul_smul, norm_smul, hv, Real.norm_eq_abs,
      abs_of_nonneg (by linarith), mul_one]
  have h4 := norm_sub_le (p + δ • v) (p - δ • v)
  linarith

lemma dot_eq_inner (x y : E3) : dot x y = inner ℝ x y := by
  simp [dot, PiLp.inner_apply, mul_comm]

lemma dot_coords (x y : E3) : dot x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [dot, Fin.sum_univ_three]

lemma norm_sq_dot (x : E3) : ‖x‖ ^ 2 = dot x x := by
  rw [dot_eq_inner, real_inner_self_eq_norm_sq]

lemma abs_dot_le (x y : E3) : |dot x y| ≤ ‖x‖ * ‖y‖ := by
  rw [dot_eq_inner]; exact abs_real_inner_le_norm x y

lemma dot_sub_l (x y z : E3) : dot (x - y) z = dot x z - dot y z := by
  simp only [dot_coords, PiLp.sub_apply]; ring

lemma dot_smul_l (c : ℝ) (x z : E3) : dot (c • x) z = c * dot x z := by
  simp only [dot_coords, PiLp.smul_apply, smul_eq_mul]; ring

lemma dot_smul_r (c : ℝ) (x z : E3) : dot z (c • x) = c * dot z x := by
  simp only [dot_coords, PiLp.smul_apply, smul_eq_mul]; ring

lemma dot_comm' (x y : E3) : dot x y = dot y x := by
  simp only [dot_coords]; ring

lemma norm_one_of_dot {x : E3} (h : dot x x = 1) : ‖x‖ = 1 := by
  have h2 : ‖x‖ ^ 2 = 1 := by rw [norm_sq_dot, h]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) (by norm_num)).mp h2

/-- The cross product on `E3`, in coordinates. -/
noncomputable def crs (x y : E3) : E3 :=
  WithLp.toLp 2 ![x 1 * y 2 - x 2 * y 1, x 2 * y 0 - x 0 * y 2, x 0 * y 1 - x 1 * y 0]

lemma crs_apply (x y : E3) :
    crs x y 0 = x 1 * y 2 - x 2 * y 1 ∧ crs x y 1 = x 2 * y 0 - x 0 * y 2 ∧
      crs x y 2 = x 0 * y 1 - x 1 * y 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [crs]

lemma dot_crs_left (x y : E3) : dot (crs x y) x = 0 := by
  obtain ⟨h0, h1, h2⟩ := crs_apply x y
  rw [dot_coords, h0, h1, h2]; ring

lemma dot_crs_right (x y : E3) : dot (crs x y) y = 0 := by
  obtain ⟨h0, h1, h2⟩ := crs_apply x y
  rw [dot_coords, h0, h1, h2]; ring

lemma dot_crs_self (x y : E3) :
    dot (crs x y) (crs x y) = dot x x * dot y y - dot x y ^ 2 := by
  obtain ⟨h0, h1, h2⟩ := crs_apply x y
  rw [dot_coords, dot_coords, dot_coords, dot_coords, h0, h1, h2]; ring

lemma crs_sub_smul (v a : E3) (c : ℝ) : crs v (a - c • v) = crs v a := by
  ext i
  fin_cases i <;> simp [crs] <;> ring

/-- The linear map `y ↦ y₀ a + y₁ b + y₂ v`. -/
noncomputable def Lmap (a b v : E3) : E3 →ₗ[ℝ] E3 where
  toFun y := y 0 • a + y 1 • b + y 2 • v
  map_add' x y := by
    simp only [PiLp.add_apply, add_smul]; abel
  map_smul' c x := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]

lemma Lmap_apply (a b v y : E3) : Lmap a b v y = y 0 • a + y 1 • b + y 2 • v := rfl

lemma det_Lmap (a b v : E3) : LinearMap.det (Lmap a b v) = dot b (crs v a) := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, Matrix.det_fin_three]
  obtain ⟨h0, h1, h2⟩ := crs_apply v a
  rw [dot_coords, h0, h1, h2]
  simp [LinearMap.toMatrix_apply, Lmap_apply]
  ring

/-- The cube `[0, 1/3]³`. -/
def Qbox : Set E3 := {y : E3 | ∀ i, y i ∈ Icc (0 : ℝ) (1 / 3)}

lemma vol_Qbox : volume Qbox = ENNReal.ofReal (1 / 27) := by
  have : Qbox = (WithLp.ofLp : E3 → (Fin 3 → ℝ)) ⁻¹'
      Icc (fun _ => (0 : ℝ)) (fun _ => 1 / 3) := by
    ext y; simp [Qbox, Pi.le_def, forall_and]
  rw [this, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi, Fin.prod_univ_three]
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- Geometric core: a convex set inside the unit ball which contains a `δ`-ball around `p`
and the unit segment `[p, p + v]` lies in an `a × b × 2` prism with `ab ≤ 432 |W|`. -/
lemma key {W : Set E3} (hW : Convex ℝ W) (hWB : W ⊆ closedBall (0 : E3) 1) {p v : E3}
    (hv : ‖v‖ = 1) {δ : ℝ} (hδ : 0 < δ) (hball : closedBall p δ ⊆ W)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p + t • v ∈ W) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ X : Set E3, IsPrismOfDims X ![a, b, 2] ∧ W ⊆ X ∧
      ENNReal.ofReal (a * b / 432) ≤ volume W := by
  have hvv : dot v v = 1 := by rw [← norm_sq_dot, hv]; norm_num
  have hpW : p ∈ W := hball (mem_closedBall_self hδ.le)
  have hpn : ‖p‖ ≤ 1 := by simpa using hWB hpW
  have hxn : ∀ x ∈ W, ‖x‖ ≤ 1 := fun x hx => by simpa using hWB hx
  have hxp : ∀ x ∈ W, ‖x - p‖ ≤ 2 := fun x hx => by
    have := norm_sub_le x p; linarith [hxn x hx]
  set P : E3 → E3 := fun x => (x - p) - dot (x - p) v • v with hP
  have hPv : ∀ x, dot (P x) v = 0 := by
    intro x; simp only [hP]; rw [dot_sub_l, dot_smul_l, hvv]; ring
  have hPbd : ∀ x ∈ W, ‖P x‖ ≤ 4 := by
    intro x hx
    have h1 := norm_sub_le (x - p) (dot (x - p) v • v)
    have h2 : ‖dot (x - p) v • v‖ ≤ 2 := by
      rw [norm_smul, hv, mul_one, Real.norm_eq_abs]
      have := abs_dot_le (x - p) v
      rw [hv, mul_one] at this
      linarith [hxp x hx]
    simp only [hP]; linarith [hxp x hx]
  -- some point of `W` has a nonzero component orthogonal to `v`
  have hPpos : ∃ y ∈ W, 0 < ‖P y‖ := by
    by_contra H
    push_neg at H
    have hz : ∀ i : Fin 3, P (p + δ • EuclideanSpace.single i (1 : ℝ)) = 0 := by
      intro i
      apply norm_le_zero_iff.mp
      apply H
      apply hball
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      simp [abs_of_pos hδ]
    have c00 := congrArg (fun z : E3 => z 0) (hz 0)
    have c11 := congrArg (fun z : E3 => z 1) (hz 1)
    have c10 := congrArg (fun z : E3 => z 0) (hz 1)
    simp [hP, dot_coords] at c00 c11 c10
    rcases c10 with (h1 | h1) | h1
    · linarith
    · simp [h1] at c11; linarith
    · simp [h1] at c00; linarith
  -- the extremal value `h`
  set S : Set ℝ := (fun x => ‖P x‖) '' W with hS
  have hSbdd : BddAbove S := ⟨4, by rintro _ ⟨x, hx, rfl⟩; exact hPbd x hx⟩
  have hSne : S.Nonempty := ⟨_, mem_image_of_mem _ hpW⟩
  set h : ℝ := sSup S with hh
  have hle : ∀ x ∈ W, ‖P x‖ ≤ h := fun x hx => le_csSup hSbdd (mem_image_of_mem _ hx)
  have hpos : 0 < h := by
    obtain ⟨y, hy, hy'⟩ := hPpos
    exact lt_of_lt_of_le hy' (hle y hy)
  obtain ⟨_, ⟨q, hqW, rfl⟩, hq⟩ := exists_lt_of_lt_csSup hSne (half_lt_self hpos)
  set hq' : ℝ := ‖P q‖ with hhq'
  have hq'pos : 0 < hq' := by linarith
  set d : E3 := P q with hd
  have hdd : dot d d = hq' ^ 2 := by rw [← norm_sq_dot]
  have hdv : dot d v = 0 := hPv q
  set e : E3 := hq'⁻¹ • d with he
  set f : E3 := hq'⁻¹ • crs v d with hf
  have hee : dot e e = 1 := by
    rw [he, dot_smul_l, dot_smul_r, hdd]; field_simp
  have hev : dot e v = 0 := by rw [he, dot_smul_l, hdv, mul_zero]
  have hfv : dot f v = 0 := by rw [hf, dot_smul_l, dot_crs_left, mul_zero]
  have hfe : dot f e = 0 := by rw [hf, he, dot_smul_l, dot_smul_r, dot_crs_right]; ring
  have hff : dot f f = 1 := by
    rw [hf, dot_smul_l, dot_smul_r, dot_crs_self, hvv, hdd, dot_comm' v d, hdv]; field_simp; ring
  have hen : ‖e‖ = 1 := norm_one_of_dot hee
  have hfn : ‖f‖ = 1 := norm_one_of_dot hff
  -- `e`-widths are bounded by `h`
  have hWe : ∀ x ∈ W, |dot (x - p) e| ≤ h := by
    intro x hx
    have : dot (x - p) e = dot (P x) e := by
      show dot (x - p) e = dot ((x - p) - dot (x - p) v • v) e
      rw [dot_sub_l (x - p) (dot (x - p) v • v) e, dot_smul_l, dot_comm' v e, hev]; ring
    rw [this]
    have := abs_dot_le (P x) e
    rw [hen, mul_one] at this
    linarith [hle x hx]
  -- the extremal value `w` in direction `f`
  set T : Set ℝ := (fun x => |dot (x - p) f|) '' W with hT
  have hTbdd : BddAbove T := ⟨2, by
    rintro _ ⟨x, hx, rfl⟩
    have := abs_dot_le (x - p) f
    rw [hfn, mul_one] at this
    linarith [hxp x hx]⟩
  have hTne : T.Nonempty := ⟨_, mem_image_of_mem _ hpW⟩
  set w : ℝ := sSup T with hw
  have hlew : ∀ x ∈ W, |dot (x - p) f| ≤ w := fun x hx => le_csSup hTbdd (mem_image_of_mem _ hx)
  have hwpos : 0 < w := by
    have hy : p + δ • f ∈ W := by
      apply hball
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hfn, mul_one,
        Real.norm_eq_abs, abs_of_pos hδ]
    have := hlew _ hy
    rw [add_sub_cancel_left, dot_smul_l, hff, mul_one, abs_of_pos hδ] at this
    linarith
  obtain ⟨_, ⟨r, hrW, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hTne (half_lt_self hwpos)
  -- the prism
  set c : E3 := p - dot p v • v with hc
  have hxc : ∀ x g : E3, dot (x - c) g = dot (x - p) g + dot p v * dot v g := by
    intro x g
    simp only [hc, dot_coords, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  set u : Fin 3 → E3 := ![e, f, v] with hu
  have hortho : ∀ i j, dot (u i) (u j) = if i = j then 1 else 0 := by
    have hef : dot e f = 0 := by rw [dot_comm']; exact hfe
    have hve : dot v e = 0 := by rw [dot_comm']; exact hev
    have hvf : dot v f = 0 := by rw [dot_comm']; exact hfv
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hu, hee, hef, hev, hfe, hff, hfv, hve, hvf, hvv]
  refine ⟨2 * h, 2 * w, by positivity, by positivity, prism c u ![2 * h, 2 * w, 2],
    ⟨c, u, hortho, rfl⟩, ?_, ?_⟩
  · intro x hx i
    fin_cases i
    · show |dot (x - c) e| ≤ 2 * h / 2
      rw [hxc, dot_comm' v e, hev, mul_zero, add_zero]
      linarith [hWe x hx]
    · show |dot (x - c) f| ≤ 2 * w / 2
      rw [hxc, dot_comm' v f, hfv, mul_zero, add_zero]
      linarith [hlew x hx]
    · show |dot (x - c) v| ≤ 2 / 2
      rw [hxc, hvv, mul_one, dot_sub_l, sub_add_cancel]
      have := abs_dot_le x v
      rw [hv, mul_one] at this
      linarith [hxn x hx]
  · -- volume
    set Lm := Lmap (q - p) (r - p) v with hLm
    have hcrs : crs v (q - p) = hq' • f := by
      rw [hf, smul_smul, mul_inv_cancel₀ hq'pos.ne', one_smul, hd]
      simp only [hP]
      rw [crs_sub_smul]
    have hdet : |LinearMap.det Lm| = hq' * |dot (r - p) f| := by
      rw [hLm, det_Lmap, hcrs, dot_smul_r, abs_mul, abs_of_pos hq'pos]
    have hdet_lb : h * w / 4 ≤ |LinearMap.det Lm| := by
      rw [hdet]
      have h0 : 0 ≤ |dot (r - p) f| := abs_nonneg _
      nlinarith
    have hsubW : (fun y => p + Lm y) '' Qbox ⊆ W := by
      rintro _ ⟨y, hy, rfl⟩
      have hy0 := hy 0
      have hy1 := hy 1
      have hy2 := hy 2
      simp only [mem_Icc] at hy0 hy1 hy2
      set s : ℝ := 1 - y 0 - y 1 with hs
      have hspos : 0 < s := by linarith
      have hlam : y 2 / s ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg hy2.1 hspos.le
        · rw [div_le_one hspos]; linarith
      have hmem := hW.sum_mem (t := Finset.univ) (w := ![s, y 0, y 1])
        (z := ![p + (y 2 / s) • v, q, r])
        (by intro i _; fin_cases i <;> simp <;> linarith)
        (by simp [Fin.sum_univ_three, hs]; ring)
        (by intro i _; fin_cases i
            · exact hseg _ hlam
            · exact hqW
            · exact hrW)
      convert hmem using 1
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ext j
      simp only [hLm, Lmap_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      have hs0 : s ≠ 0 := hspos.ne'
      field_simp
      rw [hs]; ring
    have hvolZ : volume ((fun y => p + Lm y) '' Qbox) =
        ENNReal.ofReal (|LinearMap.det Lm|) * ENNReal.ofReal (1 / 27) := by
      rw [← vol_Qbox, ← Measure.addHaar_image_linearMap]
      have : (fun y => p + Lm y) '' Qbox = (fun z => p + z) '' (Lm '' Qbox) := by
        rw [Set.image_image]
      rw [this, Set.image_add_left, measure_preimage_add]
    calc ENNReal.ofReal (2 * h * (2 * w) / 432)
        ≤ ENNReal.ofReal (|LinearMap.det Lm| * (1 / 27)) :=
          ENNReal.ofReal_le_ofReal (by nlinarith)
      _ = ENNReal.ofReal (|LinearMap.det Lm|) * ENNReal.ofReal (1 / 27) :=
          ENNReal.ofReal_mul (abs_nonneg _)
      _ = volume ((fun y => p + Lm y) '' Qbox) := hvolZ.symm
      _ ≤ volume W := measure_mono hsubW

end WZKTWAux

open MeasureTheory Metric Set WangZahlKakeya ENNReal in
theorem solution :
    ∃ M > (0 : ℝ), ∀ (δ : ℝ) (n : ℕ) (p v : Fin n → E3) (Y : Fin n → Set E3),
      IsTubeSystem δ n p v Y →
      (∀ a b : ℝ, 0 < a → 0 < b → ∀ W : Set E3, IsPrismOfDims W ![a, b, 2] →
        (tubeCountIn δ n p v W : ℝ) ≤ 100 * a * b * δ ^ (-2 : ℝ)) →
      KTCW δ n p v ≤ M := by
  refine ⟨345600, by norm_num, fun δ n p v Y hT hW => ?_⟩
  obtain ⟨hδ, hv, hsub, -, -, -⟩ := hT
  unfold KTCW
  refine csInf_le ⟨0, fun C hC => hC.1.le⟩ ⟨by norm_num, fun W hWc => ?_⟩
  by_cases h0 : tubeCountIn δ n p v W = 0
  · simp [h0]
  obtain ⟨i, hi⟩ : {i : Fin n | tube (p i) (v i) δ ⊆ W}.Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]; exact Nat.pos_of_ne_zero h0
  set W' : Set E3 := W ∩ closedBall (0 : E3) 1 with hW'
  have hW'c : Convex ℝ W' := hWc.inter (convex_closedBall 0 1)
  have htW' : tube (p i) (v i) δ ⊆ W' := subset_inter hi (hsub i)
  have hball : closedBall (p i) δ ⊆ W' := (WZKTWAux.closedBall_subset_tube _ _ _).trans htW'
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, p i + t • v i ∈ W' := fun t ht => htW' (by
    simp only [tube, mem_iUnion, exists_prop]; exact ⟨t, ht, mem_closedBall_self hδ.le⟩)
  obtain ⟨a, b, ha, hb, X, hX, hWX, hvol⟩ :=
    WZKTWAux.key hW'c inter_subset_right (hv i) hδ hball hseg
  have hcnt : tubeCountIn δ n p v W ≤ tubeCountIn δ n p v X := by
    unfold tubeCountIn
    apply Set.ncard_le_ncard _ (Set.toFinite _)
    intro j hj
    exact (subset_inter hj (hsub j)).trans hWX
  have hX' := hW a b ha hb X hX
  have hδ1 : δ ≤ 1 := WZKTWAux.delta_le_one (hv i) (hsub i) hδ.le
  have htv := (WZTubeVolAux2.tubeVol_comparable' δ hδ hδ1).2
  have htv0 : 0 ≤ tubeVol δ := ENNReal.toReal_nonneg
  have hrp : δ ^ (-2 : ℝ) * δ ^ 2 = 1 := by
    rw [Real.rpow_neg hδ.le, Real.rpow_two]; field_simp
  have hreal : (tubeCountIn δ n p v W : ℝ) * tubeVol δ ≤ 800 * (a * b) := by
    have h1 : (tubeCountIn δ n p v W : ℝ) ≤ 100 * a * b * δ ^ (-2 : ℝ) :=
      le_trans (by exact_mod_cast hcnt) hX'
    calc (tubeCountIn δ n p v W : ℝ) * tubeVol δ
        ≤ (100 * a * b * δ ^ (-2 : ℝ)) * (8 * δ ^ 2) :=
          mul_le_mul h1 htv htv0 (le_trans (by positivity) h1)
      _ = 800 * (a * b) * (δ ^ (-2 : ℝ) * δ ^ 2) := by ring
      _ = 800 * (a * b) := by rw [hrp, mul_one]
  calc (tubeCountIn δ n p v W : ℝ≥0∞) * ENNReal.ofReal (tubeVol δ)
      = ENNReal.ofReal ((tubeCountIn δ n p v W : ℝ) * tubeVol δ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (345600 * (a * b / 432)) := ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal 345600 * ENNReal.ofReal (a * b / 432) := ENNReal.ofReal_mul (by norm_num)
    _ ≤ ENNReal.ofReal 345600 * volume W' := by gcongr
    _ ≤ ENNReal.ofReal 345600 * volume W := by gcongr; exact inter_subset_left
