-- Prove2me | solution 1 for WangZahlKakeya.FSW_card_lower
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T04:47:20.743367+00:00
-- url     : https://prove2.me/submissions/830f7d0a-7045-411f-879a-89e1a040933a

import Mathlib
import Definitions.Def_WangZahlKakeya_wolff

/-! 66585d34 WangZahlKakeya.FSW_card_lower, with `c = 1/8`.
Route: the admissible set `S` of slab constants is nonempty (`C = 1/|B_δ|`), so
`FSW = sInf S`. For `C ∈ S`, test the slab `W = B_1 ∩ {|⟨x,u⟩ - ⟨p₀,u⟩| ≤ δ}` whose normal
`u = L e₁` is orthogonal to the first tube's direction (`L` = the reflection with `L v₀ = e₀`):
it contains that tube, and `L` carries it into a box of volume `2·2δ·2 = 8δ`. So
`1 ≤ C · 8δ · n`, i.e. `FSW ≥ 1/(8δn)`. With `|T| ≥ 3δ² ≥ δ²` (tubeVol_comparable, reproved
here; `δ ≤ 1` because the tube lies in the unit ball) this gives `FSW · n|T|^{1/2} ≥ 1/8`. -/

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

namespace WZFSWAux

open MeasureTheory Metric Set WangZahlKakeya
open scoped ENNReal

lemma closedBall_subset_tube (p w : E3) (δ : ℝ) : closedBall p δ ⊆ tube p w δ := by
  intro x hx
  simp only [tube, mem_iUnion, exists_prop]
  exact ⟨0, ⟨le_refl _, zero_le_one⟩, by simpa using hx⟩

lemma tube_subset_closedBall (p w : E3) (δ : ℝ) (hw : ‖w‖ ≤ 1) :
    tube p w δ ⊆ closedBall p (1 + δ) := by
  intro x hx
  simp only [tube, mem_iUnion, exists_prop] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, hxt⟩ := hx
  rw [mem_closedBall] at hxt ⊢
  have h1 : dist (p + t • w) p ≤ 1 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    nlinarith [norm_nonneg w]
  calc dist x p ≤ dist x (p + t • w) + dist (p + t • w) p := dist_triangle _ _ _
    _ ≤ 1 + δ := by linarith

lemma tubeVol_nonneg (δ : ℝ) : 0 ≤ tubeVol δ := ENNReal.toReal_nonneg

lemma tubeVol_pos {δ : ℝ} (hδ : 0 < δ) : 0 < tubeVol δ := by
  unfold tubeVol
  have hfin : volume (tube (0 : E3) (EuclideanSpace.single 0 (1 : ℝ)) δ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top measure_closedBall_lt_top.ne
      (measure_mono (tube_subset_closedBall _ _ _ ?_))
    simp
  have hpos : 0 < volume (tube (0 : E3) (EuclideanSpace.single 0 (1 : ℝ)) δ) :=
    lt_of_lt_of_le (measure_closedBall_pos volume 0 hδ) (measure_mono (closedBall_subset_tube _ _ _))
  exact ENNReal.toReal_pos hpos.ne' hfin

lemma count_le (δ : ℝ) (n : ℕ) (p v : Fin n → E3) (W : Set E3) :
    tubeCountIn δ n p v W ≤ n := by
  unfold tubeCountIn
  calc {i : Fin n | tube (p i) (v i) δ ⊆ W}.ncard ≤ Nat.card (Fin n) := Set.ncard_le_card _
    _ = n := Nat.card_eq_fintype_card.trans (Fintype.card_fin n)

lemma count_ball (δ : ℝ) (n : ℕ) (p v : Fin n → E3)
    (hsub : ∀ i, tube (p i) (v i) δ ⊆ closedBall (0 : E3) 1) :
    tubeCountIn δ n p v (closedBall (0 : E3) 1) = n := by
  unfold tubeCountIn
  have h : {i : Fin n | tube (p i) (v i) δ ⊆ closedBall (0 : E3) 1} = Set.univ :=
    Set.eq_univ_of_forall hsub
  rw [h, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]


lemma dot_eq_inner (x y : E3) : dot x y = inner ℝ x y := by
  simp [dot, PiLp.inner_apply, mul_comm]

lemma fsw_set_nonempty {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (p v : Fin n → E3) :
    {C : ℝ | 0 < C ∧ ∀ W : Set E3, IsSlab W →
      (tubeCountIn δ n p v W : ℝ≥0∞) ≤ ENNReal.ofReal C * volume W * (n : ℝ≥0∞)}.Nonempty := by
  set β : ℝ := (volume (closedBall (0 : E3) δ)).toReal with hβ
  have hβfin : volume (closedBall (0 : E3) δ) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hβpos : 0 < β := ENNReal.toReal_pos (measure_closedBall_pos volume 0 hδ).ne' hβfin
  refine ⟨1 / β, by positivity, fun W _ => ?_⟩
  by_cases h0 : tubeCountIn δ n p v W = 0
  · simp [h0]
  obtain ⟨i, hi⟩ : {i : Fin n | tube (p i) (v i) δ ⊆ W}.Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]
    exact Nat.pos_of_ne_zero h0
  have hW : volume (closedBall (0 : E3) δ) ≤ volume W := by
    rw [← Measure.addHaar_closedBall_center volume (p i)]
    exact measure_mono ((closedBall_subset_tube _ _ _).trans hi)
  have hcount : (tubeCountIn δ n p v W : ℝ≥0∞) ≤ n := by
    exact_mod_cast count_le δ n p v W
  have hone : ENNReal.ofReal (1 / β) * volume (closedBall (0 : E3) δ) = 1 := by
    rw [← ENNReal.ofReal_toReal hβfin, ← hβ, ← ENNReal.ofReal_mul (by positivity),
      one_div, inv_mul_cancel₀ hβpos.ne', ENNReal.ofReal_one]
  calc (tubeCountIn δ n p v W : ℝ≥0∞) ≤ n := hcount
    _ = ENNReal.ofReal (1 / β) * volume (closedBall (0 : E3) δ) * n := by rw [hone, one_mul]
    _ ≤ ENNReal.ofReal (1 / β) * volume W * n := by gcongr

lemma fsw_mem_lower {δ : ℝ} {n : ℕ} {p v : Fin n → E3} (hδ : 0 < δ) (hn : 0 < n)
    (hv : ∀ i, ‖v i‖ = 1) (hsub : ∀ i, tube (p i) (v i) δ ⊆ closedBall (0 : E3) 1) {C : ℝ}
    (hC : C ∈ {C : ℝ | 0 < C ∧ ∀ W : Set E3, IsSlab W →
      (tubeCountIn δ n p v W : ℝ≥0∞) ≤ ENNReal.ofReal C * volume W * (n : ℝ≥0∞)}) :
    1 ≤ C * (8 * δ) * n := by
  set i0 : Fin n := ⟨0, hn⟩
  set v0 := v i0
  set p0 := p i0
  set e0 : E3 := EuclideanSpace.single 0 (1 : ℝ) with he0
  set e1 : E3 := EuclideanSpace.single 1 (1 : ℝ) with he1
  have he0n : ‖e0‖ = 1 := by simp [e0]
  set L : E3 ≃ₗᵢ[ℝ] E3 := Submodule.reflection (ℝ ∙ (v0 - e0))ᗮ with hLdef
  have hL : L v0 = e0 := Submodule.reflection_sub (by rw [he0n, hv i0])
  have hLL : ∀ x, L (L x) = x := fun x => Submodule.reflection_reflection _ x
  set u : E3 := L e1 with hu
  have hun : ‖u‖ = 1 := by rw [hu, L.norm_map]; simp [e1]
  have hcoord : ∀ x : E3, inner ℝ x u = (L x) 1 := by
    intro x
    rw [← L.inner_map_map x u, hu, hLL, real_inner_comm, he1, EuclideanSpace.inner_single_left]
    simp
  have hv0u : inner ℝ v0 u = 0 := by
    rw [hcoord, hL, he0]; simp
  set c0 : ℝ := dot p0 u with hc0
  set W : Set E3 := closedBall (0 : E3) 1 ∩ {x : E3 | |dot x u - c0| ≤ δ} with hW
  have hslab : IsSlab W := ⟨u, c0, δ, hun, hδ.le, rfl⟩
  have htubeW : tube (p i0) (v i0) δ ⊆ W := by
    intro x hx
    refine ⟨hsub i0 hx, ?_⟩
    have hx' := hx
    simp only [tube, mem_iUnion, exists_prop] at hx'
    obtain ⟨s, _, hxs⟩ := hx'
    show |dot x u - c0| ≤ δ
    have key : dot x u - c0 = inner ℝ (x - (p0 + s • v0)) u := by
      rw [hc0, dot_eq_inner, dot_eq_inner, inner_sub_left, inner_add_left, real_inner_smul_left, hv0u]
      ring
    rw [key]
    calc |inner ℝ (x - (p0 + s • v0)) u| ≤ ‖x - (p0 + s • v0)‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ = dist x (p0 + s • v0) := by rw [hun, mul_one, dist_eq_norm]
      _ ≤ δ := hxs
  have hcnt : (1 : ℝ≥0∞) ≤ (tubeCountIn δ n p v W : ℝ≥0∞) := by
    have : 0 < tubeCountIn δ n p v W := by
      unfold tubeCountIn
      rw [Set.ncard_pos (Set.toFinite _)]
      exact ⟨i0, htubeW⟩
    exact_mod_cast this
  -- the volume of the slab
  set a : Fin 3 → ℝ := ![-1, c0 - δ, -1] with ha
  set b : Fin 3 → ℝ := ![1, c0 + δ, 1] with hb
  have hWbox : W ⊆ (⇑L) ⁻¹' ((WithLp.ofLp : E3 → (Fin 3 → ℝ)) ⁻¹' Icc a b) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx2' : |dot x u - c0| ≤ δ := hx2
    rw [dot_eq_inner, hcoord] at hx2'
    have hnx : ‖L x‖ ≤ 1 := by rw [L.norm_map]; simpa using hx1
    have hk : ∀ k : Fin 3, |(L x) k| ≤ 1 := by
      intro k
      have := PiLp.norm_apply_le (L x) k
      rw [Real.norm_eq_abs] at this
      linarith
    simp only [mem_preimage, mem_Icc]
    refine ⟨fun k => ?_, fun k => ?_⟩
    · fin_cases k
      · simp [a]; linarith [(abs_le.mp (hk 0)).1]
      · simp [a]; linarith [(abs_le.mp hx2').1]
      · simp [a]; linarith [(abs_le.mp (hk 2)).1]
    · fin_cases k
      · simp [b]; linarith [(abs_le.mp (hk 0)).2]
      · simp [b]; linarith [(abs_le.mp hx2').2]
      · simp [b]; linarith [(abs_le.mp (hk 2)).2]
  have hvolW : volume W ≤ ENNReal.ofReal (8 * δ) := by
    calc volume W ≤ volume ((⇑L) ⁻¹' ((WithLp.ofLp : E3 → (Fin 3 → ℝ)) ⁻¹' Icc a b)) :=
          measure_mono hWbox
      _ = volume ((WithLp.ofLp : E3 → (Fin 3 → ℝ)) ⁻¹' Icc a b) :=
          L.measurePreserving.measure_preimage
            (measurableSet_Icc.preimage (PiLp.volume_preserving_ofLp (Fin 3)).measurable).nullMeasurableSet
      _ = volume (Icc a b) :=
          (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage measurableSet_Icc.nullMeasurableSet
      _ = ENNReal.ofReal (8 * δ) := by
          rw [Real.volume_Icc_pi, Fin.prod_univ_three]
          simp only [a, b, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons]
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by nlinarith)]
          congr 1
          ring
  have h := hC.2 W hslab
  have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (C * (8 * δ) * n) := by
    calc (1 : ℝ≥0∞) ≤ (tubeCountIn δ n p v W : ℝ≥0∞) := hcnt
      _ ≤ ENNReal.ofReal C * volume W * (n : ℝ≥0∞) := h
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (8 * δ) * (n : ℝ≥0∞) := by gcongr
      _ = ENNReal.ofReal (C * (8 * δ) * n) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hC.1.le (by positivity) : (0 : ℝ) ≤ C * (8 * δ)),
            ENNReal.ofReal_mul hC.1.le, ENNReal.ofReal_natCast]
  exact ENNReal.one_le_ofReal.mp h2

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

end WZFSWAux

open MeasureTheory Metric Set WangZahlKakeya in
theorem solution :
    ∃ c > (0 : ℝ), ∀ (δ : ℝ) (n : ℕ) (p v : Fin n → E3) (Y : Fin n → Set E3),
      IsTubeSystem δ n p v Y → 0 < n →
      c ≤ FSW δ n p v * ((n : ℝ) * tubeVol δ ^ ((1 : ℝ) / 2)) := by
  refine ⟨1 / 8, by norm_num, fun δ n p v Y hT hn => ?_⟩
  obtain ⟨hδ, hv, hsub, -, -, -⟩ := hT
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ1 : δ ≤ 1 := WZFSWAux.delta_le_one (hv ⟨0, hn⟩) (hsub ⟨0, hn⟩) hδ.le
  have hF : 1 / (8 * δ * n) ≤ FSW δ n p v := by
    unfold FSW
    refine le_csInf (WZFSWAux.fsw_set_nonempty hδ n p v) (fun C hC => ?_)
    have := WZFSWAux.fsw_mem_lower hδ hn hv hsub hC
    rw [div_le_iff₀ (by positivity)]
    linarith
  have htv : 3 * δ ^ 2 ≤ tubeVol δ := (WZTubeVolAux2.tubeVol_comparable' δ hδ hδ1).1
  have hsq : δ ≤ tubeVol δ ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    calc δ = Real.sqrt (δ ^ 2) := (Real.sqrt_sq hδ.le).symm
      _ ≤ Real.sqrt (tubeVol δ) := Real.sqrt_le_sqrt (by nlinarith)
  calc (1 : ℝ) / 8 = 1 / (8 * δ * n) * (n * δ) := by field_simp
    _ ≤ FSW δ n p v * ((n : ℝ) * tubeVol δ ^ ((1 : ℝ) / 2)) := by
        apply mul_le_mul hF (by gcongr) (by positivity)
        exact le_trans (by positivity) hF
