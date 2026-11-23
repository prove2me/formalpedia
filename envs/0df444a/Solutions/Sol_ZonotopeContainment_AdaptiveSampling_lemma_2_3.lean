-- Prove2me | solution 1 for ZonotopeContainment.AdaptiveSampling.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:08:08.065088+00:00
-- url     : https://prove2.me/submissions/51f1e619-1750-4114-ab5b-df74588d18ef

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Algorithm
import Theorems.Thm_ZonotopeContainment_AdaptiveSampling_feasibility

open scoped BigOperators
open scoped MatrixOrder
open ZonotopeContainment.AdaptiveSampling

namespace Lemma23Aux

lemma support_eq_sum_abs {d n : ℕ} (v : Fin n → E d) (b : E d) :
    support v b = ∑ i, |inner ℝ b (v i)| := by
  unfold support
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, ⟨0, ⟨0, fun _ => by simp, by simp⟩, by simp⟩⟩
    · rintro _ ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      calc
        inner ℝ b (∑ i, t i • v i)
          = ∑ i, t i * inner ℝ b (v i) := by simp [inner_sum, real_inner_smul_right]
        _ ≤ ∑ i, |t i * inner ℝ b (v i)| := Finset.sum_le_sum (fun i _ => le_abs_self _)
        _ = ∑ i, |t i| * |inner ℝ b (v i)| := by simp [abs_mul]
        _ ≤ ∑ i, 1 * |inner ℝ b (v i)| := by
            gcongr with i
            exact ht i
        _ = ∑ i, |inner ℝ b (v i)| := by simp
  · have hbdd : BddAbove ((fun y => inner ℝ b y) '' zonotope v) := by
      refine ⟨∑ i, |inner ℝ b (v i)|, ?_⟩
      rintro _ ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      calc
        inner ℝ b (∑ i, t i • v i)
          = ∑ i, t i * inner ℝ b (v i) := by simp [inner_sum, real_inner_smul_right]
        _ ≤ ∑ i, |t i * inner ℝ b (v i)| := Finset.sum_le_sum (fun i _ => le_abs_self _)
        _ = ∑ i, |t i| * |inner ℝ b (v i)| := by simp [abs_mul]
        _ ≤ ∑ i, 1 * |inner ℝ b (v i)| := by
            gcongr with i
            exact ht i
        _ = ∑ i, |inner ℝ b (v i)| := by simp
    let t : Fin n → ℝ := fun i => if 0 ≤ inner ℝ b (v i) then 1 else -1
    have ht : ∀ i, |t i| ≤ 1 := by
      intro i; dsimp [t]; split_ifs <;> simp
    have hx_mem : (∑ i, t i • v i) ∈ zonotope v := ⟨t, ht, rfl⟩
    have hx_val : inner ℝ b (∑ i, t i • v i) = ∑ i, |inner ℝ b (v i)| := by
      rw [inner_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [real_inner_smul_right]
      dsimp [t]
      split_ifs with h
      · simp [abs_of_nonneg h]
      · simp [abs_of_neg (not_le.mp h)]
    rw [← hx_val]
    exact le_csSup hbdd ⟨∑ i, t i • v i, hx_mem, rfl⟩

lemma act_mul {d : ℕ} (M N : Mat d) (x : E d) :
    act (M * N) x = act M (act N x) := by
  ext k
  simp [act, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

lemma act_one {d : ℕ} (x : E d) : act (1 : Mat d) x = x := by
  ext k
  simp [act]

lemma inner_act_transpose {d : ℕ} (M : Mat d) (x y : E d) :
    inner ℝ x (act M y) = inner ℝ (act M.transpose x) y := by
  calc
    inner ℝ x (act M y)
      = dotProduct (M.mulVec y.ofLp) x.ofLp := by
          simp [act, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
    _ = dotProduct x.ofLp (M.mulVec y.ofLp) := dotProduct_comm _ _
    _ = dotProduct (M.vecMul x.ofLp) y.ofLp := Matrix.dotProduct_mulVec x.ofLp M y.ofLp
    _ = dotProduct (M.transpose.mulVec x.ofLp) y.ofLp := by rw [Matrix.mulVec_transpose]
    _ = dotProduct y.ofLp (M.transpose.mulVec x.ofLp) := dotProduct_comm _ _
    _ = inner ℝ (act M.transpose x) y := by
          simp [act, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]

lemma inner_act_symm {d : ℕ} {M : Mat d} (hM : M.IsHermitian) (x y : E d) :
    inner ℝ (act M x) y = inner ℝ x (act M y) := by
  have hMT : M.transpose = M := hM
  rw [inner_act_transpose M x y, hMT]

lemma act_rankOne {d : ℕ} (u x : E d) :
    act (rankOne u) x = (inner ℝ u x) • u := by
  ext k
  simp [act, rankOne, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct, mul_assoc, Finset.mul_sum, mul_comm]

lemma lewis_isHermitian {d n : ℕ} (v : Fin n → E d) : (lewis v).IsHermitian := by
  unfold lewis
  ext k l
  simp [Matrix.sum_apply, rankOne, Matrix.conjTranspose_apply, mul_comm]

lemma inner_lewis {d n : ℕ} (v : Fin n → E d) (x : E d) :
    inner ℝ x (act (lewis v) x) = ∑ i, ‖v i‖⁻¹ * (inner ℝ x (v i)) ^ 2 := by
  have hlin : act (lewis v) x = ∑ i, (‖v i‖⁻¹ : ℝ) • act (rankOne (v i)) x := by
    unfold lewis
    simp [act, map_sum, map_smul]
  rw [hlin, inner_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [act_rankOne, real_inner_smul_right, real_inner_smul_right, real_inner_comm (v i) x]
  ring

lemma inner_weightedMatrix {d n : ℕ} (v : Fin n → E d) (r : Fin n → ℝ) (x : E d) :
    inner ℝ x (act (weightedMatrix v r) x) =
      ∑ i, (r i / ‖v i‖) * (inner ℝ x (v i)) ^ 2 := by
  have hlin : act (weightedMatrix v r) x =
      ∑ i, (r i / ‖v i‖) • act (rankOne (v i)) x := by
    unfold weightedMatrix
    simp [act, map_sum, map_smul]
  rw [hlin, inner_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [act_rankOne, real_inner_smul_right, real_inner_smul_right, real_inner_comm (v i) x]
  ring

lemma matrix_le_iff_quad {d : ℕ} {A B : Mat d} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A ≤ B ↔ ∀ x : E d, inner ℝ x (act A x) ≤ inner ℝ x (act B x) := by
  change (B - A).PosSemidef ↔ _
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h x
    have hnn := h.2 x.ofLp
    have hcalc : dotProduct (star x.ofLp) ((B - A).mulVec x.ofLp) =
        inner ℝ x (act B x) - inner ℝ x (act A x) := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
      congr 1 <;>
        simp [act, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    linarith
  · intro h
    refine ⟨hB.sub hA, fun x => ?_⟩
    let xE : E d := WithLp.toLp 2 x
    have hx := h xE
    have hcalc : dotProduct (star x) ((B - A).mulVec x) =
        inner ℝ xE (act B xE) - inner ℝ xE (act A xE) := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
      congr 1 <;>
        simp [xE, act, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct,
          dotProduct_comm]
    linarith

lemma q_pos (t : ℝ) : 0 < q t := by
  unfold q
  exact div_pos one_pos (lt_of_lt_of_le zero_lt_one (le_max_left 1 |t|))

lemma q_le_one (t : ℝ) : q t ≤ 1 := by
  unfold q
  have hpos : 0 < max 1 |t| := lt_of_lt_of_le zero_lt_one (le_max_left 1 |t|)
  exact (div_le_one hpos).mpr (le_max_left 1 |t|)

lemma lewis_le_one_step {d n : ℕ} {v : Fin n → E d} {r : Fin n → ℝ}
    (hle : lewis v ≤ (1 : Mat d))
    (hr : ∀ i, 0 < r i ∧ r i ≤ 1)
    (hS : (weightedMatrix v r).PosDef) :
    lewis (updatedGenerators v r) ≤ (1 : Mat d) := by
  have hquad_v : ∀ y : E d, ∑ i, ‖v i‖⁻¹ * (inner ℝ y (v i)) ^ 2 ≤ ‖y‖ ^ 2 := by
    intro y
    have hy := (matrix_le_iff_quad (lewis_isHermitian v) Matrix.isHermitian_one).mp hle y
    simpa [inner_lewis, act_one, real_inner_self_eq_norm_sq] using hy
  set S := weightedMatrix v r
  have hS_psd : (0 : Mat d) ≤ S := by
    change (S - 0).PosSemidef
    simpa using hS.posSemidef
  set R := CFC.sqrt S
  have hR_psd : (0 : Mat d) ≤ R := CFC.sqrt_nonneg S
  have hR_herm : R.IsHermitian := by simpa using hR_psd.isHermitian
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S
  have hR_det_ne : R.det ≠ 0 := by
    intro h0
    have : S.det = 0 := by rw [← hRR, Matrix.det_mul, h0, zero_mul]
    linarith [hS.det_pos]
  have hR_unit : IsUnit R.det := isUnit_iff_ne_zero.mpr hR_det_ne
  have hRRinv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR_unit
  have hRinv_herm : R⁻¹.IsHermitian := by
    change R⁻¹.conjTranspose = R⁻¹
    have hRT : R.transpose = R := hR_herm
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [Matrix.transpose_nonsing_inv, hRT]
  have hR_norm_le : ∀ y : E d, ‖act R y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    intro y
    calc
      ‖act R y‖ ^ 2 = inner ℝ (act R y) (act R y) := (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ y (act R (act R y)) := inner_act_symm hR_herm y (act R y)
      _ = inner ℝ y (act S y) := by rw [← act_mul, hRR]
      _ = ∑ i, (r i / ‖v i‖) * (inner ℝ y (v i)) ^ 2 := inner_weightedMatrix v r y
      _ ≤ ∑ i, ‖v i‖⁻¹ * (inner ℝ y (v i)) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          rw [div_eq_mul_inv]
          calc
            r i * ‖v i‖⁻¹ ≤ 1 * ‖v i‖⁻¹ :=
              mul_le_mul_of_nonneg_right (hr i).2 (inv_nonneg.mpr (norm_nonneg _))
            _ = ‖v i‖⁻¹ := one_mul _
      _ ≤ ‖y‖ ^ 2 := hquad_v y
  have hy_norm : ∀ i, ‖v i‖ ≤ ‖act R⁻¹ (v i)‖ := by
    intro i
    have h1 := hR_norm_le (act R⁻¹ (v i))
    rw [← act_mul, hRRinv, act_one] at h1
    nlinarith [norm_nonneg (v i), norm_nonneg (act R⁻¹ (v i))]
  rw [matrix_le_iff_quad (lewis_isHermitian _) Matrix.isHermitian_one]
  intro x
  rw [inner_lewis, act_one, real_inner_self_eq_norm_sq]
  calc
    ∑ i, ‖updatedGenerators v r i‖⁻¹ * (inner ℝ x (updatedGenerators v r i)) ^ 2
      ≤ ∑ i, (r i / ‖v i‖) * (inner ℝ (act R⁻¹ x) (v i)) ^ 2 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        by_cases hvi : v i = 0
        · simp [updatedGenerators, hvi, act]
        · set yi := act R⁻¹ (v i)
          have hvi_pos : 0 < ‖v i‖ := norm_pos_iff.mpr hvi
          have hyi_ge : ‖v i‖ ≤ ‖yi‖ := hy_norm i
          have hyi_pos : 0 < ‖yi‖ := lt_of_lt_of_le hvi_pos hyi_ge
          have hvplus_norm : ‖updatedGenerators v r i‖ = r i * ‖yi‖ := by
            unfold updatedGenerators
            change ‖r i • yi‖ = r i * ‖yi‖
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hr i).1]
          have hvplus_inner : inner ℝ x (updatedGenerators v r i) =
              r i * inner ℝ (act R⁻¹ x) (v i) := by
            unfold updatedGenerators
            change inner ℝ x (r i • act R⁻¹ (v i)) = r i * inner ℝ (act R⁻¹ x) (v i)
            rw [real_inner_smul_right, inner_act_symm hRinv_herm]
          rw [hvplus_norm, hvplus_inner]
          have hrew : (r i * ‖yi‖)⁻¹ * (r i * inner ℝ (act R⁻¹ x) (v i)) ^ 2 =
              (r i / ‖yi‖) * (inner ℝ (act R⁻¹ x) (v i)) ^ 2 := by
            have hri_ne : r i ≠ 0 := ne_of_gt (hr i).1
            have hyi_ne : ‖yi‖ ≠ 0 := ne_of_gt hyi_pos
            field_simp [hri_ne, hyi_ne]
          rw [hrew]
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact div_le_div_of_nonneg_left (le_of_lt (hr i).1) hvi_pos hyi_ge
    _ = inner ℝ (act R⁻¹ x) (act S (act R⁻¹ x)) := (inner_weightedMatrix v r (act R⁻¹ x)).symm
    _ = inner ℝ (act R⁻¹ x) (act R (act R (act R⁻¹ x))) := by rw [← act_mul R R, hRR]
    _ = inner ℝ (act R (act R⁻¹ x)) (act R (act R⁻¹ x)) :=
          (inner_act_symm hR_herm (act R⁻¹ x) _).symm
    _ = ‖x‖ ^ 2 := by
          rw [← act_mul R R⁻¹, hRRinv, act_one, real_inner_self_eq_norm_sq]

lemma support_le_sqrt_d_mul_norm {d n : ℕ} {v : Fin n → E d}
    (hle : lewis v ≤ (1 : Mat d)) (b : E d) :
    support v b ≤ Real.sqrt d * ‖b‖ := by
  have hquad : ∀ x : E d, ∑ i, ‖v i‖⁻¹ * (inner ℝ x (v i)) ^ 2 ≤ ‖x‖ ^ 2 := by
    intro x
    have hx := (matrix_le_iff_quad (lewis_isHermitian v) Matrix.isHermitian_one).mp hle x
    simpa [inner_lewis, act_one, real_inner_self_eq_norm_sq] using hx
  have hsum_norm : ∑ i, ‖v i‖ ≤ d := by
    have hcoord : ∀ k : Fin d, ∑ i, ‖v i‖⁻¹ * (v i k) ^ 2 ≤ 1 := by
      intro k
      let ek : E d := EuclideanSpace.single k 1
      have hek_norm : ‖ek‖ ^ 2 = 1 := by simp [ek]
      have hek_inner : ∀ i, inner ℝ ek (v i) = v i k := by
        intro i
        simp [ek, EuclideanSpace.inner_single_left]
      simpa [hek_norm, hek_inner] using hquad ek
    calc
      ∑ i, ‖v i‖ = ∑ i, ∑ k : Fin d, ‖v i‖⁻¹ * (v i k) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← Finset.mul_sum]
        have hsq : ∑ k : Fin d, (v i k) ^ 2 = ‖v i‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]
          simp [Real.norm_eq_abs, sq_abs]
        rw [hsq]
        by_cases h0 : ‖v i‖ = 0
        · simp [h0]
        · field_simp [h0]
      _ = ∑ k : Fin d, ∑ i, ‖v i‖⁻¹ * (v i k) ^ 2 := Finset.sum_comm
      _ ≤ ∑ _k : Fin d, (1 : ℝ) := Finset.sum_le_sum (fun k _ => hcoord k)
      _ = d := by simp
  let f : Fin n → ℝ := fun i => Real.sqrt (‖v i‖⁻¹) * |inner ℝ b (v i)|
  let g : Fin n → ℝ := fun i => Real.sqrt ‖v i‖
  have hfg : ∀ i, f i * g i = |inner ℝ b (v i)| := by
    intro i
    dsimp [f, g]
    by_cases hvi : v i = 0
    · simp [hvi]
    · have hpos : 0 < ‖v i‖ := norm_pos_iff.mpr hvi
      have hmul : Real.sqrt (‖v i‖⁻¹) * Real.sqrt ‖v i‖ = 1 := by
        rw [← Real.sqrt_mul (inv_nonneg.mpr (le_of_lt hpos)), inv_mul_cancel₀ (ne_of_gt hpos),
          Real.sqrt_one]
      calc
        Real.sqrt (‖v i‖⁻¹) * |inner ℝ b (v i)| * Real.sqrt ‖v i‖
          = (Real.sqrt (‖v i‖⁻¹) * Real.sqrt ‖v i‖) * |inner ℝ b (v i)| := by ring
        _ = |inner ℝ b (v i)| := by rw [hmul, one_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hfsq : ∑ i, f i ^ 2 = ∑ i, ‖v i‖⁻¹ * (inner ℝ b (v i)) ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr (norm_nonneg _)), sq_abs]
  have hgsq : ∑ i, g i ^ 2 = ∑ i, ‖v i‖ := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    dsimp [g]
    exact Real.sq_sqrt (norm_nonneg _)
  have hsupp_sq : (support v b) ^ 2 ≤ (Real.sqrt d * ‖b‖) ^ 2 := by
    rw [support_eq_sum_abs]
    calc
      (∑ i, |inner ℝ b (v i)|) ^ 2
        = (∑ i, f i * g i) ^ 2 := by simp only [hfg]
      _ ≤ (∑ i, f i ^ 2) * (∑ i, g i ^ 2) := hcs
      _ = (∑ i, ‖v i‖⁻¹ * (inner ℝ b (v i)) ^ 2) * (∑ i, ‖v i‖) := by rw [hfsq, hgsq]
      _ ≤ ‖b‖ ^ 2 * d := mul_le_mul (hquad b) hsum_norm
          (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (sq_nonneg _)
      _ = (Real.sqrt d * ‖b‖) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d), mul_comm]
  have hrhs_nn : 0 ≤ Real.sqrt d * ‖b‖ := by positivity
  nlinarith [support_eq_sum_abs v b]

end Lemma23Aux

theorem solution (d n : ℕ) (hd : 3 ≤ d) (C : ℝ) (hC : 64 ≤ C)
    (w : Fin n → E d) (T : Mat d) (hT : ApproxLewis w T) (z : Tape d) :
    (∀ j ≤ rounds d,
      lewis (runState C w T z j).v ≤ (1 : Mat d) ∧
      ∀ b : E d, support (runState C w T z j).v b ≤ Real.sqrt d * ‖b‖) ∧
    (∀ b : E d, ‖b‖ / 4 ≤ support (runState C w T z 0).v b) := by
  obtain ⟨_, _, hstep_feas⟩ := feasibility d n hd C hC w T hT z
  have hlewis : ∀ j ≤ rounds d, lewis (runState C w T z j).v ≤ (1 : Mat d) := by
    intro j hj
    induction j with
    | zero =>
        simpa [runState] using hT.2.2
    | succ j ih =>
        have hj_lt : j < rounds d := Nat.lt_of_succ_le hj
        have hle_j := ih (Nat.le_of_lt hj_lt)
        have hstep : runState C w T z (j + 1) =
            step C (scale d j) (runState C w T z j) (z ⟨j, hj_lt⟩) := by
          simp [runState, hj_lt]
        rw [hstep]
        dsimp [step]
        have hposDef := (hstep_feas ⟨j, hj_lt⟩).1
        exact Lemma23Aux.lewis_le_one_step hle_j
          (fun _ => ⟨Lemma23Aux.q_pos _, Lemma23Aux.q_le_one _⟩) hposDef
  refine ⟨fun j hj => ⟨hlewis j hj, Lemma23Aux.support_le_sqrt_d_mul_norm (hlewis j hj)⟩, ?_⟩
  intro b
  by_cases hb : b = 0
  · subst hb
    simp [Lemma23Aux.support_eq_sum_abs]
  · have hb_pos : 0 < ‖b‖ := norm_pos_iff.mpr hb
    let u : E d := ‖b‖⁻¹ • b
    have hu_norm : ‖u‖ = 1 := by
      simp [u, norm_smul, inv_mul_cancel₀ (ne_of_gt hb_pos)]
    set v₀ := (runState C w T z 0).v
    have hlow_mat : ((1 / 4 : ℝ) • (1 : Mat d)).IsHermitian := by
      ext k l
      simp [Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
    have hlow := (Lemma23Aux.matrix_le_iff_quad hlow_mat (Lemma23Aux.lewis_isHermitian v₀)).mp
      (by simpa [v₀, runState] using hT.2.1) u
    have hlhs : inner ℝ u (act ((1 / 4 : ℝ) • (1 : Mat d)) u) = 1 / 4 := by
      have : act ((1 / 4 : ℝ) • (1 : Mat d)) u = (1 / 4 : ℝ) • u := by
        simp [act, map_smul]
      rw [this, real_inner_smul_right, real_inner_self_eq_norm_sq, hu_norm]
      ring
    rw [hlhs, Lemma23Aux.inner_lewis] at hlow
    have hle_supp : ∑ i, ‖v₀ i‖⁻¹ * (inner ℝ u (v₀ i)) ^ 2 ≤ ‖b‖⁻¹ * support v₀ b := by
      rw [Lemma23Aux.support_eq_sum_abs, Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have hcs_i : |inner ℝ u (v₀ i)| ≤ ‖v₀ i‖ := by
        calc
          |inner ℝ u (v₀ i)| ≤ ‖u‖ * ‖v₀ i‖ := abs_real_inner_le_norm u (v₀ i)
          _ = ‖v₀ i‖ := by rw [hu_norm, one_mul]
      have hterm : ‖v₀ i‖⁻¹ * (inner ℝ u (v₀ i)) ^ 2 ≤ |inner ℝ u (v₀ i)| := by
        by_cases hv0 : v₀ i = 0
        · simp [hv0]
        · have hv_pos : 0 < ‖v₀ i‖ := norm_pos_iff.mpr hv0
          rw [← sq_abs (inner ℝ u (v₀ i)), sq]
          calc
            ‖v₀ i‖⁻¹ * (|inner ℝ u (v₀ i)| * |inner ℝ u (v₀ i)|)
              = (|inner ℝ u (v₀ i)| / ‖v₀ i‖) * |inner ℝ u (v₀ i)| := by ring
            _ ≤ 1 * |inner ℝ u (v₀ i)| := by
                apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                exact (div_le_one hv_pos).mpr hcs_i
            _ = |inner ℝ u (v₀ i)| := one_mul _
      have hu_inner : |inner ℝ u (v₀ i)| = ‖b‖⁻¹ * |inner ℝ b (v₀ i)| := by
        simp [u, real_inner_smul_left, abs_mul, abs_of_pos (inv_pos.mpr hb_pos)]
      exact le_trans hterm (le_of_eq hu_inner)
    have hquarter : (1 / 4 : ℝ) ≤ ‖b‖⁻¹ * support v₀ b := le_trans hlow hle_supp
    have hmul := mul_le_mul_of_nonneg_left hquarter (le_of_lt hb_pos)
    calc
      ‖b‖ / 4 = ‖b‖ * (1 / 4) := by ring
      _ ≤ ‖b‖ * (‖b‖⁻¹ * support v₀ b) := hmul
      _ = support v₀ b := by field_simp [ne_of_gt hb_pos]
