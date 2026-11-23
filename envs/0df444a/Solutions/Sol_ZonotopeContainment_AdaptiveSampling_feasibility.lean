-- Prove2me | solution 1 for ZonotopeContainment.AdaptiveSampling.feasibility
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:03:19.958858+00:00
-- url     : https://prove2.me/submissions/b13d85fb-42ce-4730-974b-7f02a7a86759

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Algorithm

open scoped BigOperators
open scoped MatrixOrder
open ZonotopeContainment.AdaptiveSampling

namespace FeasAux

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

lemma act_rankOne {d : ℕ} (u x : E d) :
    act (rankOne u) x = (inner ℝ u x) • u := by
  ext k
  simp [act, rankOne, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct, mul_assoc, Finset.mul_sum, mul_comm]

lemma weightedMatrix_isHermitian {d n : ℕ} (v : Fin n → E d) (r : Fin n → ℝ) :
    (weightedMatrix v r).IsHermitian := by
  unfold weightedMatrix
  ext k l
  simp [Matrix.sum_apply, rankOne, Matrix.conjTranspose_apply, mul_comm]

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

lemma span_eq_top_of_forall_orth {d n : ℕ} (v : Fin n → E d)
    (h : ∀ x : E d, (∀ i, inner ℝ x (v i) = 0) → x = 0) :
    Submodule.span ℝ (Set.range v) = ⊤ := by
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro x hx
  apply h x
  intro i
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self i)) hx

lemma forall_orth_of_span_eq_top {d n : ℕ} {v : Fin n → E d}
    (hv : Submodule.span ℝ (Set.range v) = ⊤) {x : E d}
    (hx : ∀ i, inner ℝ x (v i) = 0) : x = 0 := by
  have horth : ∀ y ∈ Submodule.span ℝ (Set.range v), inner ℝ x y = 0 := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, rfl⟩
      exact hx i
    · simp
    · intro a b _ _ ha hb
      rw [inner_add_right, ha, hb, add_zero]
    · intro c a _ ha
      rw [real_inner_smul_right, ha, mul_zero]
  exact inner_self_eq_zero.mp (horth x (hv ▸ Submodule.mem_top))

lemma weightedMatrix_posDef {d n : ℕ} (v : Fin n → E d)
    (hv : Submodule.span ℝ (Set.range v) = ⊤) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    (weightedMatrix v r).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨weightedMatrix_isHermitian v r, ?_⟩
  intro x hx
  let xE : E d := WithLp.toLp 2 x
  have hxE_ne : xE ≠ 0 := by
    intro h0
    apply hx
    ext k
    exact congrArg (fun y : E d => y.ofLp k) h0
  have hdot : dotProduct (star x) ((weightedMatrix v r).mulVec x) =
      inner ℝ xE (act (weightedMatrix v r) xE) := by
    simp [xE, act, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [hdot, inner_weightedMatrix]
  have hex : ∃ i, inner ℝ xE (v i) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hxE_ne (forall_orth_of_span_eq_top hv hall)
  obtain ⟨i₀, hi₀⟩ := hex
  have hvi₀_ne : v i₀ ≠ 0 := by
    intro hv0
    apply hi₀
    simp [hv0]
  have hvi₀_norm : 0 < ‖v i₀‖ := norm_pos_iff.mpr hvi₀_ne
  have hterm_pos : 0 < (r i₀ / ‖v i₀‖) * (inner ℝ xE (v i₀)) ^ 2 :=
    mul_pos (div_pos (hr i₀) hvi₀_norm) (sq_pos_of_ne_zero hi₀)
  exact Finset.sum_pos'
    (fun i _ => mul_nonneg (div_nonneg (le_of_lt (hr i)) (norm_nonneg _)) (sq_nonneg _))
    ⟨i₀, Finset.mem_univ i₀, hterm_pos⟩

lemma q_pos (t : ℝ) : 0 < q t := by
  unfold q
  have : 0 < max 1 |t| := lt_of_lt_of_le zero_lt_one (le_max_left 1 |t|)
  exact div_pos one_pos this

lemma q_le_one (t : ℝ) : q t ≤ 1 := by
  unfold q
  have hpos : 0 < max 1 |t| := lt_of_lt_of_le zero_lt_one (le_max_left 1 |t|)
  exact (div_le_one hpos).mpr (le_max_left 1 |t|)

lemma abs_mul_q_le_one (t : ℝ) : |t * q t| ≤ 1 := by
  unfold q
  have hpos : 0 < max 1 |t| := lt_of_lt_of_le zero_lt_one (le_max_left 1 |t|)
  rw [abs_mul, abs_div, abs_one, abs_of_pos hpos, mul_one_div]
  exact (div_le_one hpos).mpr (le_max_right 1 |t|)

lemma image_zonotope_subset {d n : ℕ} (A : Mat d) (v w : Fin n → E d)
    (hθ : ∀ i, ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ act A (v i) = θ • w i) :
    (act A) '' zonotope v ⊆ zonotope w := by
  rintro _ ⟨x, ⟨t, ht, rfl⟩, rfl⟩
  choose θ hθ_pos hθ_le hθ_eq using hθ
  refine ⟨fun i => t i * θ i, ?_, ?_⟩
  · intro i
    rw [abs_mul, abs_of_pos (hθ_pos i)]
    calc
      |t i| * θ i ≤ 1 * 1 := mul_le_mul (ht i) (hθ_le i) (le_of_lt (hθ_pos i)) zero_le_one
      _ = 1 := mul_one 1
  · simp only [act, map_sum, map_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    change t i • act A (v i) = (t i * θ i) • w i
    rw [hθ_eq i, smul_smul]

lemma init_span {d n : ℕ} {w : Fin n → E d} {T : Mat d} (hT : ApproxLewis w T) :
    Submodule.span ℝ (Set.range (fun i => act T (w i))) = ⊤ := by
  set v₀ : Fin n → E d := fun i => act T (w i)
  apply span_eq_top_of_forall_orth
  intro x hx
  have hpsd : (lewis v₀ - (1 / 4 : ℝ) • (1 : Mat d)).PosSemidef := hT.2.1
  have hnn : 0 ≤ dotProduct (star x.ofLp) ((lewis v₀ - (1 / 4 : ℝ) • (1 : Mat d)).mulVec x.ofLp) :=
    (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 x.ofLp
  have hlewis_zero : act (lewis v₀) x = 0 := by
    have hlin : act (lewis v₀) x = ∑ i, (‖v₀ i‖⁻¹ : ℝ) • act (rankOne (v₀ i)) x := by
      unfold lewis
      simp [act, map_sum, map_smul]
    rw [hlin]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [act_rankOne, real_inner_comm x (v₀ i), hx i, zero_smul ℝ (v₀ i), smul_zero]
  have hcalc : dotProduct (star x.ofLp) ((lewis v₀ - (1 / 4 : ℝ) • (1 : Mat d)).mulVec x.ofLp) =
      inner ℝ x (act (lewis v₀) x) - (1 / 4 : ℝ) * ‖x‖ ^ 2 := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
    congr 1
    · simp [act, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    · calc
        dotProduct (star x.ofLp) (((1 / 4 : ℝ) • (1 : Mat d)).mulVec x.ofLp)
          = (1 / 4 : ℝ) * dotProduct (star x.ofLp) x.ofLp := by
              simp [Matrix.smul_mulVec, dotProduct_smul]
        _ = (1 / 4 : ℝ) * inner ℝ x x := by
              rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
        _ = (1 / 4 : ℝ) * ‖x‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
  rw [hcalc, hlewis_zero, inner_zero_right] at hnn
  have hnorm_sq : ‖x‖ ^ 2 ≤ 0 := by linarith
  have hnorm0 : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp hnorm0

end FeasAux

theorem solution (d n : ℕ) (_hd : 3 ≤ d) (C : ℝ) (_hC : 64 ≤ C)
    (w : Fin n → E d) (T : Mat d) (hT : ApproxLewis w T) (z : Tape d) :
    (∀ i, act (runState C w T z 0).A ((runState C w T z 0).v i) = w i) ∧
    (∀ j ≤ rounds d,
      Submodule.span ℝ (Set.range (runState C w T z j).v) = ⊤ ∧
      (∀ i, ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
        act (runState C w T z j).A ((runState C w T z j).v i) = θ • w i) ∧
      (act (runState C w T z j).A) '' zonotope (runState C w T z j).v ⊆ zonotope w) ∧
    (∀ j : Fin (rounds d),
      (weightedMatrix (runState C w T z j).v
        (weights C (scale d j) (runState C w T z j).v (z j))).PosDef ∧
      localPoint C (scale d j) (runState C w T z j).v (z j) ∈
        zonotope (runState C w T z j).v ∧
      (∀ i, act (runState C w T z (j + 1)).A ((runState C w T z (j + 1)).v i) =
        weights C (scale d j) (runState C w T z j).v (z j) i •
          act (runState C w T z j).A ((runState C w T z j).v i)) ∧
      recorded C w T z j ∈ zonotope w) := by
  have hT_det : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT.1
  have h0 : ∀ i, act (runState C w T z 0).A ((runState C w T z 0).v i) = w i := by
    intro i
    simp only [runState]
    rw [← FeasAux.act_mul, Matrix.nonsing_inv_mul T hT_det, FeasAux.act_one]
  have hinv : ∀ j ≤ rounds d,
      Submodule.span ℝ (Set.range (runState C w T z j).v) = ⊤ ∧
      (∀ i, ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
        act (runState C w T z j).A ((runState C w T z j).v i) = θ • w i) := by
    intro j hj
    induction j with
    | zero =>
        refine ⟨?_, ?_⟩
        · simpa [runState] using FeasAux.init_span hT
        · intro i
          exact ⟨1, zero_lt_one, le_rfl, by simpa using h0 i⟩
    | succ j ih =>
        have hj_lt : j < rounds d := Nat.lt_of_succ_le hj
        obtain ⟨hspan_j, hθ_j⟩ := ih (Nat.le_of_lt hj_lt)
        have hstep : runState C w T z (j + 1) =
            step C (scale d j) (runState C w T z j) (z ⟨j, hj_lt⟩) := by
          simp [runState, hj_lt]
        set sj := runState C w T z j
        set rj := weights C (scale d j) sj.v (z ⟨j, hj_lt⟩)
        have hrj_pos : ∀ i, 0 < rj i := fun i => FeasAux.q_pos _
        have hrj_le : ∀ i, rj i ≤ 1 := fun i => FeasAux.q_le_one _
        set Sj := weightedMatrix sj.v rj
        have hSj_posDef : Sj.PosDef := FeasAux.weightedMatrix_posDef sj.v hspan_j rj hrj_pos
        have hSj_psd : (0 : Mat d) ≤ Sj := by
          change (Sj - 0).PosSemidef
          simpa using hSj_posDef.posSemidef
        set Rj := CFC.sqrt Sj
        have hRRj : Rj * Rj = Sj := CFC.sqrt_mul_sqrt_self Sj
        have hSj_det : 0 < Sj.det := hSj_posDef.det_pos
        have hRj_det_ne : Rj.det ≠ 0 := by
          intro h0det
          have : Sj.det = 0 := by rw [← hRRj, Matrix.det_mul, h0det, zero_mul]
          linarith
        have hRj_unit : IsUnit Rj.det := isUnit_iff_ne_zero.mpr hRj_det_ne
        have hRRinv : Rj * Rj⁻¹ = 1 := Matrix.mul_nonsing_inv Rj hRj_unit
        have hRinvR : Rj⁻¹ * Rj = 1 := Matrix.nonsing_inv_mul Rj hRj_unit
        have hupd_i : ∀ i, act (sj.A * Rj) (updatedGenerators sj.v rj i) =
            rj i • act sj.A (sj.v i) := by
          intro i
          unfold updatedGenerators
          change act (sj.A * Rj) (rj i • act Rj⁻¹ (sj.v i)) = rj i • act sj.A (sj.v i)
          rw [act, map_smul]
          change rj i • act (sj.A * Rj) (act Rj⁻¹ (sj.v i)) = rj i • act sj.A (sj.v i)
          rw [FeasAux.act_mul sj.A Rj, ← FeasAux.act_mul Rj Rj⁻¹, hRRinv, FeasAux.act_one]
        rw [hstep]
        dsimp [step]
        refine ⟨?_, ?_⟩
        · apply FeasAux.span_eq_top_of_forall_orth
          intro x hx
          have horth_j : ∀ i, inner ℝ (act Rj⁻¹.transpose x) (sj.v i) = 0 := by
            intro i
            have hi := hx i
            unfold updatedGenerators at hi
            change inner ℝ x (rj i • act Rj⁻¹ (sj.v i)) = 0 at hi
            rw [real_inner_smul_right, FeasAux.inner_act_transpose] at hi
            exact (mul_eq_zero.mp hi).resolve_left (ne_of_gt (hrj_pos i))
          have hzero : act Rj⁻¹.transpose x = 0 :=
            FeasAux.forall_orth_of_span_eq_top hspan_j horth_j
          have h1 : act Rj.transpose (act Rj⁻¹.transpose x) = 0 := by
            rw [hzero]; simp [act]
          rw [← FeasAux.act_mul, ← Matrix.transpose_mul, hRinvR, Matrix.transpose_one,
            FeasAux.act_one] at h1
          exact h1
        · intro i
          obtain ⟨θ, hθ_pos, hθ_le, hθ_eq⟩ := hθ_j i
          refine ⟨rj i * θ, mul_pos (hrj_pos i) hθ_pos, ?_, ?_⟩
          · calc
              rj i * θ ≤ 1 * 1 := mul_le_mul (hrj_le i) hθ_le (le_of_lt hθ_pos) zero_le_one
              _ = 1 := mul_one 1
          · rw [hupd_i i, hθ_eq, smul_smul]
  refine ⟨h0, ?_, ?_⟩
  · intro j hj
    obtain ⟨hspan_j, hθ_j⟩ := hinv j hj
    exact ⟨hspan_j, hθ_j, FeasAux.image_zonotope_subset _ _ _ hθ_j⟩
  · intro j
    obtain ⟨hspan_j, hθ_j⟩ := hinv j.1 (Nat.le_of_lt j.2)
    have hsub_j := FeasAux.image_zonotope_subset _ _ _ hθ_j
    set sj := runState C w T z j
    set rj := weights C (scale d j) sj.v (z j)
    have hrj_pos : ∀ i, 0 < rj i := fun i => FeasAux.q_pos _
    have hSj_posDef : (weightedMatrix sj.v rj).PosDef :=
      FeasAux.weightedMatrix_posDef sj.v hspan_j rj hrj_pos
    have hSj_psd : (0 : Mat d) ≤ weightedMatrix sj.v rj := by
      change (weightedMatrix sj.v rj - 0).PosSemidef
      simpa using hSj_posDef.posSemidef
    have hloc : localPoint C (scale d j) sj.v (z j) ∈ zonotope sj.v := by
      refine ⟨fun i => projections C (scale d j) sj.v (z j) i * rj i, ?_, rfl⟩
      intro i
      exact FeasAux.abs_mul_q_le_one _
    have hrec : recorded C w T z j ∈ zonotope w :=
      hsub_j ⟨localPoint C (scale d j) sj.v (z j), hloc, rfl⟩
    refine ⟨hSj_posDef, hloc, ?_, hrec⟩
    intro i
    have hstep : runState C w T z (j.1 + 1) = step C (scale d j) sj (z j) := by
      simp [runState, j.2, sj]
    rw [hstep]
    dsimp [step]
    set Rj := CFC.sqrt (weightedMatrix sj.v rj)
    have hRRj : Rj * Rj = weightedMatrix sj.v rj := CFC.sqrt_mul_sqrt_self _
    have hSj_det : 0 < (weightedMatrix sj.v rj).det := hSj_posDef.det_pos
    have hRj_det_ne : Rj.det ≠ 0 := by
      intro h0det
      have : (weightedMatrix sj.v rj).det = 0 := by
        rw [← hRRj, Matrix.det_mul, h0det, zero_mul]
      linarith
    have hRRinv : Rj * Rj⁻¹ = 1 :=
      Matrix.mul_nonsing_inv Rj (isUnit_iff_ne_zero.mpr hRj_det_ne)
    unfold updatedGenerators
    change act (sj.A * Rj) (rj i • act Rj⁻¹ (sj.v i)) = rj i • act sj.A (sj.v i)
    rw [act, map_smul]
    change rj i • act (sj.A * Rj) (act Rj⁻¹ (sj.v i)) = rj i • act sj.A (sj.v i)
    rw [FeasAux.act_mul sj.A Rj, ← FeasAux.act_mul Rj Rj⁻¹, hRRinv, FeasAux.act_one]
