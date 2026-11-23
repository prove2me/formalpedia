-- Prove2me | solution 1 for ZonotopeContainment.AdaptiveSampling.update_identities
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:55:57.374979+00:00
-- url     : https://prove2.me/submissions/804dda97-69ba-4d57-b8c3-79fd9c021864

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Algorithm

open scoped BigOperators
open scoped MatrixOrder
open ZonotopeContainment.AdaptiveSampling

namespace UpdateIdAux

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
      intro i
      dsimp [t]
      split_ifs <;> simp
    have hx_mem : (∑ i, t i • v i) ∈ zonotope v := ⟨t, ht, rfl⟩
    have hx_val : inner ℝ b (∑ i, t i • v i) = ∑ i, |inner ℝ b (v i)| := by
      rw [inner_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [real_inner_smul_right]
      dsimp [t]
      split_ifs with h
      · simp [abs_of_nonneg h]
      · have hlt : inner ℝ b (v i) < 0 := not_le.mp h
        simp [abs_of_neg hlt]
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
    have horth : ∀ y ∈ Submodule.span ℝ (Set.range v), inner ℝ xE y = 0 := by
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨i, rfl⟩
        exact hall i
      · simp
      · intro a b _ _ ha hb
        rw [inner_add_right, ha, hb, add_zero]
      · intro c a _ ha
        rw [real_inner_smul_right, ha, mul_zero]
    have hself : inner ℝ xE xE = 0 := horth xE (hv ▸ Submodule.mem_top)
    exact hxE_ne (inner_self_eq_zero.mp hself)
  obtain ⟨i₀, hi₀⟩ := hex
  have hvi₀_ne : v i₀ ≠ 0 := by
    intro hv0
    apply hi₀
    simp [hv0]
  have hvi₀_norm : 0 < ‖v i₀‖ := norm_pos_iff.mpr hvi₀_ne
  have hterm_pos : 0 < (r i₀ / ‖v i₀‖) * (inner ℝ xE (v i₀)) ^ 2 := by
    have h1 : 0 < r i₀ / ‖v i₀‖ := div_pos (hr i₀) hvi₀_norm
    have h2 : 0 < (inner ℝ xE (v i₀)) ^ 2 := sq_pos_of_ne_zero hi₀
    exact mul_pos h1 h2
  exact Finset.sum_pos'
    (fun i _ => mul_nonneg (div_nonneg (le_of_lt (hr i)) (norm_nonneg _)) (sq_nonneg _))
    ⟨i₀, Finset.mem_univ i₀, hterm_pos⟩

end UpdateIdAux

theorem solution (d n : ℕ) (v : Fin n → E d)
    (hv : Submodule.span ℝ (Set.range v) = ⊤) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i ∧ r i ≤ 1) (b : E d) :
    ‖act (CFC.sqrt (weightedMatrix v r)) b‖ ^ 2 =
      inner ℝ b (act (weightedMatrix v r) b) ∧
    support v b - support (updatedGenerators v r)
      (act (CFC.sqrt (weightedMatrix v r)) b) =
      ∑ i, (1 - r i) * |inner ℝ b (v i)| := by
  set S : Mat d := weightedMatrix v r
  have hS_posDef : S.PosDef := UpdateIdAux.weightedMatrix_posDef v hv r (fun i => (hr i).1)
  have hS_psd : (0 : Mat d) ≤ S := by
    change (S - 0).PosSemidef
    simpa using hS_posDef.posSemidef
  set R : Mat d := CFC.sqrt S
  have hR_psd : (0 : Mat d) ≤ R := CFC.sqrt_nonneg S
  have hR_herm : R.IsHermitian := by simpa using hR_psd.isHermitian
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S
  have hnorm : ‖act R b‖ ^ 2 = inner ℝ b (act S b) := by
    calc
      ‖act R b‖ ^ 2 = inner ℝ (act R b) (act R b) := (real_inner_self_eq_norm_sq (act R b)).symm
      _ = inner ℝ b (act R (act R b)) := UpdateIdAux.inner_act_symm hR_herm b (act R b)
      _ = inner ℝ b (act (R * R) b) := by rw [← UpdateIdAux.act_mul]
      _ = inner ℝ b (act S b) := by rw [hRR]
  refine ⟨hnorm, ?_⟩
  have hS_det_pos : 0 < S.det := hS_posDef.det_pos
  have hR_det_ne : R.det ≠ 0 := by
    intro h0
    have : S.det = 0 := by
      rw [← hRR, Matrix.det_mul, h0, zero_mul]
    linarith
  have hR_isUnit_det : IsUnit R.det := isUnit_iff_ne_zero.mpr hR_det_ne
  have hRRinv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR_isUnit_det
  rw [UpdateIdAux.support_eq_sum_abs v b,
    UpdateIdAux.support_eq_sum_abs (updatedGenerators v r) (act R b),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hinner : inner ℝ (act R b) (updatedGenerators v r i) = r i * inner ℝ b (v i) := by
    unfold updatedGenerators
    change inner ℝ (act R b) (r i • act R⁻¹ (v i)) = r i * inner ℝ b (v i)
    rw [real_inner_smul_right, UpdateIdAux.inner_act_symm hR_herm b (act R⁻¹ (v i)),
      ← UpdateIdAux.act_mul, hRRinv, UpdateIdAux.act_one]
  rw [hinner, abs_mul, abs_of_pos (hr i).1]
  ring
