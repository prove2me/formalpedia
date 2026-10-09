-- Prove2me | solution 1 for PathFindingLP.WeightFunction.properties_of_weight_function
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T02:04:54.953558+00:00
-- url     : https://prove2.me/submissions/aaf21aa4-4989-49cc-9cd2-bdbc210c8a41
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PathFindingLP_WeightFunction_RegularizedObjective
import Definitions.Def_PathFindingLP_WeightFunction_IsWeightFunction
import Theorems.Thm_PathFindingLP_WeightFunction_step_consistency
import Theorems.Thm_PathFindingLP_WeightFunction_slack_sensitivity_bound

set_option autoImplicit false

open Matrix

lemma pfw_mulVec_injective {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) :
    Function.Injective A.mulVec := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fin_fun] at h
  have hk : Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 0 := by
    unfold Matrix.rank at hA; omega
  have hb : LinearMap.ker A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hk
  have := LinearMap.ker_eq_bot.mp hb
  exact fun x y h => this h

lemma pfw_posDef {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n)
    (s d : Fin m → ℝ) (hs : ∀ i, 0 < s i) (hd : ∀ i, 0 < d i) :
    ((diagonal (fun i => (s i)⁻¹) * A)ᵀ * diagonal d *
      (diagonal (fun i => (s i)⁻¹) * A)).PosDef := by
  have hinj : Function.Injective (diagonal (fun i => (s i)⁻¹) * A).mulVec := by
    intro x y hxy
    apply pfw_mulVec_injective A hA
    have h2 : (diagonal (fun i => (s i)⁻¹) * A) *ᵥ x = (diagonal (fun i => (s i)⁻¹) * A) *ᵥ y :=
      hxy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h2
    funext i
    have := congrFun h2 i
    simp only [mulVec_diagonal] at this
    have hne : (s i)⁻¹ ≠ 0 := inv_ne_zero (hs i).ne'
    exact mul_left_cancel₀ hne this
  have hD : (diagonal d).PosDef := Matrix.posDef_diagonal_iff.mpr hd
  have := hD.conjTranspose_mul_mul_same hinj
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this

lemma pfw_psd {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (Bᵀ * diagonal d * B).PosSemidef := by
  have hD : (diagonal d).PosSemidef := Matrix.PosSemidef.diagonal (fun i => hd i)
  have := hD.conjTranspose_mul_mul_same B
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this

lemma pfw_rank_one {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin m → ℝ) (i : Fin m)
    (c : ℝ) :
    Bᵀ * diagonal (Function.update d i (d i + c)) * B =
      Bᵀ * diagonal d * B + replicateCol Unit (c • (fun k => B i k)) *
        replicateRow Unit (fun k => B i k) := by
  ext k l
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, diagonal_apply,
    replicateCol_apply, replicateRow_apply, Pi.smul_apply, smul_eq_mul]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.univ_unique, Finset.sum_singleton]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  rw [Function.update_self]
  have : ∑ x ∈ Finset.univ.erase i, B x k * Function.update d i (d i + c) x * B x l
      = ∑ x ∈ Finset.univ.erase i, B x k * d x * B x l := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this]
  ring

lemma pfw_det_affine {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin m → ℝ) (i : Fin m)
    (hM : IsUnit (Bᵀ * diagonal d * B).det) :
    ∃ q : ℝ, ∀ c : ℝ, (Bᵀ * diagonal (Function.update d i (d i + c)) * B).det =
      (Bᵀ * diagonal d * B).det * (1 + c * q) := by
  refine ⟨(replicateRow Unit (fun k => B i k) * (Bᵀ * diagonal d * B)⁻¹ *
      replicateCol Unit (fun k => B i k)) () (), fun c => ?_⟩
  rw [pfw_rank_one, det_add_replicateCol_mul_replicateRow hM]
  congr 1
  rw [Matrix.det_unique]
  have : replicateCol Unit (c • (fun k => B i k)) = c • replicateCol Unit (fun k => B i k) := by
    ext; simp
  rw [this, Matrix.mul_smul]
  simp

/-- Scaling one weight by `t ∈ [0,1]` shrinks the determinant by at most the factor `t`. -/
lemma pfw_det_scale {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin m → ℝ)
    (hd : ∀ j, 0 ≤ d j) (i : Fin m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (Bᵀ * diagonal d * B).det ≤ (Bᵀ * diagonal (Function.update d i (t * d i)) * B).det := by
  have hd' : ∀ j, 0 ≤ Function.update d i (t * d i) j := by
    intro j
    by_cases h : j = i
    · subst h; simp only [Function.update_self]; exact mul_nonneg ht0 (hd j)
    · rw [Function.update_of_ne h]; exact hd j
  have hR := (pfw_psd B _ hd').det_nonneg
  have hM := (pfw_psd B d hd).det_nonneg
  rcases hM.lt_or_eq with hpos | hzero
  · obtain ⟨q, hq⟩ := pfw_det_affine B d i (isUnit_iff_ne_zero.mpr hpos.ne')
    have h0 := hq (-d i)
    have hupd0 : Function.update d i (d i + -d i) = Function.update d i (0 * d i) := by
      congr 1; ring
    have hz : ∀ j, 0 ≤ Function.update d i (0 * d i) j := by
      intro j
      by_cases h : j = i
      · subst h; simp
      · rw [Function.update_of_ne h]; exact hd j
    have hR0 := (pfw_psd B _ hz).det_nonneg
    rw [hupd0] at h0
    rw [h0] at hR0
    have h1 : 0 ≤ 1 + -d i * q := by
      by_contra hneg
      push Not at hneg
      nlinarith
    have ht := hq ((t - 1) * d i)
    have hupd : Function.update d i (d i + (t - 1) * d i) = Function.update d i (t * d i) := by
      congr 1; ring
    rw [hupd] at ht
    rw [ht]
    nlinarith [hd i]
  · rw [← hzero, mul_zero]; exact hR

lemma pfw_sum_update {m : ℕ} (f : Fin m → ℝ) (i : Fin m) (x : ℝ) :
    ∑ j, Function.update f i x j = ∑ j, f j - f i + x := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    Finset.sdiff_singleton_eq_erase]
  ring

open PathFindingLP.WeightFunction in
/-- Uniformity: every coordinate of a minimizer is at most `2`. -/
lemma pfw_le_two {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) (α β : ℝ)
    (hα0 : 0 < α) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2) (s w : Fin m → ℝ) (hs : ∀ i, 0 < s i)
    (hw : IsRegularizedMinimizer A α β s w) (i : Fin m) : w i ≤ 2 := by
  obtain ⟨hwpos, hmin⟩ := hw
  set B := diagonal (fun i => (s i)⁻¹) * A with hB
  have ht : (0 : ℝ) < 3 / 4 := by norm_num
  set w' := Function.update w i ((3 / 4) * w i) with hw'
  have hw'pos : ∀ j, 0 < w' j := by
    intro j
    by_cases h : j = i
    · subst h; simp only [w', Function.update_self]; exact mul_pos ht (hwpos j)
    · simp only [w', Function.update_of_ne h]; exact hwpos j
  have key := hmin w' hw'pos
  unfold fhat at key
  rw [← hB] at key
  have hdiag : (fun j => w' j ^ α)
      = Function.update (fun j => w j ^ α) i ((3 / 4 : ℝ) ^ α * (fun j => w j ^ α) i) := by
    funext j
    by_cases h : j = i
    · subst h; simp only [w', Function.update_self]; exact Real.mul_rpow ht.le (hwpos j).le
    · simp only [w', Function.update_of_ne h]
  rw [hdiag] at key
  have htα0 : (0 : ℝ) < (3 / 4 : ℝ) ^ α := Real.rpow_pos_of_pos ht _
  have htα1 : (3 / 4 : ℝ) ^ α ≤ 1 := Real.rpow_le_one ht.le (by norm_num) hα0.le
  have hdet := pfw_det_scale B (fun j => w j ^ α) (fun j => (Real.rpow_pos_of_pos (hwpos j) _).le)
    i _ htα0.le htα1
  have hDpos : 0 < (Bᵀ * diagonal (fun j => w j ^ α) * B).det :=
    (pfw_posDef A hA s _ hs (fun j => Real.rpow_pos_of_pos (hwpos j) _)).det_pos
  set D := (Bᵀ * diagonal (fun j => w j ^ α) * B).det with hD
  set D' := (Bᵀ * diagonal (Function.update (fun j => w j ^ α) i
    ((3 / 4 : ℝ) ^ α * (fun j => w j ^ α) i)) * B).det with hD'
  have hD'pos : 0 < D' := lt_of_lt_of_le (mul_pos htα0 hDpos) hdet
  have hlog : Real.log ((3 / 4 : ℝ) ^ α) + Real.log D ≤ Real.log D' := by
    rw [← Real.log_mul htα0.ne' hDpos.ne']
    exact Real.log_le_log (mul_pos htα0 hDpos) hdet
  rw [Real.log_rpow ht] at hlog
  have hlog2 : Real.log (3 / 4 : ℝ) + (1 / α) * Real.log D ≤ (1 / α) * Real.log D' := by
    have h1 := mul_le_mul_of_nonneg_left hlog (le_of_lt (one_div_pos.mpr hα0))
    have h2 : (1 / α) * (α * Real.log (3 / 4 : ℝ) + Real.log D)
        = Real.log (3 / 4 : ℝ) + (1 / α) * Real.log D := by
      field_simp
    linarith
  have hsum := pfw_sum_update w i ((3 / 4) * w i)
  have hlogfun : (fun j => Real.log (w' j))
      = Function.update (fun j => Real.log (w j)) i (Real.log ((3 / 4) * w i)) := by
    funext j
    by_cases h : j = i
    · subst h; simp only [w', Function.update_self]
    · simp only [w', Function.update_of_ne h]
  have hlsum : ∑ j, Real.log (w' j) = ∑ j, Real.log (w j) + Real.log (3 / 4 : ℝ) := by
    have := pfw_sum_update (fun j => Real.log (w j)) i (Real.log ((3 / 4) * w i))
    rw [show (∑ j, Real.log (w' j)) = ∑ j, (fun j => Real.log (w' j)) j from rfl, hlogfun, this,
      Real.log_mul (by norm_num) (hwpos i).ne']
    ring
  rw [hsum, hlsum] at key
  have hl34 : -(1 / 3 : ℝ) ≤ Real.log (3 / 4 : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
    have h2 : Real.log (3 / 4 : ℝ) = - Real.log (4 / 3 : ℝ) := by
      rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv]
    linarith
  nlinarith

lemma pfw_det_upper {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (α : ℝ) (hα : 0 < α) :
    ∃ K : ℝ, ∀ w : Fin m → ℝ, (∀ j, 0 < w j) → ∀ μ : ℝ, 0 < μ → (∀ j, w j ≤ μ) →
      0 < (Bᵀ * diagonal (fun j => w j ^ α) * B).det →
      Real.log (Bᵀ * diagonal (fun j => w j ^ α) * B).det ≤ K + α * n * Real.log μ := by
  set c := ∑ j, ∑ k, |B j k| + 1 with hcdef
  have hc : ∀ j k, |B j k| ≤ c := by
    intro j k
    have h1 : |B j k| ≤ ∑ k', |B j k'| :=
      Finset.single_le_sum (f := fun k' => |B j k'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h2 : ∑ k', |B j k'| ≤ ∑ j', ∑ k', |B j' k'| :=
      Finset.single_le_sum (f := fun j' => ∑ k', |B j' k'|)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ j)
    linarith
  have hcpos : 0 < c := by
    have : 0 ≤ ∑ j, ∑ k, |B j k| := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
      (fun _ _ => abs_nonneg _))
    linarith
  set Q := ((m : ℝ) + 1) * c ^ 2 with hQdef
  have hQ : 0 < Q := by positivity
  refine ⟨Real.log ((n.factorial : ℝ) * Q ^ n), ?_⟩
  intro w hw μ hμ hwμ hdet
  have hentry : ∀ k l, |(Bᵀ * diagonal (fun j => w j ^ α) * B) k l| ≤ Q * μ ^ α := by
    intro k l
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    calc |∑ j, B j k * w j ^ α * B j l| ≤ ∑ j, |B j k * w j ^ α * B j l| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin m, c * μ ^ α * c := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hw j) _)]
          have hr : w j ^ α ≤ μ ^ α := Real.rpow_le_rpow (hw j).le (hwμ j) hα.le
          have h0 : 0 ≤ w j ^ α := (Real.rpow_pos_of_pos (hw j) _).le
          gcongr
          · exact hc j k
          · exact hc j l
      _ = (m : ℝ) * c ^ 2 * μ ^ α := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ Q * μ ^ α := by
          have : 0 ≤ μ ^ α := (Real.rpow_pos_of_pos hμ _).le
          rw [hQdef]; gcongr; linarith
  have hd := Matrix.det_le (abv := (AbsoluteValue.abs : AbsoluteValue ℝ ℝ)) (fun k l => by
    rw [AbsoluteValue.abs_apply]; exact hentry k l)
  rw [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] at hd
  have hdet' : (Bᵀ * diagonal (fun j => w j ^ α) * B).det ≤
      (n.factorial : ℝ) * (Q * μ ^ α) ^ n := le_trans (le_abs_self _) hd
  have hμα : 0 < μ ^ α := Real.rpow_pos_of_pos hμ _
  have hfact : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  calc Real.log (Bᵀ * diagonal (fun j => w j ^ α) * B).det
      ≤ Real.log ((n.factorial : ℝ) * (Q * μ ^ α) ^ n) := Real.log_le_log hdet hdet'
    _ = Real.log ((n.factorial : ℝ) * Q ^ n) + α * n * Real.log μ := by
      rw [mul_pow, ← mul_assoc, Real.log_mul (by positivity) (by positivity), Real.log_pow,
        Real.log_rpow hμ]
      ring

open PathFindingLP.WeightFunction in
lemma pfw_fhat_lower {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 ≤ β) (s : Fin m → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ K : ℝ, ∀ w : Fin m → ℝ, (∀ j, 0 < w j) → ∀ j0 : Fin m,
      (∑ j, w j) - K - ((n : ℝ) + β * ((m : ℝ) - 1)) * Real.log (∑ j, w j)
        - β * Real.log (w j0) ≤ fhat A α β s w := by
  set B := diagonal (fun i => (s i)⁻¹) * A with hB
  obtain ⟨K, hK⟩ := pfw_det_upper B α hα
  refine ⟨K / α, ?_⟩
  intro w hw j0
  have hμ : 0 < ∑ j, w j := Finset.sum_pos (fun j _ => hw j) ⟨j0, Finset.mem_univ _⟩
  have hwμ : ∀ j, w j ≤ ∑ j, w j := fun j =>
    Finset.single_le_sum (f := w) (fun j _ => (hw j).le) (Finset.mem_univ j)
  have hDpos : 0 < (Bᵀ * diagonal (fun j => w j ^ α) * B).det :=
    (pfw_posDef A hA s _ hs (fun j => Real.rpow_pos_of_pos (hw j) _)).det_pos
  have hlogD := hK w hw _ hμ hwμ hDpos
  set μ := ∑ j, w j with hμdef
  set D := (Bᵀ * diagonal (fun j => w j ^ α) * B).det with hD
  have hlogD' : (1 / α) * Real.log D ≤ K / α + n * Real.log μ := by
    have h1 := mul_le_mul_of_nonneg_left hlogD (le_of_lt (one_div_pos.mpr hα))
    have h2 : (1 / α) * (K + α * n * Real.log μ) = K / α + n * Real.log μ := by
      field_simp
    linarith
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Fin.pos j0).ne'
  have hsumlog : ∑ j, Real.log (w j) ≤ Real.log (w j0) + ((m : ℝ) - 1) * Real.log μ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
    have : ∑ j ∈ Finset.univ.erase j0, Real.log (w j) ≤
        ∑ _j ∈ Finset.univ.erase j0, Real.log μ :=
      Finset.sum_le_sum (fun j _ => Real.log_le_log (hw j) (hwμ j))
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hm1, Nat.cast_one] at this
    linarith
  have hβs := mul_le_mul_of_nonneg_left hsumlog hβ
  unfold fhat
  rw [← hB, ← hD]
  nlinarith

lemma pfw_scalar_log (c μ : ℝ) (hc : 0 ≤ c) (hμ : 0 < μ) :
    c * Real.log μ ≤ μ / 2 + c * Real.log (2 * c + 1) := by
  have h2c : 0 < 2 * c + 1 := by linarith
  have h1 := Real.log_le_sub_one_of_pos (div_pos hμ h2c)
  rw [Real.log_div hμ.ne' h2c.ne'] at h1
  have h3 : c * (Real.log μ - Real.log (2 * c + 1)) ≤ c * (μ / (2 * c + 1) - 1) :=
    mul_le_mul_of_nonneg_left h1 hc
  have h4 : c * (μ / (2 * c + 1)) ≤ μ / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ h2c (by norm_num)]
    nlinarith
  nlinarith

open PathFindingLP.WeightFunction in
/-- Existence of a minimizer of `f̂(s, ·)` on the positive orthant (coercivity). -/
lemma pfw_exists {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hm : 0 < m) (s : Fin m → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ w, IsRegularizedMinimizer A α β s w := by
  obtain ⟨K, hK⟩ := pfw_fhat_lower A hA α β hα hβ.le s hs
  set c1 := (n : ℝ) + β * ((m : ℝ) - 1) with hc1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc1n : 0 ≤ c1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  set F0 := fhat A α β s (fun _ => 1) with hF0
  set L1 := c1 * Real.log (2 * c1 + 1) with hL1
  set L2 := (c1 + β) * Real.log (2 * (c1 + β) + 1) with hL2
  set R := max 1 (2 * (F0 + K + L2) + 2) with hR
  set T := -(F0 + K + L1 + 1) / β with hT
  set ε := min 1 (Real.exp T) with hε
  have hεpos : 0 < ε := lt_min one_pos (Real.exp_pos _)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hR1 : 1 ≤ R := le_max_left _ _
  -- outside the box the objective exceeds F0
  have hout : ∀ w : Fin m → ℝ, (∀ j, 0 < w j) → ∀ j, (w j < ε ∨ R < w j) →
      F0 < fhat A α β s w := by
    intro w hw j hj
    have hlow := hK w hw j
    have hμ : 0 < ∑ i, w i := Finset.sum_pos (fun i _ => hw i) ⟨j, Finset.mem_univ _⟩
    have hwμ : w j ≤ ∑ i, w i :=
      Finset.single_le_sum (f := w) (fun i _ => (hw i).le) (Finset.mem_univ j)
    set μ := ∑ i, w i with hμdef
    rcases hj with hsmall | hlarge
    · have hsc := pfw_scalar_log c1 μ hc1n hμ
      have hlt : Real.log (w j) < T := by
        rw [Real.log_lt_iff_lt_exp (hw j)]
        exact lt_of_lt_of_le hsmall (min_le_right _ _)
      have hβT : β * T = -(F0 + K + L1 + 1) := by
        rw [hT]; field_simp
      have hβlog : β * Real.log (w j) < β * T := mul_lt_mul_of_pos_left hlt hβ
      nlinarith
    · have hsc := pfw_scalar_log (c1 + β) μ (by linarith) hμ
      have hlogj : Real.log (w j) ≤ Real.log μ := Real.log_le_log (hw j) hwμ
      have hβl := mul_le_mul_of_nonneg_left hlogj hβ.le
      have hRμ : R < μ := lt_of_lt_of_le hlarge hwμ
      have hR2 : 2 * (F0 + K + L2) + 2 ≤ R := le_max_right _ _
      nlinarith
  set S : Set (Fin m → ℝ) := Set.Icc (fun _ => ε) (fun _ => R) with hS
  have hSpos : ∀ w ∈ S, ∀ j, 0 < w j := fun w hw j => lt_of_lt_of_le hεpos (hw.1 j)
  have hcont : ContinuousOn (fun w => fhat A α β s w) S := by
    unfold fhat
    apply ContinuousOn.sub
    apply ContinuousOn.sub
    · exact (continuous_finsetSum _ (fun j _ => continuous_apply j)).continuousOn
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.log
      · apply Continuous.continuousOn
        apply Continuous.matrix_det
        apply Continuous.matrix_mul (Continuous.matrix_mul continuous_const ?_) continuous_const
        apply Continuous.matrix_diagonal
        exact continuous_pi (fun j => (Real.continuous_rpow_const hα.le).comp (continuous_apply j))
      · intro w hw
        exact (pfw_posDef A hA s _ hs
          (fun j => Real.rpow_pos_of_pos (hSpos w hw j) _)).det_pos.ne'
    · apply ContinuousOn.mul continuousOn_const
      apply continuousOn_finsetSum
      intro j _
      apply ContinuousOn.log (continuous_apply j).continuousOn
      intro w hw
      exact (hSpos w hw j).ne'
  have h1S : (fun _ : Fin m => (1 : ℝ)) ∈ S := ⟨fun _ => hε1, fun _ => hR1⟩
  obtain ⟨x, hxS, hxmin⟩ := isCompact_Icc.exists_isMinOn ⟨_, h1S⟩ hcont
  refine ⟨x, hSpos x hxS, fun w' hw' => ?_⟩
  by_cases hin : w' ∈ S
  · exact hxmin hin
  · have hx1 : fhat A α β s x ≤ F0 := hxmin h1S
    have : ∃ j, w' j < ε ∨ R < w' j := by
      by_contra hno
      push Not at hno
      exact hin ⟨fun j => (hno j).1, fun j => (hno j).2⟩
    obtain ⟨j, hj⟩ := this
    have := hout w' hw' j hj
    linarith

open Matrix PathFindingLP.WeightFunction in
lemma pfw_size_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.rank = n) (hn : 0 < n) (hnm : n < m) (s : Fin m → ℝ) (hs : ∀ i, 0 < s i)
    (w : Fin m → ℝ) (hw : IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s w) :
    ∑ i, |w i| ≤ 2 * (A.rank : ℝ) := by
  obtain ⟨hwpos, hmin⟩ := hw
  have hrank : (A.rank : ℝ) = n := by exact_mod_cast hA
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnmR : (n : ℝ) < m := by exact_mod_cast hnm
  have hmR : (0 : ℝ) < m := by linarith
  -- α > 0
  have hαpos : 0 < thm1Alpha A := by
    unfold thm1Alpha
    rw [hrank]
    have h2 : (2 : ℝ) < 2 * (m : ℝ) / n := by
      rw [lt_div_iff₀ hnR]; nlinarith
    have hL : 1 < Real.logb 2 (2 * (m : ℝ) / n) := by
      have := Real.logb_lt_logb (b := 2) (by norm_num) (by norm_num) h2
      rwa [Real.logb_self_eq_one (by norm_num)] at this
    have : (Real.logb 2 (2 * (m : ℝ) / n))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL
    linarith
  have hβm : thm1Beta A * m = n / 2 := by
    unfold thm1Beta; rw [hrank]; field_simp
  set α := thm1Alpha A with hαdef
  set β := thm1Beta A with hβdef
  have ht : (0 : ℝ) < 3 / 4 := by norm_num
  have key := hmin (fun i => (3 / 4 : ℝ) * w i) (fun i => mul_pos ht (hwpos i))
  unfold fhat at key
  set B := diagonal (fun i => (s i)⁻¹) * A with hB
  have hdiag : diagonal (fun i => ((3 / 4 : ℝ) * w i) ^ α)
      = ((3 / 4 : ℝ) ^ α) • diagonal (fun i => w i ^ α) := by
    ext i j
    rw [Matrix.smul_apply, diagonal_apply, diagonal_apply]
    split_ifs with h
    · subst h; rw [Real.mul_rpow ht.le (hwpos i).le]; rfl
    · simp
  have hdet : det (Bᵀ * diagonal (fun i => ((3 / 4 : ℝ) * w i) ^ α) * B)
      = ((3 / 4 : ℝ) ^ α) ^ n * det (Bᵀ * diagonal (fun i => w i ^ α) * B) := by
    rw [hdiag, Matrix.mul_smul, Matrix.smul_mul, Matrix.det_smul, Fintype.card_fin]
  rw [hdet] at key
  have hsum1 : ∑ i, (3 / 4 : ℝ) * w i = (3 / 4 : ℝ) * ∑ i, w i := by rw [Finset.mul_sum]
  have hlog : ∑ i, Real.log ((3 / 4 : ℝ) * w i)
      = m * Real.log (3 / 4 : ℝ) + ∑ i, Real.log (w i) := by
    have : ∀ i, Real.log ((3 / 4 : ℝ) * w i) = Real.log (3 / 4 : ℝ) + Real.log (w i) :=
      fun i => Real.log_mul (by norm_num) (hwpos i).ne'
    simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hsum1, hlog] at key
  set D := det (Bᵀ * diagonal (fun i => w i ^ α) * B) with hD
  set S := ∑ i, w i with hS
  set Lw := ∑ i, Real.log (w i) with hLw
  -- log (3/4) ≥ -1/3
  have hlt : -(1 / 3 : ℝ) ≤ Real.log (3 / 4 : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
    have h2 : Real.log (3 / 4 : ℝ) = - Real.log (4 / 3 : ℝ) := by
      rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv]
    linarith
  have hlneg : Real.log (3 / 4 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hSbound : S ≤ 2 * n := by
    by_cases hD0 : D = 0
    · rw [hD0, mul_zero, Real.log_zero] at key
      have hk : (1 / 4 : ℝ) * S ≤ -(β * m) * Real.log (3 / 4 : ℝ) := by nlinarith
      rw [hβm] at hk
      nlinarith
    · have hpow : ((3 / 4 : ℝ) ^ α) ^ n ≠ 0 := pow_ne_zero _ (Real.rpow_pos_of_pos ht _).ne'
      rw [Real.log_mul hpow hD0, Real.log_pow, Real.log_rpow ht] at key
      have hcancel : (1 / α) * ((n : ℝ) * (α * Real.log (3 / 4 : ℝ)))
          = n * Real.log (3 / 4 : ℝ) := by field_simp
      have hk : (1 / 4 : ℝ) * S ≤ -(n + β * m) * Real.log (3 / 4 : ℝ) := by
        have := key
        rw [mul_add, hcancel] at this
        nlinarith
      rw [hβm] at hk
      nlinarith
  have habs : ∑ i, |w i| = S := Finset.sum_congr rfl (fun i _ => abs_of_pos (hwpos i))
  rw [habs, hrank]
  exact hSbound

open PathFindingLP.WeightFunction in
lemma pfw_alpha_pos {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.rank = n) (hn : 0 < n) (hnm : n < m) : 0 < thm1Alpha A := by
  have hrank : (A.rank : ℝ) = n := by exact_mod_cast hA
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnmR : (n : ℝ) < m := by exact_mod_cast hnm
  unfold thm1Alpha
  rw [hrank]
  have h2 : (2 : ℝ) < 2 * (m : ℝ) / n := by
    rw [lt_div_iff₀ hnR]; nlinarith
  have hL : 1 < Real.logb 2 (2 * (m : ℝ) / n) := by
    have := Real.logb_lt_logb (b := 2) (by norm_num) (by norm_num) h2
    rwa [Real.logb_self_eq_one (by norm_num)] at this
  have : (Real.logb 2 (2 * (m : ℝ) / n))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL
  linarith

open PathFindingLP.WeightFunction in
lemma pfw_beta_bounds {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.rank = n) (hn : 0 < n) (hnm : n < m) : 0 < thm1Beta A ∧ thm1Beta A ≤ 1 / 2 := by
  have hrank : (A.rank : ℝ) = n := by exact_mod_cast hA
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnmR : (n : ℝ) < m := by exact_mod_cast hnm
  have hmR : (0 : ℝ) < m := by linarith
  unfold thm1Beta
  rw [hrank]
  constructor
  · positivity
  · rw [div_le_iff₀ (by positivity)]; linarith

open PathFindingLP.WeightFunction in
/-- Uniqueness from differentiability of every minimizer selector: two selectors that differ only
at `s₀` are both continuous at `s₀`, so they agree there. -/
lemma pfw_unique_of_diff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.rank = n) (hn : 0 < n) (hnm : n < m)
    (hdiff : ∀ g : (Fin m → ℝ) → (Fin m → ℝ),
      (∀ s : Fin m → ℝ, (∀ i, 0 < s i) →
        IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s (g s)) →
      ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → DifferentiableAt ℝ g s)
    (s₀ w w' : Fin m → ℝ) (hs₀ : ∀ i, 0 < s₀ i)
    (hw : IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s₀ w)
    (hw' : IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s₀ w') : w = w' := by
  classical
  have hm : 0 < m := lt_trans hn hnm
  have hex : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) →
      ∃ v, IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s v := fun s hs =>
    pfw_exists A hA _ _ (pfw_alpha_pos A hA hn hnm) (pfw_beta_bounds A hA hn hnm).1 hm s hs
  let g0 : (Fin m → ℝ) → (Fin m → ℝ) := fun s =>
    if h : ∀ i, 0 < s i then (hex s h).choose else 0
  have hg0 : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) →
      IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s (g0 s) := by
    intro s h
    simp only [g0, dif_pos h]
    exact (hex s h).choose_spec
  have hsel : ∀ v, IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s₀ v →
      ∀ s : Fin m → ℝ, (∀ i, 0 < s i) →
        IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s (Function.update g0 s₀ v s) := by
    intro v hv s h
    by_cases hs : s = s₀
    · subst hs; rw [Function.update_self]; exact hv
    · rw [Function.update_of_ne hs]; exact hg0 s h
  have ca := (hdiff _ (hsel w hw) s₀ hs₀).continuousAt
  have cb := (hdiff _ (hsel w' hw') s₀ hs₀).continuousAt
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have ta : Filter.Tendsto (Function.update g0 s₀ w) (nhdsWithin s₀ {s₀}ᶜ)
      (nhds (Function.update g0 s₀ w s₀)) := ca.tendsto.mono_left nhdsWithin_le_nhds
  have tb : Filter.Tendsto (Function.update g0 s₀ w') (nhdsWithin s₀ {s₀}ᶜ)
      (nhds (Function.update g0 s₀ w' s₀)) := cb.tendsto.mono_left nhdsWithin_le_nhds
  have heq : Function.update g0 s₀ w =ᶠ[nhdsWithin s₀ {s₀}ᶜ] Function.update g0 s₀ w' := by
    apply eventually_nhdsWithin_of_forall
    intro s hs
    rw [Function.update_of_ne hs, Function.update_of_ne hs]
  have := tendsto_nhds_unique (ta.congr' heq) tb
  simpa [Function.update_self] using this

open PathFindingLP.WeightFunction in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.rank = n) (hn : 0 < n) (hnm : n < m) :
    (∀ s : Fin m → ℝ, (∀ i, 0 < s i) →
        ∃! w : Fin m → ℝ, IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s w) ∧
      ∀ g : (Fin m → ℝ) → (Fin m → ℝ),
        (∀ s : Fin m → ℝ, (∀ i, 0 < s i) →
          IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s (g s)) →
        IsWeightFunction A g (2 * (A.rank : ℝ)) 2
          (2 * Real.logb 2 (2 * (m : ℝ) / (A.rank : ℝ))) := by
  have hm : 0 < m := lt_trans hn hnm
  have hα := pfw_alpha_pos A hA hn hnm
  have hβ := pfw_beta_bounds A hA hn hnm
  have hdiff : ∀ g : (Fin m → ℝ) → (Fin m → ℝ),
      (∀ s : Fin m → ℝ, (∀ i, 0 < s i) →
        IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s (g s)) →
      ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → DifferentiableAt ℝ g s :=
    fun g hg => (PathFindingLP.WeightFunction.step_consistency A hA hn hnm g hg).1
  refine ⟨fun s hs => ?_, fun g hg => ?_⟩
  · obtain ⟨w, hw⟩ := pfw_exists A hA _ _ hα hβ.1 hm s hs
    exact ⟨w, hw, fun w' hw' => pfw_unique_of_diff A hA hn hnm hdiff s w' w hs hw' hw⟩
  · have hsc := PathFindingLP.WeightFunction.step_consistency A hA hn hnm g hg
    refine ⟨fun s hs => ⟨(hg s hs).1, hsc.1 s hs⟩, fun s hs => pfw_size_bound A hA hn hnm s hs _
      (hg s hs), ⟨by norm_num, fun s hs =>
        PathFindingLP.WeightFunction.slack_sensitivity_bound A hA hn hnm s hs _ (hg s hs)⟩,
      hsc.2, fun s hs => ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    rw [Real.norm_eq_abs, abs_of_pos ((hg s hs).1 i)]
    exact pfw_le_two A hA _ _ hα hβ.1.le hβ.2 s (g s) hs (hg s hs) i
