-- Prove2me | solution 1 for PriceCapacities.LowerBound.lemma_10_7
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T07:38:47.226944+00:00
-- url     : https://prove2.me/submissions/a4801074-2936-4354-821c-be6358e65886

import Mathlib

namespace PCQ
open Polynomial Real


noncomputable def nd (m : ℕ) (k : ℕ) : ℝ := cos ((2*k+1)*π/(2*m))

lemma nd_inj (m : ℕ) : Set.InjOn (nd m) (Finset.range m : Finset ℕ) := by
  have h := Polynomial.Chebyshev.roots_T_real_nodup m
  have := (Finset.range m).nodup_map_iff_injOn.mp h
  exact this

lemma T_eq_nodal (m : ℕ) :
    Chebyshev.T ℝ (m:ℤ) = C (Chebyshev.T ℝ (m:ℤ)).leadingCoeff *
      Lagrange.nodal (Finset.range m) (nd m) := by
  have hr := Polynomial.Chebyshev.roots_T_real m
  have hc : Multiset.card (Chebyshev.T ℝ (m:ℤ)).roots = (Chebyshev.T ℝ (m:ℤ)).natDegree := by
    rw [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast, hr]
    change (Finset.image (nd m) (Finset.range m)).card = m
    rw [Finset.card_image_of_injOn (nd_inj m), Finset.card_range]
  have := C_leadingCoeff_mul_prod_multiset_X_sub_C hc
  rw [Lagrange.nodal_eq]
  conv_lhs => rw [← this]
  rw [hr]
  congr 1
  change ∏ x ∈ Finset.image (nd m) (Finset.range m), (X - C x) = _
  rw [Finset.prod_image (nd_inj m)]


lemma sin_psi (m j : ℕ) (hm : 1 ≤ m) :
    sin ((m:ℝ) * ((2*j+1)*π/(2*m))) = (-1)^j := by
  have hm' : (m:ℝ) ≠ 0 := by positivity
  have : (m:ℝ) * ((2*j+1)*π/(2*m)) = j*π + π/2 := by field_simp
  rw [this, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]

lemma basis_at_one (m j : ℕ) (hm : 1 ≤ m) (hj : j < m) :
    eval 1 (Lagrange.basis (Finset.range m) (nd m) j) =
      (-1)^j * (cos (π*(2*j+1)/(4*m)) / (m * sin (π*(2*j+1)/(4*m)))) := by
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  have hjs : j ∈ Finset.range m := Finset.mem_range.mpr hj
  have hT := T_eq_nodal m
  set a := (Chebyshev.T ℝ (m:ℤ)).leadingCoeff with ha
  have ha0 : a ≠ 0 := by
    rw [ha]; simp only [ne_eq, leadingCoeff_eq_zero]
    intro h
    have := Polynomial.Chebyshev.degree_T (R := ℝ) (m:ℤ)
    rw [h] at this; simp at this
  have hnod : Lagrange.nodal (Finset.range m) (nd m) = C a⁻¹ * Chebyshev.T ℝ (m:ℤ) := by
    rw [hT, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha0]; simp
  set ψ := (2*(j:ℝ)+1)*π/(2*m) with hψ
  have hψpos : 0 < ψ := by positivity
  have hψlt : ψ < π := by
    rw [hψ, div_lt_iff₀ (by positivity)]
    have : (2*(j:ℝ)+1) < 2*m := by
      have : (j:ℝ)+1 ≤ m := by exact_mod_cast hj
      linarith
    nlinarith [Real.pi_pos]
  have hsin : 0 < sin ψ := Real.sin_pos_of_pos_of_lt_pi hψpos hψlt
  have hv : nd m j = cos ψ := rfl
  have hne : (1:ℝ) ≠ nd m j := by
    rw [hv]
    have : cos ψ < 1 := by
      rw [← Real.cos_zero]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl _) hψlt.le hψpos
    linarith
  rw [Lagrange.eval_basis_not_at_node hjs hne]
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hjs, hnod, derivative_C_mul,
    Polynomial.Chebyshev.T_derivative_eq_U]
  have hU := Polynomial.Chebyshev.U_real_cos ψ ((m:ℤ) - 1)
  have hT1 : (Chebyshev.T ℝ (m:ℤ)).eval 1 = 1 := by
    have := Polynomial.Chebyshev.T_real_cos 0 (m:ℤ)
    simpa using this
  have hsm : sin (((m:ℤ) - 1 + 1 : ℤ) * ψ) = (-1)^j := by
    have := sin_psi m j hm
    push_cast; simpa [hψ] using this
  have hUv : (Chebyshev.U ℝ ((m:ℤ)-1)).eval (nd m j) = (-1)^j / sin ψ := by
    rw [hv, eq_div_iff hsin.ne']; rw [← hsm]; exact_mod_cast hU
  have hφ : π*(2*j+1)/(4*m) = ψ/2 := by rw [hψ]; field_simp; ring
  rw [hφ]
  have hs2 : 0 < sin (ψ/2) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hsin2 : sin ψ = 2 * sin (ψ/2) * cos (ψ/2) := by
    have := Real.sin_two_mul (ψ/2); rwa [show 2*(ψ/2) = ψ by ring] at this
  have hcos2 : cos ψ = 1 - 2 * sin (ψ/2)^2 := by
    have := Real.cos_two_mul (ψ/2); rw [show 2*(ψ/2) = ψ by ring] at this
    rw [this]; nlinarith [Real.sin_sq_add_cos_sq (ψ/2)]
  have hc2 : 0 < cos (ψ/2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  simp only [eval_mul, eval_C, hT1, hv, eval_natCast, Int.cast_natCast]
  rw [hv] at hUv
  rw [hUv, hsin2, hcos2]
  field_simp
  ring_nf
  have h1 : (-1:ℝ)^(j*2) = 1 := by rw [pow_mul']; norm_num
  rw [h1]; ring


lemma quad (m i : ℕ) (hm : 1 ≤ m) (hi : i < m) :
    ∑ j ∈ Finset.range m, ((-1:ℝ)^j * (cos (π*(2*j+1)/(4*m)) / (m * sin (π*(2*j+1)/(4*m))))) *
      sin (π*(2*j+1)/(4*m)) ^ (2*i) = if i = 0 then 1 else 0 := by
  set f : ℝ[X] := (C (1/2 : ℝ) * (1 - X))^i with hf
  have hnat : f.natDegree ≤ i := by
    refine (natDegree_pow_le).trans ?_
    have : (C (1/2 : ℝ) * (1 - X)).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans (by
        refine (natDegree_sub_le _ _).trans ?_; simp)
    nlinarith
  have hdeg : f.degree < (Finset.range m).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt (degree_le_natDegree) (by exact_mod_cast lt_of_le_of_lt hnat hi)
  have h := Lagrange.eq_interpolate (nd_inj m) hdeg
  have h1 := congrArg (eval 1) h
  rw [Lagrange.interpolate_apply, eval_finset_sum] at h1
  have hl : eval 1 f = if i = 0 then 1 else 0 := by
    rw [hf]; simp [eval_pow, zero_pow_eq]
  rw [← hl, h1]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  rw [eval_mul, eval_C, basis_at_one m j hm hj']
  have : eval (nd m j) f = sin (π*(2*j+1)/(4*m)) ^ (2*i) := by
    have hψ : nd m j = cos ((2*j+1)*π/(2*m)) := rfl
    have hm0 : (m:ℝ) ≠ 0 := by positivity
    have hs : sin (π*(2*j+1)/(4*m)) ^ 2 = (1 - nd m j)/2 := by
      rw [hψ, show (2*(j:ℝ)+1)*π/(2*m) = 2 * (π*(2*j+1)/(4*m)) by field_simp; ring,
        Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (π*(2*j+1)/(4*m))]
    rw [hf, eval_pow, pow_mul, hs]; simp; ring_nf
  rw [this]; ring




lemma binom_hasSum (β : ℝ) (y : ℝ) (hy : |y| < 1) :
    HasSum (fun n : ℕ => Ring.choose β n * y ^ n) ((1 + y) ^ β) := by
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := β)).hasSum
    (y := y) (by simpa [edist_dist] using hy)
  simpa [binomialSeries, FormalMultilinearSeries.coeff_ofScalars, mul_comm, add_zero] using h

lemma binom_bdd (β : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, |Ring.choose β n| * (9/10:ℝ)^n ≤ B := by
  have h := (binom_hasSum β (9/10) (by norm_num [abs_of_pos])).summable
  have h2 := (h.norm).tendsto_atTop_zero
  obtain ⟨B, hB⟩ := h2.bddAbove_range
  refine ⟨max B 0, le_max_right _ _, fun n => ?_⟩
  have := hB ⟨n, rfl⟩
  simp only [norm_mul, norm_pow, Real.norm_eq_abs] at this
  rw [abs_of_pos (by norm_num : (0:ℝ) < 9/10)] at this
  exact this.trans (le_max_left _ _)

lemma tail (β : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ (m : ℕ) (e w : ℕ → ℝ), 0 < m →
    (∀ k < m, 0 ≤ e k ∧ e k ≤ 1) →
    (∀ n < m, ∑ k ∈ Finset.range m, w k * e k ^ n = if n = 0 then 1 else 0) →
    ∀ t : ℝ, |t| ≤ 1/4 →
    |∑ k ∈ Finset.range m, w k * (1 + e k * t) ^ β - 1| ≤
      B * (∑ k ∈ Finset.range m, |w k|) * (5/18) ^ m := by
  obtain ⟨B, hB0, hB⟩ := binom_bdd β
  refine ⟨2 * B, by positivity, fun m e w hm he hmom t ht => ?_⟩
  set S := ∑ k ∈ Finset.range m, |w k| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hy : ∀ k ∈ Finset.range m, |e k * t| ≤ 1/4 := by
    intro k hk
    obtain ⟨h0, h1⟩ := he k (Finset.mem_range.mp hk)
    rw [abs_mul, abs_of_nonneg h0]
    calc e k * |t| ≤ 1 * (1/4) := mul_le_mul h1 ht (abs_nonneg _) (by norm_num)
      _ = 1/4 := by norm_num
  have hsum : HasSum (fun n : ℕ => ∑ k ∈ Finset.range m, w k * (Ring.choose β n * (e k * t)^n))
      (∑ k ∈ Finset.range m, w k * (1 + e k * t) ^ β) := by
    refine hasSum_sum (fun k hk => ?_)
    exact (binom_hasSum β _ (lt_of_le_of_lt (hy k hk) (by norm_num))).mul_left (w k)
  set a : ℕ → ℝ := fun n => ∑ k ∈ Finset.range m, w k * (Ring.choose β n * (e k * t)^n) with ha
  have ha' : ∀ n, a n = Ring.choose β n * t ^ n * ∑ k ∈ Finset.range m, w k * e k ^ n := by
    intro n; rw [ha]; simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mul_pow]; ring
  have hhead : ∑ i ∈ Finset.range m, a i = 1 := by
    rw [Finset.sum_eq_single 0]
    · rw [ha', hmom 0 hm]; simp
    · intro b hb hb0
      rw [ha', hmom b (Finset.mem_range.mp hb)]; simp [hb0]
    · intro h; exact absurd (Finset.mem_range.mpr hm) h
  have htail := (hasSum_nat_add_iff' m).mpr hsum
  rw [hhead] at htail
  have hg : HasSum (fun n : ℕ => B * S * (5/18:ℝ)^m * (5/18:ℝ)^n)
      (B * S * (5/18:ℝ)^m * (1 - 5/18)⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hbd : ∀ n, ‖a (n + m)‖ ≤ B * S * (5/18:ℝ)^m * (5/18:ℝ)^n := by
    intro n
    rw [ha', Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have h1 : |∑ k ∈ Finset.range m, w k * e k ^ (n+m)| ≤ S := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k hk => ?_))
      obtain ⟨h0, h1⟩ := he k (Finset.mem_range.mp hk)
      rw [abs_mul, abs_of_nonneg (pow_nonneg h0 _)]
      calc |w k| * e k ^ (n+m) ≤ |w k| * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ h0 h1) (abs_nonneg _)
        _ = |w k| := mul_one _
    have h2 : |Ring.choose β (n+m)| ≤ B * (10/9:ℝ)^(n+m) := by
      have := hB (n+m)
      have hp : (0:ℝ) < (9/10)^(n+m) := by positivity
      rw [show (10/9:ℝ) = ((9/10:ℝ))⁻¹ by norm_num, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hp]
      exact this
    have h3 : |t|^(n+m) ≤ (1/4:ℝ)^(n+m) := pow_le_pow_left₀ (abs_nonneg _) ht _
    calc |Ring.choose β (n+m)| * |t|^(n+m) * |∑ k ∈ Finset.range m, w k * e k ^ (n+m)|
        ≤ (B * (10/9:ℝ)^(n+m)) * (1/4:ℝ)^(n+m) * S := by
          gcongr
      _ = B * S * (5/18:ℝ)^m * (5/18:ℝ)^n := by
          rw [show (5/18:ℝ) = (10/9) * (1/4) by norm_num, mul_pow, mul_pow, pow_add, pow_add]
          ring
  have := htail.norm_le_of_bounded hg hbd
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  have : 0 ≤ B * S * (5/18:ℝ)^m := by positivity
  norm_num
  nlinarith




noncomputable def phi (m j : ℕ) : ℝ := π*(2*j+1)/(4*m)

lemma phi_pos (m j : ℕ) (hm : 1 ≤ m) : 0 < phi m j := by
  unfold phi; have : (0:ℝ) < m := by exact_mod_cast hm
  positivity

lemma phi_lt (m j : ℕ) (hm : 1 ≤ m) (hj : j < m) : phi m j < π/2 := by
  unfold phi
  have : (0:ℝ) < m := by exact_mod_cast hm
  have hj' : (j:ℝ) + 1 ≤ m := by exact_mod_cast hj
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [Real.pi_pos]

lemma sin_phi_ge (m j : ℕ) (hm : 1 ≤ m) (hj : j < m) :
    (2*j+1)/(2*m) ≤ sin (phi m j) := by
  have h := Real.mul_le_sin (phi_pos m j hm).le (phi_lt m j hm hj).le
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  refine le_trans (le_of_eq ?_) h
  unfold phi; field_simp <;> norm_num

lemma sin_phi_pos (m j : ℕ) (hm : 1 ≤ m) (hj : j < m) : 0 < sin (phi m j) :=
  Real.sin_pos_of_pos_of_lt_pi (phi_pos m j hm) (by linarith [phi_lt m j hm hj, Real.pi_pos])

lemma cos_phi_nonneg (m j : ℕ) (hm : 1 ≤ m) (hj : j < m) : 0 ≤ cos (phi m j) :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [phi_pos m j hm, Real.pi_pos], (phi_lt m j hm hj).le⟩

lemma w_abs (m j : ℕ) (hm : 1 ≤ m) (hj : j < m) :
    |(-1:ℝ)^j * (cos (phi m j) / (m * sin (phi m j)))| = cos (phi m j) / (m * sin (phi m j)) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (div_nonneg (cos_phi_nonneg m j hm hj)
      (mul_pos hm' (sin_phi_pos m j hm hj)).le)]

lemma w_le_two (m j : ℕ) (hm : 1 ≤ m) (hj : j < m) :
    cos (phi m j) / (m * sin (phi m j)) ≤ 2 := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hs := sin_phi_ge m j hm hj
  have hp := sin_phi_pos m j hm hj
  have hc := Real.cos_le_one (phi m j)
  have : 1/2 ≤ m * sin (phi m j) := by
    have : (2*(j:ℝ)+1)/(2*m) * m ≤ sin (phi m j) * m := mul_le_mul_of_nonneg_right hs hm'.le
    have h2 : (2*(j:ℝ)+1)/(2*m) * m = (2*j+1)/2 := by field_simp
    nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma sum_w_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ j ∈ Finset.range m, |(-1:ℝ)^j * (cos (phi m j) / (m * sin (phi m j)))| ≤ 2 * m := by
  calc _ ≤ ∑ j ∈ Finset.range m, (2:ℝ) := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        have hj' := Finset.mem_range.mp hj
        rw [w_abs m j hm hj']; exact w_le_two m j hm hj'
    _ = 2 * m := by simp [mul_comm]

lemma inv_cube_sum (m : ℕ) : ∑ j ∈ Finset.range m, 1 / (2*(j:ℝ)+1)^3 ≤ 2 - 2/((m:ℝ)+1) := by
  induction m with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have : 1 / (2*(n:ℝ)+1)^3 ≤ 2/((n:ℝ)+1) - 2/((n+1:ℕ)+1) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [mul_nonneg hn hn, mul_nonneg (mul_nonneg hn hn) hn, mul_nonneg hn (mul_nonneg hn (mul_nonneg hn hn))]
    push_cast at this ⊢
    linarith

lemma sum_w_div_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ j ∈ Finset.range m, |(-1:ℝ)^j * (cos (phi m j) / (m * sin (phi m j)))| / sin (phi m j) ^ 2
      ≤ 16 * (m:ℝ)^2 := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  calc _ ≤ ∑ j ∈ Finset.range m, 8 * (m:ℝ)^2 * (1 / (2*(j:ℝ)+1)^3) := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        have hj' := Finset.mem_range.mp hj
        rw [w_abs m j hm hj']
        have hs := sin_phi_ge m j hm hj'
        have hp := sin_phi_pos m j hm hj'
        have hc := Real.cos_le_one (phi m j)
        have hc0 := cos_phi_nonneg m j hm hj'
        have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
        set s := sin (phi m j)
        have h1 : cos (phi m j) / (m * s) / s^2 ≤ 1 / (m * s^3) := by
          rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [pow_pos hp 3, pow_pos hp 2, mul_pos hm' (pow_pos hp 3)]
        refine h1.trans ?_
        have h2 : ((2*(j:ℝ)+1)/(2*m))^3 ≤ s^3 := pow_le_pow_left₀ (by positivity) hs 3
        rw [div_le_iff₀ (by positivity)]
        calc (1:ℝ) = 8 * (m:ℝ)^2 * (1 / (2*(j:ℝ)+1)^3) * (m * ((2*(j:ℝ)+1)/(2*m))^3) := by
              field_simp <;> norm_num
          _ ≤ 8 * (m:ℝ)^2 * (1 / (2*(j:ℝ)+1)^3) * (m * s^3) := by
              gcongr
    _ = 8 * (m:ℝ)^2 * ∑ j ∈ Finset.range m, 1 / (2*(j:ℝ)+1)^3 := by rw [Finset.mul_sum]
    _ ≤ 16 * (m:ℝ)^2 := by
        have := inv_cube_sum m
        have h3 : (0:ℝ) ≤ 2/((m:ℝ)+1) := by positivity
        nlinarith [sq_nonneg (m:ℝ)]




lemma mvt_reduction (α K0 : ℝ) (hK0 : 0 < K0) (M : ℕ) (K γ : Fin M → ℝ)
    (hK : ∀ l, K0 ≤ K l) (E : ℝ)
    (hE : ∀ a : ℝ, |a| ≤ K0/4 → |∑ l, γ l * (α * (K l + a) ^ (α - 1)) - 1| ≤ E)
    (u h : ℝ) (hu : 0 ≤ u) (hh : |h| ≤ K0/4) (hhu : |h - u| ≤ K0/4) :
    |∑ l, γ l * ((K l + h) ^ α - (K l + h - u) ^ α) - u| ≤ E * u := by
  rw [abs_le] at hh hhu
  let H : ℝ → ℝ := fun s => ∑ l, γ l * (K l + h - s) ^ α + s
  have hder : ∀ s ∈ Set.Icc 0 u, HasDerivWithinAt H
      (-(∑ l, γ l * (α * (K l + (h - s)) ^ (α - 1)) - 1)) (Set.Icc 0 u) s := by
    intro s hs
    have hpos : ∀ l, K l + h - s ≠ 0 := by
      intro l
      have := hK l; have := hs.1; have := hs.2; nlinarith [hh.1, hhu.1]
    have h1 : ∀ l ∈ (Finset.univ : Finset (Fin M)), HasDerivAt (fun s => γ l * (K l + h - s) ^ α)
        (γ l * (-1 * α * (K l + h - s) ^ (α - 1))) s := by
      intro l _
      have hd : HasDerivAt (fun s : ℝ => K l + h - s) (-1) s := by
        exact (hasDerivAt_const s (K l + h)).sub (hasDerivAt_id s) |>.congr_deriv (by ring)
      exact (hd.rpow_const (Or.inl (hpos l))).const_mul (γ l)
    have h2 := (HasDerivAt.fun_sum h1).add (hasDerivAt_id s)
    have h3 : HasDerivAt H (∑ l, γ l * (-1 * α * (K l + h - s) ^ (α - 1)) + 1) s := h2
    have h4 : ∑ l, γ l * (-1 * α * (K l + h - s) ^ (α - 1)) + 1
        = -(∑ l, γ l * (α * (K l + (h - s)) ^ (α - 1)) - 1) := by
      rw [neg_sub]
      have : ∑ l, γ l * (-1 * α * (K l + h - s) ^ (α - 1)) =
          -∑ l, γ l * (α * (K l + (h - s)) ^ (α - 1)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [show K l + (h - s) = K l + h - s by ring]; ring
      rw [this]; ring
    rw [← h4]; exact h3.hasDerivWithinAt
  have hbound : ∀ s ∈ Set.Icc 0 u,
      ‖-(∑ l, γ l * (α * (K l + (h - s)) ^ (α - 1)) - 1)‖ ≤ E := by
    intro s hs
    rw [norm_neg, Real.norm_eq_abs]
    refine hE (h - s) ?_
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_Icc 0 u)
    (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu)
  have e1 : H u - H 0 = -(∑ l, γ l * ((K l + h) ^ α - (K l + h - u) ^ α) - u) := by
    simp only [H]
    rw [show ∑ l, γ l * (K l + h - u) ^ α = ∑ l, γ l * (K l + h - u) ^ α from rfl]
    have : ∑ l, γ l * ((K l + h) ^ α - (K l + h - u) ^ α) =
        ∑ l, γ l * (K l + h - 0) ^ α - ∑ l, γ l * (K l + h - u) ^ α := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun l _ => by rw [sub_zero]; ring)
    rw [this]; ring
  rw [e1, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg hu] at this
  exact this


lemma sin_low (q M : ℕ) (hq : 4 ≤ q) (hM : 5 * q ≤ M) (j : ℕ) (hj : j < 3 * q) :
    1 / (M:ℝ) ≤ sin (phi (3*q) j) := by
  have hq' : (4:ℝ) ≤ q := by exact_mod_cast hq
  have hM' : 5 * (q:ℝ) ≤ M := by exact_mod_cast hM
  have hm1 : 1 ≤ 3 * q := by omega
  have hm' : ((3*q : ℕ):ℝ) = 3 * q := by push_cast; ring
  have h0 : phi (3*q) 0 ≤ phi (3*q) j := by
    unfold phi
    have : (0:ℝ) < ((3*q:ℕ):ℝ) := by rw [hm']; positivity
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : (0:ℝ) ≤ j := Nat.cast_nonneg j
    simp only [Nat.cast_zero, mul_zero, zero_add, mul_one]
    nlinarith [mul_nonneg Real.pi_pos.le this]
  have hsin : sin (phi (3*q) 0) ≤ sin (phi (3*q) j) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [phi_pos (3*q) 0 hm1, Real.pi_pos]) 
      (phi_lt (3*q) j hm1 hj).le h0
  refine le_trans ?_ hsin
  set x := phi (3*q) 0 with hx
  have hxv : x = π / (12 * q) := by
    rw [hx]; unfold phi; rw [hm']; field_simp; ring
  have hqpos : (0:ℝ) < q := by linarith
  have hx0 : 0 < x := by rw [hxv]; positivity
  have hx1 : x ≤ 1/2 := by
    rw [hxv, div_le_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four]
  have hs := Real.sin_gt_sub_cube hx0
  have hxx : x * x ≤ 1/4 := by nlinarith
  have : x - x^3/6 ≥ x * (15/16) := by nlinarith [mul_le_mul_of_nonneg_left hxx hx0.le]
  have h5 : 1 / (M:ℝ) ≤ 1 / (5 * q) := one_div_le_one_div_of_le (by positivity) hM'
  have h6 : 1 / (5 * (q:ℝ)) ≤ x * (15/16) := by
    rw [hxv, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.pi_gt_three]
  linarith

lemma fin_sum (M m : ℕ) (hmM : m ≤ M) (g : ℕ → ℝ) :
    ∑ l : Fin M, (if l.val < m then g l.val else 0) = ∑ n ∈ Finset.range m, g n := by
  rw [Fin.sum_univ_eq_sum_range (fun n => if n < m then g n else 0) M, ← Finset.sum_filter]
  congr 1
  ext n; simp only [Finset.mem_filter, Finset.mem_range]; omega

lemma numeric_bound (q M : ℕ) (hM : M ≤ 5 * q + 4) :
    (2:ℝ)^M * (2 * ((3*q : ℕ):ℝ) * (5/18:ℝ)^(3*q)) ≤ 224 := by
  have h1 : (2:ℝ)^M ≤ 2^(5*q+4) := pow_le_pow_right₀ (by norm_num) hM
  have hb : 1 + (q:ℝ) * (3/7) ≤ (1 + 3/7)^q := one_add_mul_le_pow (by norm_num) q
  have h2 : (q:ℝ) * (7/10)^q ≤ 7/3 := by
    have h3 : (10/7:ℝ)^q * (7/10)^q = 1 := by rw [← mul_pow]; norm_num
    have h4 : (0:ℝ) ≤ (7/10)^q := by positivity
    have : (q:ℝ) * (3/7) ≤ (10/7)^q := by norm_num at hb; linarith
    nlinarith
  have h5 : (32 * (5/18:ℝ)^3)^q ≤ (7/10)^q := pow_le_pow_left₀ (by positivity) (by norm_num) q
  have e1 : (2:ℝ)^(5*q+4) = 16 * 32^q := by rw [pow_add, pow_mul]; norm_num; ring
  have e2 : (5/18:ℝ)^(3*q) = ((5/18)^3)^q := by rw [pow_mul]
  have e3 : (2:ℝ)^(5*q+4) * (2 * ((3*q : ℕ):ℝ) * (5/18:ℝ)^(3*q)) = 96 * q * (32 * (5/18:ℝ)^3)^q := by
    rw [e1, e2, mul_pow]; push_cast; ring
  calc (2:ℝ)^M * (2 * ((3*q : ℕ):ℝ) * (5/18:ℝ)^(3*q))
      ≤ (2:ℝ)^(5*q+4) * (2 * ((3*q : ℕ):ℝ) * (5/18:ℝ)^(3*q)) := by gcongr
    _ = 96 * q * (32 * (5/18:ℝ)^3)^q := e3
    _ ≤ 96 * q * (7/10)^q := by gcongr
    _ ≤ 224 := by nlinarith

lemma KK (α K0 : ℝ) (hK0 : 0 < K0) : K0 ^ (1 - α) * K0 ^ (α - 1) = 1 := by
  rw [← Real.rpow_add hK0]; simp

lemma T1 (α K0 e w a : ℝ) (hα : 0 < α) (hK0 : 0 < K0) (he0 : 0 < e) (he1 : e ≤ 1)
    (ha : |a / K0| ≤ 1/4) :
    (K0 ^ (1 - α) * α⁻¹ * w * e ^ (α - 1)) * (α * (K0 / e + a) ^ (α - 1)) =
      w * (1 + e * (a / K0)) ^ (α - 1) := by
  have hk : K0 / e + a = (K0 / e) * (1 + e * (a / K0)) := by field_simp
  have hp : 0 < 1 + e * (a / K0) := by
    rw [abs_le] at ha; nlinarith [ha.1, ha.2]
  rw [hk, Real.mul_rpow (by positivity) hp.le, Real.div_rpow hK0.le he0.le]
  have hKK := KK α K0 hK0
  have he' : e ^ (α - 1) ≠ 0 := (Real.rpow_pos_of_pos he0 _).ne'
  generalize (1 + e * (a / K0)) ^ (α - 1) = P
  generalize K0 ^ (α - 1) = Kb at hKK ⊢
  generalize e ^ (α - 1) = eb at he' ⊢
  have hα' : α ≠ 0 := hα.ne'
  calc K0 ^ (1 - α) * α⁻¹ * w * eb * (α * (Kb / eb * P))
      = (K0 ^ (1 - α) * Kb) * w * P * (α⁻¹ * α) * (eb * eb⁻¹) := by rw [div_eq_mul_inv]; ring
    _ = w * P := by rw [hKK, inv_mul_cancel₀ hα', mul_inv_cancel₀ he']; ring

lemma T2 (α K0 e w : ℝ) (hα : 0 < α) (hK0 : 0 < K0) (he0 : 0 < e) :
    |K0 ^ (1 - α) * α⁻¹ * w * e ^ (α - 1)| * (K0 / e) ^ α = K0 * α⁻¹ * (|w| / e) := by
  have h1 : 0 < K0 ^ (1 - α) := Real.rpow_pos_of_pos hK0 _
  have h2 : 0 < e ^ (α - 1) := Real.rpow_pos_of_pos he0 _
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos h1, abs_of_pos h2, abs_of_pos (inv_pos.mpr hα),
    Real.div_rpow hK0.le he0.le]
  have hK : K0 ^ (1 - α) * K0 ^ α = K0 := by
    rw [← Real.rpow_add hK0]; simp
  have he : e ^ (α - 1) / e ^ α = e⁻¹ := by
    rw [Real.rpow_sub he0, Real.rpow_one]; field_simp
  have he' : e ^ α ≠ 0 := (Real.rpow_pos_of_pos he0 _).ne'
  calc K0 ^ (1 - α) * α⁻¹ * |w| * e ^ (α - 1) * (K0 ^ α / e ^ α)
      = (K0 ^ (1 - α) * K0 ^ α) * α⁻¹ * |w| * (e ^ (α - 1) / e ^ α) := by field_simp
    _ = K0 * α⁻¹ * (|w| / e) := by rw [hK, he]; field_simp

lemma T3 (α K0 e w : ℝ) (hα : 0 < α) (hK0 : 0 < K0) (he0 : 0 < e) (he1 : e ≤ 1) :
    |K0 ^ (1 - α) * α⁻¹ * w * e ^ (α - 1)| ≤ K0 ^ (1 - α) * α⁻¹ * (|w| / e) := by
  have h1 : 0 < K0 ^ (1 - α) := Real.rpow_pos_of_pos hK0 _
  have h2 : 0 < e ^ (α - 1) := Real.rpow_pos_of_pos he0 _
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos h1, abs_of_pos h2, abs_of_pos (inv_pos.mpr hα)]
  have he : e ^ (α - 1) ≤ e⁻¹ := by
    rw [Real.rpow_sub he0, Real.rpow_one]
    have : e ^ α ≤ 1 := Real.rpow_le_one he0.le he1 hα.le
    rw [div_le_iff₀ he0, inv_mul_cancel₀ he0.ne']; exact this
  calc K0 ^ (1 - α) * α⁻¹ * |w| * e ^ (α - 1) ≤ K0 ^ (1 - α) * α⁻¹ * |w| * e⁻¹ := by gcongr
    _ = _ := by rw [div_eq_mul_inv]; ring

lemma T4 (α K0 e w : ℝ) (hα : 0 < α) (hK0 : 0 < K0) (he0 : 0 < e) :
    |K0 ^ (1 - α) * α⁻¹ * w * e ^ (α - 1)| * (K0 / e) ^ (α - 1) = α⁻¹ * |w| := by
  have h1 : 0 < K0 ^ (1 - α) := Real.rpow_pos_of_pos hK0 _
  have h2 : 0 < e ^ (α - 1) := Real.rpow_pos_of_pos he0 _
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos h1, abs_of_pos h2, abs_of_pos (inv_pos.mpr hα),
    Real.div_rpow hK0.le he0.le]
  have hKK := KK α K0 hK0
  have he' : e ^ (α - 1) ≠ 0 := (Real.rpow_pos_of_pos he0 _).ne'
  generalize K0 ^ (α - 1) = Kb at hKK ⊢
  generalize e ^ (α - 1) = eb at he' ⊢
  calc K0 ^ (1 - α) * α⁻¹ * |w| * eb * (Kb / eb)
      = (K0 ^ (1 - α) * Kb) * α⁻¹ * |w| * (eb * eb⁻¹) := by rw [div_eq_mul_inv]; ring
    _ = α⁻¹ * |w| := by rw [hKK, mul_inv_cancel₀ he']; ring

end PCQ

theorem solution (α : ℝ) (hα : 0 < α) :
    ∃ Cα : ℝ, ∀ K0 : ℝ, 0 < K0 → ∀ M : ℕ, 1 ≤ M →
      ∃ (K γ : Fin M → ℝ),
        (∀ l, K0 ≤ K l ∧ K l ≤ K0 * (M : ℝ) ^ 2) ∧
        (∀ u h : ℝ, 0 ≤ u → |h| ≤ K0 / 4 → |h - u| ≤ K0 / 4 →
          |∑ l, γ l * ((K l + h) ^ α - (K l + h - u) ^ α) - u| ≤ Cα * ((2 : ℝ) ^ M)⁻¹ * u) ∧
        ∑ l, |γ l| * K l ^ α ≤ Cα * K0 * (M : ℝ) ^ 2 ∧
        ∑ l, |γ l| ≤ Cα * K0 ^ (1 - α) * (M : ℝ) ^ 2 ∧
        ∑ l, |γ l| * K l ^ (α - 1) ≤ Cα * M := by
  obtain ⟨B, hB0, hB⟩ := PCQ.tail (α - 1)
  have hαi : 0 < α⁻¹ := inv_pos.mpr hα
  refine ⟨2 ^ 20 + 224 * B + 20 / α, ?_⟩
  generalize hCdef : (2 ^ 20 + 224 * B + 20 / α : ℝ) = C
  intro K0 hK0 M hM
  have hC20 : (2:ℝ) ^ 20 ≤ C := by
    have : 0 ≤ 20 / α := by positivity
    linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 224) hB0]
  have hC224 : 224 * B ≤ C := by
    have : 0 ≤ 20 / α := by positivity
    linarith [(by positivity : (0:ℝ) ≤ 2 ^ 20)]
  have hC20a : 20 / α ≤ C := by
    have : 0 ≤ 224 * B := by positivity
    linarith [(by positivity : (0:ℝ) ≤ 2 ^ 20)]
  have hC0 : 0 ≤ C := le_trans (by positivity) hC20
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hKp : 0 < K0 ^ (1 - α) := Real.rpow_pos_of_pos hK0 _
  by_cases hM20 : M < 20
  · refine ⟨fun _ => K0, fun _ => 0, ?_, ?_, ?_, ?_, ?_⟩
    · intro l; exact ⟨le_rfl, by nlinarith [mul_nonneg hK0.le (by nlinarith : (0:ℝ) ≤ (M:ℝ)^2 - 1)]⟩
    · intro u h hu _ _
      simp only [zero_mul, Finset.sum_const_zero, zero_sub, abs_neg, abs_of_nonneg hu]
      have h2 : (2:ℝ) ^ M ≤ 2 ^ 20 := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : 1 ≤ C * ((2:ℝ) ^ M)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; linarith
      nlinarith
    · simp only [abs_zero, zero_mul, Finset.sum_const_zero]; positivity
    · simp only [abs_zero, zero_mul, Finset.sum_const_zero]; positivity
    · simp only [abs_zero, zero_mul, Finset.sum_const_zero]; positivity
  · push_neg at hM20
    obtain ⟨q, hq⟩ : ∃ q, q = M / 5 := ⟨_, rfl⟩
    have hq4 : 4 ≤ q := by omega
    have hq5 : 5 * q ≤ M := by omega
    have hq6 : M ≤ 5 * q + 4 := by omega
    have hm1 : 1 ≤ 3 * q := by omega
    have hmM : 3 * q ≤ M := by omega
    have hmM' : ((3 * q : ℕ) : ℝ) ≤ M := by exact_mod_cast hmM
    have hm0 : (0:ℝ) < ((3 * q : ℕ) : ℝ) := by exact_mod_cast hm1
    set m := 3 * q with hm
    set e : ℕ → ℝ := fun n => Real.sin (PCQ.phi m n) ^ 2 with he
    set w : ℕ → ℝ := fun n => (-1:ℝ) ^ n * (Real.cos (PCQ.phi m n) / (m * Real.sin (PCQ.phi m n))) with hw
    have hMpos : (0:ℝ) < M := by linarith
    have he_pos : ∀ n < m, 0 < e n := fun n hn => by
      have := PCQ.sin_phi_pos m n hm1 hn; simp only [he]; positivity
    have he_le : ∀ n < m, e n ≤ 1 := fun n hn => by
      have := Real.sin_le_one (PCQ.phi m n); have := PCQ.sin_phi_pos m n hm1 hn
      simp only [he]; nlinarith
    have he_low : ∀ n < m, 1 / (M:ℝ) ^ 2 ≤ e n := fun n hn => by
      have h1 := PCQ.sin_low q M hq4 hq5 n hn
      simp only [he]
      rw [← one_div_pow]
      exact pow_le_pow_left₀ (by positivity) h1 2
    have hmom : ∀ n < m, ∑ k ∈ Finset.range m, w k * e k ^ n = if n = 0 then 1 else 0 := by
      intro n hn
      rw [← PCQ.quad m n hm1 hn]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [hw, he, pow_mul]
      rfl
    have hS1 : ∑ k ∈ Finset.range m, |w k| ≤ 2 * m := PCQ.sum_w_le m hm1
    have hS2 : ∑ k ∈ Finset.range m, |w k| / e k ≤ 16 * (m:ℝ) ^ 2 := PCQ.sum_w_div_le m hm1
    have hm2 : (m:ℝ) ^ 2 ≤ (M:ℝ) ^ 2 := by nlinarith
    set K : Fin M → ℝ := fun l => if l.val < m then K0 / e l.val else K0 with hK
    set γ : Fin M → ℝ := fun l =>
      if l.val < m then K0 ^ (1 - α) * α⁻¹ * w l.val * e l.val ^ (α - 1) else 0 with hγ
    have hKge : ∀ l, K0 ≤ K l := by
      intro l; simp only [hK]; split_ifs with h
      · rw [le_div_iff₀ (he_pos _ h)]; nlinarith [he_le _ h]
      · exact le_rfl
    refine ⟨K, γ, ?_, ?_, ?_, ?_, ?_⟩
    · intro l
      refine ⟨hKge l, ?_⟩
      simp only [hK]; split_ifs with h
      · rw [div_le_iff₀ (he_pos _ h)]
        have := he_low _ h
        rw [div_le_iff₀ (by positivity)] at this
        nlinarith
      · nlinarith [mul_nonneg hK0.le (by nlinarith : (0:ℝ) ≤ (M:ℝ)^2 - 1)]
    · intro u h hu hh hhu
      have hE : ∀ a : ℝ, |a| ≤ K0 / 4 →
          |∑ l, γ l * (α * (K l + a) ^ (α - 1)) - 1| ≤ C * ((2:ℝ) ^ M)⁻¹ := by
        intro a ha
        have hta : |a / K0| ≤ 1 / 4 := by
          rw [abs_div, abs_of_pos hK0, div_le_iff₀ hK0]; linarith
        have hterm : ∀ l : Fin M, γ l * (α * (K l + a) ^ (α - 1)) =
            if l.val < m then w l.val * (1 + e l.val * (a / K0)) ^ (α - 1) else 0 := by
          intro l
          by_cases h : l.val < m
          · simp only [hγ, hK, h, if_true]
            exact PCQ.T1 α K0 (e l.val) (w l.val) a hα hK0 (he_pos _ h) (he_le _ h) hta
          · simp [hγ, h]
        rw [Finset.sum_congr rfl (fun l _ => hterm l)]
        rw [PCQ.fin_sum M m hmM (fun n => w n * (1 + e n * (a / K0)) ^ (α - 1))]
        have h1 := hB m e w (by omega) (fun k hk => ⟨(he_pos k hk).le, he_le k hk⟩) hmom (a / K0) hta
        refine h1.trans ?_
        have hn := PCQ.numeric_bound q M hq6
        have hX : 2 * (m:ℝ) * (5/18:ℝ) ^ m ≤ 224 * ((2:ℝ) ^ M)⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
          calc 2 * (m:ℝ) * (5/18:ℝ) ^ m * 2 ^ M = (2:ℝ) ^ M * (2 * (m:ℝ) * (5/18:ℝ) ^ m) := by ring
            _ ≤ 224 := hn
        have hr : (0:ℝ) ≤ (5/18) ^ m := by positivity
        calc (B * ∑ k ∈ Finset.range m, |w k|) * (5/18:ℝ) ^ m
            ≤ (B * (2 * m)) * (5/18:ℝ) ^ m := by gcongr
          _ = B * (2 * (m:ℝ) * (5/18:ℝ) ^ m) := by ring
          _ ≤ B * (224 * ((2:ℝ) ^ M)⁻¹) := by gcongr
          _ = (224 * B) * ((2:ℝ) ^ M)⁻¹ := by ring
          _ ≤ C * ((2:ℝ) ^ M)⁻¹ := by gcongr
      exact PCQ.mvt_reduction α K0 hK0 M K γ hKge (C * ((2:ℝ) ^ M)⁻¹) hE u h hu hh hhu
    · have hterm : ∀ l : Fin M, |γ l| * K l ^ α =
          if l.val < m then K0 * α⁻¹ * (|w l.val| / e l.val) else 0 := by
        intro l
        by_cases h : l.val < m
        · simp only [hγ, hK, h, if_true]
          exact PCQ.T2 α K0 (e l.val) (w l.val) hα hK0 (he_pos _ h)
        · simp [hγ, h]
      rw [Finset.sum_congr rfl (fun l _ => hterm l),
        PCQ.fin_sum M m hmM (fun n => K0 * α⁻¹ * (|w n| / e n)), ← Finset.mul_sum]
      have h20 : 20 * α⁻¹ ≤ C := by rw [← div_eq_mul_inv]; exact hC20a
      have h3 : α⁻¹ * (16 * (m:ℝ) ^ 2) ≤ C * (M:ℝ) ^ 2 := by
        calc α⁻¹ * (16 * (m:ℝ) ^ 2) ≤ α⁻¹ * (20 * (M:ℝ) ^ 2) := by gcongr; nlinarith
          _ = (20 * α⁻¹) * (M:ℝ) ^ 2 := by ring
          _ ≤ C * (M:ℝ) ^ 2 := by gcongr
      calc K0 * α⁻¹ * ∑ n ∈ Finset.range m, |w n| / e n ≤ K0 * α⁻¹ * (16 * (m:ℝ) ^ 2) := by
            gcongr
        _ = K0 * (α⁻¹ * (16 * (m:ℝ) ^ 2)) := by ring
        _ ≤ K0 * (C * (M:ℝ) ^ 2) := by gcongr
        _ = C * K0 * (M:ℝ) ^ 2 := by ring
    · have hterm : ∀ l : Fin M, |γ l| ≤
          if l.val < m then K0 ^ (1 - α) * α⁻¹ * (|w l.val| / e l.val) else 0 := by
        intro l
        by_cases h : l.val < m
        · simp only [hγ, h, if_true]
          exact PCQ.T3 α K0 (e l.val) (w l.val) hα hK0 (he_pos _ h) (he_le _ h)
        · simp [hγ, h]
      refine (Finset.sum_le_sum (fun l _ => hterm l)).trans ?_
      rw [PCQ.fin_sum M m hmM (fun n => K0 ^ (1 - α) * α⁻¹ * (|w n| / e n)), ← Finset.mul_sum]
      have h20 : 20 * α⁻¹ ≤ C := by rw [← div_eq_mul_inv]; exact hC20a
      have h3 : α⁻¹ * (16 * (m:ℝ) ^ 2) ≤ C * (M:ℝ) ^ 2 := by
        calc α⁻¹ * (16 * (m:ℝ) ^ 2) ≤ α⁻¹ * (20 * (M:ℝ) ^ 2) := by gcongr; nlinarith
          _ = (20 * α⁻¹) * (M:ℝ) ^ 2 := by ring
          _ ≤ C * (M:ℝ) ^ 2 := by gcongr
      calc K0 ^ (1 - α) * α⁻¹ * ∑ n ∈ Finset.range m, |w n| / e n
          ≤ K0 ^ (1 - α) * α⁻¹ * (16 * (m:ℝ) ^ 2) := by gcongr
        _ = K0 ^ (1 - α) * (α⁻¹ * (16 * (m:ℝ) ^ 2)) := by ring
        _ ≤ K0 ^ (1 - α) * (C * (M:ℝ) ^ 2) := by gcongr
        _ = C * K0 ^ (1 - α) * (M:ℝ) ^ 2 := by ring
    · have hterm : ∀ l : Fin M, |γ l| * K l ^ (α - 1) =
          if l.val < m then α⁻¹ * |w l.val| else 0 := by
        intro l
        by_cases h : l.val < m
        · simp only [hγ, hK, h, if_true]
          exact PCQ.T4 α K0 (e l.val) (w l.val) hα hK0 (he_pos _ h)
        · simp [hγ, h]
      rw [Finset.sum_congr rfl (fun l _ => hterm l),
        PCQ.fin_sum M m hmM (fun n => α⁻¹ * |w n|), ← Finset.mul_sum]
      have h20 : 20 * α⁻¹ ≤ C := by rw [← div_eq_mul_inv]; exact hC20a
      calc α⁻¹ * ∑ n ∈ Finset.range m, |w n| ≤ α⁻¹ * (2 * m) := by gcongr
        _ ≤ α⁻¹ * (2 * M) := by gcongr
        _ = (2 * α⁻¹) * M := by ring
        _ ≤ C * M := by gcongr; linarith
