-- Prove2me | solution 1 for SmaleNinth.khachiyan_ellipsoid_decides
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T16:20:05.921226+00:00
-- url     : https://prove2.me/submissions/8ca9a703-6e97-429b-ba07-7651785a07ca

import Theorems.Thm_LinearOptimization_ellipsoid_method_correct
import Theorems.Thm_SmaleNinth_khachiyan_perturbation_bounds
import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_LinearOptimization_EllipsoidMethod
import Definitions.Def_SmaleNinth_Khachiyan

/-!
Khachiyan's theorem in iteration form, assembled from the platform's
ellipsoid correctness theorem (Bertsimas–Tsitsiklis Theorem 8.2) and the
perturbation bounds of the Khachiyan module.
-/

open Matrix LinearOptimization MeasureTheory

namespace SmaleNinth

/-! ### Positivity of the Khachiyan constants -/

lemma khachiyanEps_pos (n U : ℕ) (hU : 1 ≤ U) : 0 < khachiyanEps n U := by
  unfold khachiyanEps
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  positivity

lemma khachiyanBox_pos (n U : ℕ) : 0 < khachiyanBox n U := by
  unfold khachiyanBox; positivity

lemma one_le_khachiyanBox_sub (n U : ℕ) (hU : 1 ≤ U) :
    1 ≤ (n.factorial : ℝ) * (U : ℝ) ^ n := by
  have h1 : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr n.factorial_ne_zero
  have h2 : (1 : ℝ) ≤ (U : ℝ) ^ n := one_le_pow₀ (by exact_mod_cast hU)
  nlinarith

lemma khachiyanRadius_pos (n U : ℕ) : 0 < khachiyanRadius n U := by
  unfold khachiyanRadius; have := khachiyanBox_pos n U; positivity

lemma khachiyanVolLB_pos (n U : ℕ) (hn : 1 ≤ n) (hU : 1 ≤ U) :
    0 < khachiyanVolLB n U := by
  unfold khachiyanVolLB
  have := khachiyanEps_pos n U hU
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  positivity

/-! ### Volume of the initial ball -/

/-- The ball `E(0, r²I)` lies in the cube `[-r, r]ⁿ`, whose volume is `(2r)ⁿ`. -/
lemma volume_ellipsoidBall_le (n : ℕ) (r : ℝ) (hr : 0 < r) :
    volume (ellipsoidBall (0 : Fin n → ℝ) r) ≤ ENNReal.ofReal ((2 * r) ^ n) := by
  have hinv : (r ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹
      = (r ^ 2)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      inv_mul_cancel₀ (by positivity), one_smul]
  have hsub : ellipsoidBall (0 : Fin n → ℝ) r ⊆
      Set.Icc (fun _ => -r) (fun _ => r) := by
    intro x hx
    simp only [ellipsoidBall, ellipsoid, Set.mem_setOf_eq, sub_zero, hinv,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at hx
    have hxx : x ⬝ᵥ x ≤ r ^ 2 := by
      rwa [inv_mul_le_iff₀ (by positivity), mul_one] at hx
    have hi : ∀ i, x i ^ 2 ≤ r ^ 2 := by
      intro i
      calc x i ^ 2 = x i * x i := by ring
        _ ≤ ∑ j, x j * x j :=
          Finset.single_le_sum (f := fun j => x j * x j)
            (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
        _ = x ⬝ᵥ x := rfl
        _ ≤ r ^ 2 := hxx
    rw [Set.mem_Icc]
    exact ⟨fun i => (abs_le_of_sq_le_sq' (hi i) hr.le).1,
      fun i => (abs_le_of_sq_le_sq' (hi i) hr.le).2⟩
  calc volume (ellipsoidBall (0 : Fin n → ℝ) r)
      ≤ volume (Set.Icc (fun _ : Fin n => -r) (fun _ => r)) := measure_mono hsub
    _ = ∏ _i : Fin n, ENNReal.ofReal (r - -r) := Real.volume_Icc_pi
    _ = ENNReal.ofReal ((2 * r) ^ n) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ENNReal.ofReal_pow (by linarith)]
      congr 2; ring

/-! ### The logarithm estimate -/

/-- `log U ≤ ⌊log₂ U⌋ + 1`. -/
lemma log_le_natLog_add_one (U : ℕ) (hU : 1 ≤ U) :
    Real.log U ≤ (Nat.log 2 U : ℝ) + 1 := by
  have h1 : (U : ℝ) < 2 ^ (Nat.log 2 U + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) U
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num); linarith
  calc Real.log U ≤ Real.log (2 ^ (Nat.log 2 U + 1)) := Real.log_le_log hU' h1.le
    _ = ((Nat.log 2 U : ℝ) + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
    _ ≤ ((Nat.log 2 U : ℝ) + 1) * 1 := by gcongr
    _ = _ := by ring

/-- `log (k!) ≤ k · log k ≤ k (k − 1)` — crude but polynomial. -/
lemma log_factorial_le (k : ℕ) : Real.log (k.factorial : ℝ) ≤ (k : ℝ) * k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  calc Real.log (k.factorial : ℝ) ≤ Real.log ((k : ℝ) ^ k) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast Nat.factorial_le_pow k
    _ = k * Real.log k := Real.log_pow _ _
    _ ≤ k * k := by
        gcongr
        have := Real.log_le_sub_one_of_pos hk'; linarith

/-- The ratio `V / v'` fed to the iteration budget, in closed form. -/
lemma khachiyan_ratio_eq (n U : ℕ) (hn : 1 ≤ n) (hU : 1 ≤ U) :
    (2 * khachiyanRadius n U) ^ n / (khachiyanVolLB n U / 2)
      = 2 * (2 * khachiyanRadius n U * (n * U) / khachiyanEps n U) ^ n := by
  have hε := khachiyanEps_pos n U hU
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  unfold khachiyanVolLB
  rw [div_pow, div_pow, mul_pow, mul_pow]
  field_simp
  ring

/-- The base of the power, bounded by an explicit product. -/
lemma khachiyan_base_le (n U : ℕ) (hU : 1 ≤ U) :
    2 * khachiyanRadius n U * (n * U) / khachiyanEps n U
      ≤ 8 * n * ((n : ℝ) + 1) ^ 2 * ((n + 1).factorial : ℝ) * (n.factorial : ℝ)
          * (U : ℝ) ^ (2 * n + 2) := by
  have hε := khachiyanEps_pos n U hU
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  have hbox : khachiyanBox n U ≤ 2 * ((n.factorial : ℝ) * (U : ℝ) ^ n) := by
    unfold khachiyanBox
    have := one_le_khachiyanBox_sub n U hU
    linarith
  rw [div_le_iff₀ hε]
  unfold khachiyanRadius khachiyanEps
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hfac : (0 : ℝ) < (n + 1).factorial := by positivity
  have hfac' : (0 : ℝ) < n.factorial := by positivity
  -- clear the denominator inside `khachiyanEps`
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  have key : 2 * (((n : ℝ) + 1) * khachiyanBox n U) * (n * U)
      * (2 * ((n : ℝ) + 1) * ((n + 1).factorial : ℝ) * (U : ℝ) ^ (n + 1))
      ≤ 2 * (((n : ℝ) + 1) * (2 * ((n.factorial : ℝ) * (U : ℝ) ^ n))) * (n * U)
      * (2 * ((n : ℝ) + 1) * ((n + 1).factorial : ℝ) * (U : ℝ) ^ (n + 1)) := by
    gcongr
  refine le_of_le_of_eq (le_trans (le_of_eq ?_) key) ?_
  · ring
  · rw [show 2 * n + 2 = (n + 1) + (n + 1) by ring, pow_add]; ring

/-- The logarithm of the base is bounded by a polynomial in `n` and `⌊log₂ U⌋`. -/
lemma log_khachiyan_base_le (n U : ℕ) (hn : 1 ≤ n) (hU : 1 ≤ U) :
    Real.log (2 * khachiyanRadius n U * (n * U) / khachiyanEps n U)
      ≤ 2 * (n : ℝ) ^ 2 + 7 * n + 9 + (2 * n + 2) * (Nat.log 2 U : ℝ) := by
  have hε := khachiyanEps_pos n U hU
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  have hr := khachiyanRadius_pos n U
  have hfac : (0 : ℝ) < (n + 1).factorial := by positivity
  have hfac' : (0 : ℝ) < n.factorial := by positivity
  have hpos : 0 < 2 * khachiyanRadius n U * (n * U) / khachiyanEps n U := by positivity
  calc Real.log (2 * khachiyanRadius n U * (n * U) / khachiyanEps n U)
      ≤ Real.log (8 * n * ((n : ℝ) + 1) ^ 2 * ((n + 1).factorial : ℝ) * (n.factorial : ℝ)
          * (U : ℝ) ^ (2 * n + 2)) :=
        Real.log_le_log hpos (khachiyan_base_le n U hU)
    _ = Real.log 8 + Real.log n + 2 * Real.log ((n : ℝ) + 1)
          + Real.log ((n + 1).factorial : ℝ) + Real.log (n.factorial : ℝ)
          + (2 * n + 2) * Real.log U := by
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_pow, Real.log_pow]
        push_cast; ring
    _ ≤ 7 + ((n : ℝ) - 1) + 2 * n + ((n : ℝ) + 1) * ((n : ℝ) + 1) + (n : ℝ) * n
          + (2 * n + 2) * ((Nat.log 2 U : ℝ) + 1) := by
        have h8 : Real.log 8 ≤ 7 := by
          have := Real.log_le_sub_one_of_pos (x := 8) (by norm_num); linarith
        have hln : Real.log n ≤ (n : ℝ) - 1 := Real.log_le_sub_one_of_pos hn'
        have hln1 : Real.log ((n : ℝ) + 1) ≤ n := by
          have := Real.log_le_sub_one_of_pos (x := (n : ℝ) + 1) (by positivity); linarith
        have hf1 : Real.log ((n + 1).factorial : ℝ) ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1) := by
          have := log_factorial_le (n + 1); push_cast at this; exact this
        have hf2 : Real.log (n.factorial : ℝ) ≤ (n : ℝ) * n := log_factorial_le n
        have hlU := log_le_natLog_add_one U hU
        have h2n : (0 : ℝ) ≤ 2 * n + 2 := by positivity
        have := mul_le_mul_of_nonneg_left hlU h2n
        linarith
    _ = _ := by ring

/-- The polynomial bookkeeping, done over `ℕ`. -/
lemma khachiyan_poly_bound (n ℓ : ℕ) (hn : 2 ≤ n) :
    2 * (n + 1) * (1 + n * (2 * n ^ 2 + 7 * n + 9 + (2 * n + 2) * ℓ))
      ≤ 10 ^ 6 * (n + 2) ^ 4 * (ℓ + n + 2) := by
  nlinarith [Nat.zero_le ℓ, Nat.zero_le n, Nat.mul_le_mul hn hn,
    Nat.zero_le (n * ℓ), Nat.zero_le (n ^ 4 * ℓ), Nat.zero_le (n ^ 5)]

/-- The iteration budget is polynomially bounded. -/
lemma khachiyanIterations_le (n U : ℕ) (hn : 2 ≤ n) (hU : 1 ≤ U) :
    khachiyanIterations n U ≤ 10 ^ 6 * (n + 2) ^ 4 * (Nat.log 2 U + n + 2) := by
  have hn1 : 1 ≤ n := by omega
  unfold khachiyanIterations
  rw [Nat.ceil_le]
  set ℓ := Nat.log 2 U with hℓ
  have hlog : Real.log ((2 * khachiyanRadius n U) ^ n / (khachiyanVolLB n U / 2))
      ≤ 1 + n * (2 * (n : ℝ) ^ 2 + 7 * n + 9 + (2 * n + 2) * (ℓ : ℝ)) := by
    have hε := khachiyanEps_pos n U hU
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
    have hU' : (0 : ℝ) < U := by exact_mod_cast hU
    have hr := khachiyanRadius_pos n U
    have hbase : 0 < 2 * khachiyanRadius n U * (n * U) / khachiyanEps n U := by positivity
    rw [khachiyan_ratio_eq n U hn1 hU, Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num); linarith
    have := mul_le_mul_of_nonneg_left (log_khachiyan_base_le n U hn1 hU) hn'.le
    linarith
  have hnn : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by positivity
  calc 2 * ((n : ℝ) + 1) * Real.log ((2 * khachiyanRadius n U) ^ n / (khachiyanVolLB n U / 2))
      ≤ 2 * ((n : ℝ) + 1) * (1 + n * (2 * (n : ℝ) ^ 2 + 7 * n + 9 + (2 * n + 2) * (ℓ : ℝ))) :=
        mul_le_mul_of_nonneg_left hlog hnn
    _ = ((2 * (n + 1) * (1 + n * (2 * n ^ 2 + 7 * n + 9 + (2 * n + 2) * ℓ)) : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ ((10 ^ 6 * (n + 2) ^ 4 * (ℓ + n + 2) : ℕ) : ℝ) := by
        exact_mod_cast khachiyan_poly_bound n ℓ hn

end SmaleNinth

open SmaleNinth

theorem solution {m n : ℕ} (U : ℕ) (hU : 1 ≤ U)
    (hn : 2 ≤ n) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ))
    (x : ℕ → Fin n → ℝ) (D : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hx0 : x 0 = 0)
    (hD0 : D 0 = (khachiyanRadius n U) ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hrun : IsEllipsoidRun (khachiyanSystemA A) (khachiyanSystemb n U b)
      x D (khachiyanIterations n U)) :
    ((∃ t ≤ khachiyanIterations n U,
        x t ∈ polyhedron (khachiyanSystemA A) (khachiyanSystemb n U b)) ↔
      (polyhedron (A.map (Int.cast : ℤ → ℝ))
        (fun i => (b i : ℝ))).Nonempty) ∧
    khachiyanIterations n U ≤
      10 ^ 6 * (n + 2) ^ 4 * (Nat.log 2 U + n + 2) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hequiv, hbdd, hcover, hvol⟩ :=
    SmaleNinth.khachiyan_perturbation_bounds U hU hn1 A b hA hb
  have hvpos := khachiyanVolLB_pos n U hn1 hU
  refine ⟨⟨?_, ?_⟩, khachiyanIterations_le n U hn hU⟩
  · rintro ⟨t, -, ht⟩
    exact hequiv.mpr ⟨x t, ht⟩
  · intro hne
    by_contra hmiss
    have hmiss' : ∀ t < khachiyanIterations n U,
        x t ∉ polyhedron (khachiyanSystemA A) (khachiyanSystemb n U b) :=
      fun t ht hx => hmiss ⟨t, ht.le, hx⟩
    have hne' := hequiv.mp hne
    have hdim : polyhedron (khachiyanSystemA A) (khachiyanSystemb n U b) = ∅ ∨
        IsFullDimensional (polyhedron (khachiyanSystemA A) (khachiyanSystemb n U b)) := by
      rcases (polyhedron (khachiyanSystemA A) (khachiyanSystemb n U b)).eq_empty_or_nonempty
        with h | h
      · exact Or.inl h
      · right
        exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hvpos) (hvol h)
    have hvol' : polyhedron (khachiyanSystemA A) (khachiyanSystemb n U b) ≠ ∅ →
        ENNReal.ofReal (khachiyanVolLB n U / 2) <
          volume (polyhedron (khachiyanSystemA A) (khachiyanSystemb n U b)) := by
      intro hne''
      calc ENNReal.ofReal (khachiyanVolLB n U / 2)
          < ENNReal.ofReal (khachiyanVolLB n U) := by
            rw [ENNReal.ofReal_lt_ofReal_iff hvpos]; linarith
        _ ≤ _ := hvol (Set.nonempty_iff_ne_empty.mpr hne'')
    have hempty := LinearOptimization.ellipsoid_method_correct hn
      (khachiyanSystemA A) (khachiyanSystemb n U b) 0
      (khachiyanRadius n U) (khachiyanVolLB n U / 2) ((2 * khachiyanRadius n U) ^ n)
      (khachiyanRadius_pos n U) (by positivity) hbdd hdim hcover
      (volume_ellipsoidBall_le n _ (khachiyanRadius_pos n U)) hvol'
      (khachiyanIterations n U) rfl x D hx0 hD0 hrun
      hmiss'
    exact hne'.ne_empty hempty
