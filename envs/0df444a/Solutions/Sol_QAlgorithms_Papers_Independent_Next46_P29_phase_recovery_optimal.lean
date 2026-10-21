-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P29.phase_recovery_optimal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T15:23:20.001926+00:00
-- url     : https://prove2.me/submissions/89c4a587-ed58-41b5-a06a-d6fe27ff68fd

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29
noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff Matrix.Norms.L2Operator

open QAlgorithms QAlgorithms.Papers.Independent.Next46.P29

open QAlgorithms.Papers.Independent.Information100.P56 (IsIrreducible)

open QAlgorithms.Papers.Independent.Information100.P63 (mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P71 (IsSubchannel)

attribute [local instance] Classical.decEq Classical.propDecidable

theorem g61d_exp_int (k : ℤ) :
    (∫ θ in Set.Icc (0:ℝ) (2 * Real.pi), Complex.exp (-Complex.I * (k : ℂ) * (θ : ℂ))) =
      if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity)]
  split_ifs with hk
  · subst hk; simp
  · have hc : -Complex.I * (k : ℂ) ≠ 0 := by
      simp [Complex.I_ne_zero, hk]
    have := integral_exp_mul_complex (a := 0) (b := 2 * Real.pi) hc
    simp only [mul_assoc] at this ⊢
    rw [this]
    have h1 : Complex.exp (-Complex.I * ((k : ℂ) * ((2 * Real.pi : ℝ) : ℂ))) = 1 := by
      rw [Complex.exp_eq_one_iff]
      refine ⟨-k, ?_⟩
      push_cast; ring
    simp only [← mul_assoc] at h1 ⊢
    push_cast at h1 ⊢
    rw [h1]; simp

theorem g61d_integrable_exp (k : ℤ) :
    IntegrableOn (fun θ : ℝ => Complex.exp (-Complex.I * (k : ℂ) * (θ : ℂ)))
      (Set.Icc (0:ℝ) (2 * Real.pi)) :=
  (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc

theorem g61d_coord {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (c : ι × κ → ℂ) (i : ι) (j : κ) :
    (∑ p : ι × κ, c p • Matrix.single p.1 p.2 (1 : ℂ)) i j = c (i, j) := by
  rw [Matrix.sum_apply, Finset.sum_eq_single (i, j)]
  · simp
  · rintro ⟨a, b⟩ _ hne
    rw [Matrix.smul_apply, Matrix.single_apply]
    have : ¬ (a = i ∧ b = j) := fun h => hne (by rw [h.1, h.2])
    simp [this]
  · simp

theorem g61d_matrix_integral {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (f : ℝ → Matrix ι κ ℂ) (s : Set ℝ)
    (hf : ∀ i j, IntegrableOn (fun θ => f θ i j) s) (i : ι) (j : κ) :
    (∫ θ in s, f θ) i j = ∫ θ in s, f θ i j := by
  have hrep : ∀ θ, f θ = ∑ p : ι × κ, (f θ p.1 p.2) • Matrix.single p.1 p.2 (1 : ℂ) := by
    intro θ
    ext a b
    rw [g61d_coord]
  have hI : (∫ θ in s, f θ) =
      ∫ θ in s, ∑ p : ι × κ, (f θ p.1 p.2) • Matrix.single p.1 p.2 (1 : ℂ) := by
    congr 1; funext θ; exact hrep θ
  rw [hI, integral_finsetSum]
  · simp only [integral_smul_const]
    exact g61d_coord (fun p => ∫ θ in s, f θ p.1 p.2) i j
  · intro p _
    exact (hf p.1 p.2).smul_const _

theorem g61d_K_apply (N : ℕ) (θ : ℝ) (x : Fin (N + 1) × Fin 2) (b : Fin 2) :
    phaseOrbitKraus N θ x b = ((Real.sqrt (N + 1 : ℝ))⁻¹ : ℂ) *
      Complex.exp (-Complex.I * ((x.1.val + x.2.val : ℕ) : ℂ) * (θ : ℂ)) *
      (if x.2 = b then 1 else 0) := by
  obtain ⟨n, a⟩ := x
  simp only [phaseOrbitKraus, act, numberRotation, phaseKet, Matrix.mulVec_diagonal,
    Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    rw [show ((n.val + a.val : ℕ) : ℂ) = (n.val : ℂ) + (a.val : ℂ) by push_cast; ring]
    rw [show -Complex.I * ((n.val : ℂ) + (a.val : ℂ)) * (θ : ℂ) =
      -Complex.I * (n.val : ℂ) * (θ : ℂ) + -Complex.I * (a.val : ℂ) * (θ : ℂ) by ring,
      Complex.exp_add]
    try simp only [WithLp.ofLp_toLp]
    ring
  · simp

theorem g61d_conj_exp (k : ℕ) (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-Complex.I * (k : ℂ) * (θ : ℂ))) =
      Complex.exp (Complex.I * (k : ℂ) * (θ : ℂ)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal]

theorem g61d_sqrt_sq (N : ℕ) :
    ((Real.sqrt (N + 1 : ℝ))⁻¹ : ℂ) * ((Real.sqrt (N + 1 : ℝ))⁻¹ : ℂ) = ((N : ℂ) + 1)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast; ring

theorem g61d_encIntegrand (N : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ)
    (x y : Fin (N + 1) × Fin 2) :
    (phaseOrbitKraus N θ * X * (phaseOrbitKraus N θ)ᴴ) x y =
      X x.2 y.2 / ((N : ℂ) + 1) *
        Complex.exp (-Complex.I * ((((x.1.val + x.2.val : ℕ) : ℤ) - ((y.1.val + y.2.val : ℕ) : ℤ) : ℤ) : ℂ) * (θ : ℂ)) := by
  have hsq := g61d_sqrt_sq N
  have e : Complex.exp (-Complex.I * ((((x.1.val + x.2.val : ℕ) : ℤ) - ((y.1.val + y.2.val : ℕ) : ℤ) : ℤ) : ℂ) * (θ : ℂ))
      = Complex.exp (-Complex.I * ((x.1.val + x.2.val : ℕ) : ℂ) * (θ : ℂ)) *
        Complex.exp (Complex.I * ((y.1.val + y.2.val : ℕ) : ℂ) * (θ : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g61d_K_apply, Fin.sum_univ_two,
    star_mul', RCLike.star_def, g61d_conj_exp, Complex.conj_ofReal, map_inv₀]
  set A := Complex.exp (-Complex.I * ((x.1.val + x.2.val : ℕ) : ℂ) * (θ : ℂ))
  set B := Complex.exp (Complex.I * ((y.1.val + y.2.val : ℕ) : ℂ) * (θ : ℂ))
  set c := ((Real.sqrt (N + 1 : ℝ))⁻¹ : ℂ)
  obtain ⟨n, a⟩ := x
  obtain ⟨m, b⟩ := y
  rw [div_eq_mul_inv, ← hsq]
  fin_cases a <;> fin_cases b <;> simp <;> ring

theorem g61d_enc_apply (N : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) (x y : Fin (N + 1) × Fin 2) :
    phaseEncoding N X x y =
      if x.1.val + x.2.val = y.1.val + y.2.val then X x.2 y.2 / ((N : ℂ) + 1) else 0 := by
  unfold phaseEncoding phaseAverage
  rw [Matrix.smul_apply, g61d_matrix_integral]
  · simp_rw [g61d_encIntegrand]
    rw [integral_const_mul, g61d_exp_int]
    have h2 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    split_ifs with h1 h3 h3
    · rw [Complex.real_smul]; push_cast; field_simp
    · exfalso; apply h3; omega
    · exfalso; apply h1; omega
    · simp
  · intro i j
    simp_rw [g61d_encIntegrand]
    exact (g61d_integrable_exp _).const_mul _

theorem g61d_recIntegrand (N : ℕ) (Y : Matrix (Fin (N + 1) × Fin 2) (Fin (N + 1) × Fin 2) ℂ)
    (θ : ℝ) (b b' : Fin 2) :
    ((phaseOrbitKraus N θ)ᴴ * Y * phaseOrbitKraus N θ) b b' =
      ∑ n : Fin (N + 1), ∑ m : Fin (N + 1), Y (n, b) (m, b') / ((N : ℂ) + 1) *
        Complex.exp (-Complex.I * ((((m.val + b'.val : ℕ) : ℤ) - ((n.val + b.val : ℕ) : ℤ) : ℤ) : ℂ) * (θ : ℂ)) := by
  have hsq := g61d_sqrt_sq N
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g61d_K_apply,
    star_mul', RCLike.star_def, g61d_conj_exp, Complex.conj_ofReal, map_inv₀]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  have e : ∀ n m : Fin (N + 1), ∀ c d : Fin 2,
      Complex.exp (-Complex.I * ((((m.val + d.val : ℕ) : ℤ) - ((n.val + c.val : ℕ) : ℤ) : ℤ) : ℂ) * (θ : ℂ))
      = Complex.exp (Complex.I * ((n.val + c.val : ℕ) : ℂ) * (θ : ℂ)) *
        Complex.exp (-Complex.I * ((m.val + d.val : ℕ) : ℂ) * (θ : ℂ)) := by
    intro n m c d
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp only [e]
  fin_cases b <;> fin_cases b' <;> simp <;>
    refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_)) <;>
    rw [div_eq_mul_inv, ← hsq] <;> ring

theorem g61d_rec_apply (N : ℕ) (Y : Matrix (Fin (N + 1) × Fin 2) (Fin (N + 1) × Fin 2) ℂ)
    (b b' : Fin 2) :
    phaseRecovery N Y b b' =
      ∑ n : Fin (N + 1), ∑ m : Fin (N + 1),
        if n.val + b.val = m.val + b'.val then Y (n, b) (m, b') else 0 := by
  unfold phaseRecovery phaseAverage
  rw [Matrix.smul_apply, Matrix.smul_apply, g61d_matrix_integral]
  · simp_rw [g61d_recIntegrand]
    rw [integral_finsetSum]
    · simp_rw [integral_finsetSum _ (fun m _ => (g61d_integrable_exp _).const_mul _)]
      simp_rw [integral_const_mul, g61d_exp_int]
      simp only [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      refine Finset.sum_congr rfl (fun m _ => ?_)
      have h2 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      have hN : ((N : ℂ) + 1) ≠ 0 := by norm_cast
      split_ifs with h1 h3 h3
      · simp only [Complex.real_smul, smul_eq_mul]; push_cast; field_simp
      · exfalso; apply h3; omega
      · exfalso; apply h1; omega
      · simp
    · intro n _
      exact integrable_finsetSum _ (fun m _ => (g61d_integrable_exp _).const_mul _)
  · intro i j
    simp_rw [g61d_recIntegrand]
    exact integrable_finsetSum _ (fun n _ =>
      integrable_finsetSum _ (fun m _ => (g61d_integrable_exp _).const_mul _))

theorem g61d_sumfin (N : ℕ) (a t : ℕ) (c : ℂ) :
    (∑ n : Fin (N + 1), if n.val + a = t then c else 0) =
      if a ≤ t ∧ t - a ≤ N then c else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨t - a, by omega⟩]
    · simp; omega
    · intro n _ hn
      rw [if_neg]
      intro h'
      apply hn; ext; simp; omega
    · simp
  · apply Finset.sum_eq_zero
    intro n _
    rw [if_neg]
    omega

theorem g61d_branch_apply (N t : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) (x y : Fin (N + 1) × Fin 2) :
    phaseBranch N t X x y =
      if x.1.val + x.2.val = t ∧ y.1.val + y.2.val = t then X x.2 y.2 / ((N : ℂ) + 1) else 0 := by
  have hsq := g61d_sqrt_sq N
  simp only [phaseBranch, conjSuperop, numberProjector, Matrix.diagonal_mul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  simp only [Matrix.kroneckerMap_apply, pureDensity, Matrix.of_apply, phaseKet]
  simp
  by_cases hx : x.1.val + x.2.val = t <;> by_cases hy : y.1.val + y.2.val = t <;>
    simp [hx, hy] <;> rw [div_eq_mul_inv, ← hsq] <;> ring

theorem g61d_dec_conj (N t : ℕ) (Y : Matrix (Fin (N + 1) × Fin 2) (Fin (N + 1) × Fin 2) ℂ)
    (b b' : Fin 2) :
    conjSuperop (numberDecoder N t) Y b b' =
      ∑ n : Fin (N + 1), ∑ m : Fin (N + 1),
        if n.val + b.val = t ∧ m.val + b'.val = t then Y (n, b) (m, b') else 0 := by
  simp only [conjSuperop, Matrix.mul_apply, Matrix.conjTranspose_apply, numberDecoder,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases b <;> fin_cases b' <;> simp <;>
    refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_)) <;>
    split_ifs <;> simp_all

theorem g61d_double (N b b' t : ℕ) (v : ℂ) :
    (∑ n : Fin (N + 1), ∑ m : Fin (N + 1),
      if n.val + b = t ∧ m.val + b' = t then v else 0) =
      if (b ≤ t ∧ t - b ≤ N) ∧ (b' ≤ t ∧ t - b' ≤ N) then v else 0 := by
  simp_rw [ite_and]
  have h : ∀ n : Fin (N + 1), (∑ m : Fin (N + 1),
      if n.val + b = t then (if m.val + b' = t then v else 0) else 0) =
      if n.val + b = t then (if b' ≤ t ∧ t - b' ≤ N then v else 0) else 0 := by
    intro n; by_cases h1 : n.val + b = t
    · simp only [h1, if_true]; exact g61d_sumfin N b' t v
    · simp only [h1, if_false, Finset.sum_const_zero]
  simp_rw [h, g61d_sumfin]
  split_ifs <;> tauto

theorem g61d_sum_range_ite (N : ℕ) (p q : ℕ) (hp : p < N + 2) (v : ℂ) :
    (∑ t ∈ Finset.range (N + 2), if p = t ∧ q = t then v else 0) =
      if p = q then v else 0 := by
  rw [Finset.sum_eq_single p]
  · simp only [true_and]
    by_cases h : q = p
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  · intro t _ ht; rw [if_neg]; omega
  · intro h; exact absurd (Finset.mem_range.2 hp) h

theorem g61d_enc_branch (N : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    phaseEncoding N X = ∑ t ∈ Finset.range (N + 2), phaseBranch N t X := by
  ext x y
  rw [g61d_enc_apply, Matrix.sum_apply]
  simp_rw [g61d_branch_apply]
  rw [g61d_sum_range_ite N _ _ (by omega)]

theorem g61d_rec_dec (N : ℕ) (Y : Matrix (Fin (N + 1) × Fin 2) (Fin (N + 1) × Fin 2) ℂ) :
    phaseRecovery N Y = ∑ t ∈ Finset.range (N + 2), conjSuperop (numberDecoder N t) Y := by
  ext b b'
  rw [g61d_rec_apply, Matrix.sum_apply]
  simp_rw [g61d_dec_conj]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [g61d_sum_range_ite N _ _ (by omega)]

/-- the isometry `b ↦ ψ ⊗ |b⟩` -/
def g61d_V (N : ℕ) : Matrix (Fin (N + 1) × Fin 2) (Fin 2) ℂ :=
  fun x b => if x.2 = b then ((Real.sqrt (N + 1 : ℝ))⁻¹ : ℂ) else 0

theorem g61d_VXV (N : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    g61d_V N * X * (g61d_V N)ᴴ = (pureDensity (phaseKet N)).kronecker X := by
  have hsq := g61d_sqrt_sq N
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g61d_V, Fin.sum_univ_two,
    Matrix.kroneckerMap_apply, pureDensity, Matrix.of_apply, phaseKet]
  obtain ⟨n, a⟩ := x
  obtain ⟨m, b⟩ := y
  fin_cases a <;> fin_cases b <;> simp <;> ring

theorem g61d_VV (N : ℕ) : (g61d_V N)ᴴ * g61d_V N = 1 := by
  have hsq := g61d_sqrt_sq N
  ext b b'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g61d_V, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  fin_cases b <;> fin_cases b' <;> simp [Matrix.one_apply] <;>
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by positivity)] <;>
    push_cast <;> field_simp

theorem g61d_enc_channel (N : ℕ) : IsChannel (phaseEncoding N) := by
  refine ⟨N + 2, fun t => numberProjector N t.val * g61d_V N, ?_, ?_⟩
  · unfold IsKrausFamily
    have h1 : ∀ t : Fin (N + 2), (numberProjector N t.val * g61d_V N)ᴴ *
        (numberProjector N t.val * g61d_V N) =
        (g61d_V N)ᴴ * (numberProjector N t.val * g61d_V N) := by
      intro t
      have hP : (numberProjector N t.val)ᴴ * numberProjector N t.val = numberProjector N t.val := by
        simp only [numberProjector, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
        congr 1
        funext z
        split_ifs <;> simp_all
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (numberProjector N t.val)ᴴ, hP]
    simp_rw [h1, ← Matrix.mul_sum, ← Matrix.sum_mul]
    have h2 : ∑ t : Fin (N + 2), numberProjector N t.val = 1 := by
      ext x y
      rw [Matrix.sum_apply]
      simp only [numberProjector, Matrix.diagonal_apply]
      by_cases hxy : x = y
      · subst hxy
        simp only [if_true, Matrix.one_apply_eq]
        rw [Finset.sum_eq_single ⟨x.1.val + x.2.val, by omega⟩]
        · simp
        · intro t _ ht; rw [if_neg]; intro h; apply ht; ext; simp [h]
        · simp
      · simp [hxy, Matrix.one_apply_ne hxy]
    rw [h2, Matrix.one_mul, g61d_VV]
  · intro X
    unfold krausApply
    rw [g61d_enc_branch, ← Fin.sum_univ_eq_sum_range (fun t => phaseBranch N t X)]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [phaseBranch, conjSuperop, ← g61d_VXV, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

theorem g61d_rec_channel (N : ℕ) : IsChannel (phaseRecovery N) := by
  refine ⟨N + 2, fun t => numberDecoder N t.val, ?_, ?_⟩
  · unfold IsKrausFamily
    ext x y
    rw [Matrix.sum_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, numberDecoder, Fin.sum_univ_two]
    by_cases hxy : x = y
    · subst hxy
      rw [Matrix.one_apply_eq, Finset.sum_eq_single ⟨x.1.val + x.2.val, by omega⟩]
      · obtain ⟨n, a⟩ := x
        fin_cases a <;> simp
      · intro t _ ht
        obtain ⟨n, a⟩ := x
        have : ¬ (n.val + a.val = t.val) := fun h => ht (Fin.ext (by simp [h]))
        fin_cases a <;> simp_all
      · simp
    · rw [Matrix.one_apply_ne hxy]
      apply Finset.sum_eq_zero
      intro t _
      obtain ⟨n, a⟩ := x
      obtain ⟨m, b⟩ := y
      have key : ∀ c : Fin 2, ¬ ((a = c ∧ n.val + a.val = t.val) ∧ (b = c ∧ m.val + b.val = t.val)) := by
        rintro c ⟨⟨h1, h2⟩, h3, h4⟩
        apply hxy
        subst h1; subst h3
        have : n = m := Fin.ext (by omega)
        rw [this]
      have k0 := key 0
      have k1 := key 1
      split_ifs <;> simp_all
  · intro Y
    unfold krausApply
    rw [g61d_rec_dec, ← Fin.sum_univ_eq_sum_range (fun t => conjSuperop (numberDecoder N t) Y)]
    rfl

theorem g61d_count_le (N : ℕ) (v : ℂ) :
    (∑ m : Fin (N + 1), if m.val ≤ N then v else 0) = ((N : ℂ) + 1) * v := by
  have : ∀ m : Fin (N + 1), m.val ≤ N := fun m => by omega
  simp [this]

theorem g61d_count_lt (N : ℕ) (v : ℂ) :
    (∑ m : Fin (N + 1), if m.val < N then v else 0) = (N : ℂ) * v := by
  rw [Fin.sum_univ_castSucc]
  simp

theorem g61d_count_ge (N : ℕ) (v : ℂ) :
    (∑ m : Fin (N + 1), if 1 ≤ m.val then v else 0) = (N : ℂ) * v := by
  rw [Fin.sum_univ_succ]
  simp

/-- the operator blocks of the maximally entangled projector -/
def g61d_B (b a : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i i' => if i = b ∧ i' = a then (1 / 2 : ℂ) else 0

theorem g61d_Fe (Φ : Superop (Fin 2) (Fin 2)) :
    QuditFidelity.entanglementFidelity 2 (by decide) Φ =
      (1 / 2 : ℝ) * (∑ a : Fin 2, ∑ b : Fin 2, Φ (g61d_B b a) b a).re := by
  unfold QuditFidelity.entanglementFidelity effectProb
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply,
    finiteMaxEntangled, idTensorSuperop]
  have hc : ((Real.sqrt (Fintype.card (Fin 2) : ℝ))⁻¹ : ℂ) * (starRingEnd ℂ) ((Real.sqrt (Fintype.card (Fin 2) : ℝ))⁻¹ : ℂ) = 1 / 2 := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by positivity)]
    simp
  have hB : ∀ j i : Fin 2 × Fin 2, (Matrix.of fun i_1 i' =>
      (if j.1 = i_1 then ((Real.sqrt (Fintype.card (Fin 2) : ℝ))⁻¹ : ℂ) else 0) *
        (starRingEnd ℂ) (if i.1 = i' then ((Real.sqrt (Fintype.card (Fin 2) : ℝ))⁻¹ : ℂ) else 0)) =
      g61d_B j.1 i.1 := by
    intro j i
    ext x y
    simp only [g61d_B, Matrix.of_apply]
    have h22 : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 2⁻¹ := by
      rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; rfl
    by_cases h1 : j.1 = x <;> by_cases h2 : i.1 = y <;> simp [h1, h2, h22] <;> aesop
  simp only [hB]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  have hs2 : Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; norm_num
  simp [hs2]
  ring

theorem g61d_DE {M : ℕ} (N : ℕ) (K : Fin M → Matrix (Fin 2) (Fin (N + 1) × Fin 2) ℂ) (b a : Fin 2) :
    (krausApply K (phaseEncoding N (g61d_B b a))) b a =
      (∑ k : Fin M, ∑ n : Fin (N + 1), ∑ m : Fin (N + 1),
        (if n.val + b.val = m.val + a.val then
          K k b (n, b) * (starRingEnd ℂ) (K k a (m, a)) else 0)) / (2 * ((N : ℂ) + 1)) := by
  simp only [Finset.sum_div]
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    g61d_enc_apply, g61d_B, Matrix.of_apply, Finset.sum_mul, Fintype.sum_prod_type, Fin.sum_univ_two]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hN : (N : ℂ) + 1 ≠ 0 := by norm_cast
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  simp only [ite_and]
  split_ifs <;> subst_vars <;> simp only [Fin.val_zero, Fin.val_one, Fin.isValue, Fin.val_two] at * <;>
    first | (exfalso; omega) | (simp_all; done) | (simp only [RCLike.star_def]; field_simp; ring1) | done

theorem g61d_diag (N : ℕ) (f : Fin (N + 1) → Fin (N + 1) → ℂ) :
    (∑ n : Fin (N + 1), ∑ m : Fin (N + 1), if n.val + 0 = m.val + 0 then f n m else 0) =
      ∑ n, f n n := by
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Finset.sum_eq_single n]
  · simp
  · intro m _ hm; rw [if_neg]; intro h; apply hm; ext; omega
  · simp

theorem g61d_diag1 (N : ℕ) (f : Fin (N + 1) → Fin (N + 1) → ℂ) :
    (∑ n : Fin (N + 1), ∑ m : Fin (N + 1), if n.val + 1 = m.val + 1 then f n m else 0) =
      ∑ n, f n n := by
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Finset.sum_eq_single n]
  · simp
  · intro m _ hm; rw [if_neg]; intro h; apply hm; ext; omega
  · simp

theorem g61d_shiftA (N : ℕ) (f : Fin (N + 1) → Fin (N + 1) → ℂ) :
    (∑ n : Fin (N + 1), ∑ m : Fin (N + 1), if n.val + 0 = m.val + 1 then f n m else 0) =
      ∑ i : Fin N, f i.succ i.castSucc := by
  rw [Fin.sum_univ_succ]
  have h0 : (∑ m : Fin (N + 1), if (0 : Fin (N + 1)).val + 0 = m.val + 1 then f 0 m else 0) = 0 := by
    apply Finset.sum_eq_zero; intro m _; rw [if_neg]; simp
  rw [h0, zero_add]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i.castSucc]
  · simp
  · intro m _ hm; rw [if_neg]; intro h; apply hm; ext; simp at h ⊢; omega
  · simp

theorem g61d_shiftB (N : ℕ) (f : Fin (N + 1) → Fin (N + 1) → ℂ) :
    (∑ n : Fin (N + 1), ∑ m : Fin (N + 1), if n.val + 1 = m.val + 0 then f n m else 0) =
      ∑ i : Fin N, f i.castSucc i.succ := by
  rw [Finset.sum_comm, Fin.sum_univ_succ]
  have h0 : (∑ n : Fin (N + 1), if n.val + 1 = (0 : Fin (N + 1)).val + 0 then f n 0 else 0) = 0 := by
    apply Finset.sum_eq_zero; intro m _; rw [if_neg]; simp
  rw [h0, zero_add]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i.castSucc]
  · simp
  · intro m _ hm; rw [if_neg]; intro h; apply hm; ext; simp at h ⊢; omega
  · simp

theorem g61d_S (N : ℕ) (z : Fin 2 → Fin (N + 1) → ℂ) :
    (∑ a : Fin 2, ∑ b : Fin 2, ∑ n : Fin (N + 1), ∑ m : Fin (N + 1),
      if n.val + b.val = m.val + a.val then z b n * (starRingEnd ℂ) (z a m) else 0) =
      (∑ n, z 0 n * (starRingEnd ℂ) (z 0 n)) + (∑ n, z 1 n * (starRingEnd ℂ) (z 1 n)) +
      ((∑ i : Fin N, z 0 i.succ * (starRingEnd ℂ) (z 1 i.castSucc)) +
       (∑ i : Fin N, z 1 i.castSucc * (starRingEnd ℂ) (z 0 i.succ))) := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one]
  rw [g61d_diag, g61d_diag1, g61d_shiftA, g61d_shiftB]
  ring

theorem g61d_Sre (N : ℕ) (z : Fin 2 → Fin (N + 1) → ℂ) :
    (∑ a : Fin 2, ∑ b : Fin 2, ∑ n : Fin (N + 1), ∑ m : Fin (N + 1),
      if n.val + b.val = m.val + a.val then z b n * (starRingEnd ℂ) (z a m) else 0).re ≤
      (∑ n, Complex.normSq (z 0 n)) + (∑ n, Complex.normSq (z 1 n)) +
      ∑ i : Fin N, (Complex.normSq (z 0 i.succ) + Complex.normSq (z 1 i.castSucc)) := by
  rw [g61d_S]
  simp only [Complex.add_re, Complex.re_sum, Complex.mul_conj, Complex.ofReal_re]
  rw [← Finset.sum_add_distrib]
  have : ∀ i : Fin N, (z 0 i.succ * (starRingEnd ℂ) (z 1 i.castSucc)).re +
      (z 1 i.castSucc * (starRingEnd ℂ) (z 0 i.succ)).re ≤
      Complex.normSq (z 0 i.succ) + Complex.normSq (z 1 i.castSucc) := by
    intro i
    have h1 := Complex.normSq_nonneg (z 0 i.succ - z 1 i.castSucc)
    rw [Complex.normSq_sub] at h1
    have h2 : (z 1 i.castSucc * (starRingEnd ℂ) (z 0 i.succ)).re =
        (z 0 i.succ * (starRingEnd ℂ) (z 1 i.castSucc)).re := by
      rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
    linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => this i)
  rw [Finset.sum_add_distrib] at hs
  linarith

theorem g61d_col {M : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Fin M → Matrix (Fin 2) ι ℂ)
    (hK : IsKrausFamily K) (x : ι) (b : Fin 2) :
    ∑ k, Complex.normSq (K k b x) ≤ 1 := by
  have h := congrArg (fun A => (A x x).re) hK
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
    Complex.one_re, Complex.re_sum] at h
  have h' : ∀ k, ∑ j : Fin 2, (star (K k j x) * K k j x).re = ∑ j : Fin 2, Complex.normSq (K k j x) := by
    intro k
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]
  simp only [h'] at h
  rw [← h]
  refine Finset.sum_le_sum (fun k _ => ?_)
  exact Finset.single_le_sum (f := fun j => Complex.normSq (K k j x))
    (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ b)

theorem g61d_RE (N : ℕ) (rho : Matrix (Fin 2) (Fin 2) ℂ) :
      phaseRecovery N (phaseEncoding N rho) =
        ((N : ℝ) / (N + 1) : ℂ) • rho +
        ((1 : ℝ) / (N + 1) : ℂ) • dephasing rho := by
    have hN : ((N : ℂ) + 1) ≠ 0 := by norm_cast
    ext b b'
    rw [g61d_rec_apply]
    simp_rw [g61d_enc_apply]
    have hs : ∀ n m : Fin (N + 1),
        (if n.val + b.val = m.val + b'.val then
          (if (n, b).1.val + (n, b).2.val = (m, b').1.val + (m, b').2.val then
            rho (n, b).2 (m, b').2 / ((N : ℂ) + 1) else 0) else 0) =
        if n.val + b.val = m.val + b'.val then rho b b' / ((N : ℂ) + 1) else 0 := by
      intro n m
      split_ifs <;> simp_all
    simp_rw [hs]
    rw [Finset.sum_comm]
    simp_rw [g61d_sumfin]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, dephasing, Matrix.diagonal_apply]
    fin_cases b <;> fin_cases b' <;> simp
    · rw [g61d_count_le]; push_cast; field_simp
    · rw [g61d_count_lt]; push_cast; field_simp
    · rw [g61d_count_ge]; push_cast; field_simp
    · rw [g61d_count_le]; push_cast; field_simp

theorem solution (N : ℕ) :
    ∀ D : Superop (Fin (N + 1) × Fin 2) (Fin 2), IsChannel D →
      QuditFidelity.entanglementFidelity 2 (by decide) (D ∘ phaseEncoding N) ≤
        QuditFidelity.entanglementFidelity 2 (by decide)
          (phaseRecovery N ∘ phaseEncoding N) := by
  rintro D ⟨M, K, hK, hD⟩
  rw [g61d_Fe, g61d_Fe]
  have hNr : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  -- value of the right side
  have hR : (∑ a : Fin 2, ∑ b : Fin 2, (phaseRecovery N ∘ phaseEncoding N) (g61d_B b a) b a).re =
      (2 * N + 1) / (N + 1) := by
    have hc : (∑ a : Fin 2, ∑ b : Fin 2, (phaseRecovery N ∘ phaseEncoding N) (g61d_B b a) b a) =
        (((2 * N + 1) / (N + 1) : ℝ) : ℂ) := by
      simp only [Function.comp, g61d_RE]
      simp only [Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply, dephasing,
        Matrix.diagonal_apply, g61d_B, Matrix.of_apply, smul_eq_mul]
      simp
      push_cast
      field_simp
      ring
    rw [hc, Complex.ofReal_re]
  rw [hR]
  -- the left side
  simp only [Function.comp, hD, g61d_DE]
  have e1 : (∑ a : Fin 2, ∑ b : Fin 2, (∑ k : Fin M, ∑ n : Fin (N + 1), ∑ m : Fin (N + 1),
        (if n.val + b.val = m.val + a.val then
          K k b (n, b) * (starRingEnd ℂ) (K k a (m, a)) else 0)) / (2 * ((N : ℂ) + 1))) =
      (∑ k : Fin M, ∑ a : Fin 2, ∑ b : Fin 2, ∑ n : Fin (N + 1), ∑ m : Fin (N + 1),
        (if n.val + b.val = m.val + a.val then
          K k b (n, b) * (starRingEnd ℂ) (K k a (m, a)) else 0)) /
        ((2 * ((N : ℝ) + 1) : ℝ) : ℂ) := by
    push_cast
    simp only [← Finset.sum_div]
    congr 1
    exact (Finset.sum_congr rfl (fun a _ => Finset.sum_comm)).trans Finset.sum_comm
  rw [e1, Complex.div_ofReal_re, Complex.re_sum]
  have hk := fun k : Fin M => g61d_Sre N (fun b n => K k b (n, b))
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hk k)
  simp only [Finset.sum_add_distrib] at hsum
  have c1 : ∑ k : Fin M, ∑ n : Fin (N + 1), Complex.normSq (K k 0 (n, 0)) =
      ∑ n : Fin (N + 1), ∑ k, Complex.normSq (K k 0 (n, 0)) := Finset.sum_comm
  have c2 : ∑ k : Fin M, ∑ n : Fin (N + 1), Complex.normSq (K k 1 (n, 1)) =
      ∑ n : Fin (N + 1), ∑ k, Complex.normSq (K k 1 (n, 1)) := Finset.sum_comm
  have c3 : ∑ k : Fin M, ∑ i : Fin N, Complex.normSq (K k 0 (i.succ, 0)) =
      ∑ i : Fin N, ∑ k, Complex.normSq (K k 0 (i.succ, 0)) := Finset.sum_comm
  have c4 : ∑ k : Fin M, ∑ i : Fin N, Complex.normSq (K k 1 (i.castSucc, 1)) =
      ∑ i : Fin N, ∑ k, Complex.normSq (K k 1 (i.castSucc, 1)) := Finset.sum_comm
  have b1 : ∑ n : Fin (N + 1), ∑ k, Complex.normSq (K k 0 (n, 0)) ≤ N + 1 := by
    have := Finset.sum_le_sum (fun n (_ : n ∈ (Finset.univ : Finset (Fin (N + 1)))) =>
      g61d_col K hK (n, 0) 0)
    simpa using this
  have b2 : ∑ n : Fin (N + 1), ∑ k, Complex.normSq (K k 1 (n, 1)) ≤ N + 1 := by
    have := Finset.sum_le_sum (fun n (_ : n ∈ (Finset.univ : Finset (Fin (N + 1)))) =>
      g61d_col K hK (n, 1) 1)
    simpa using this
  have b3 : ∑ i : Fin N, ∑ k, Complex.normSq (K k 0 (i.succ, 0)) ≤ N := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
      g61d_col K hK (i.succ, 0) 0)
    simpa using this
  have b4 : ∑ i : Fin N, ∑ k, Complex.normSq (K k 1 (i.castSucc, 1)) ≤ N := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
      g61d_col K hK (i.castSucc, 1) 1)
    simpa using this
  have htot : (∑ k : Fin M, (∑ a : Fin 2, ∑ b : Fin 2, ∑ n : Fin (N + 1), ∑ m : Fin (N + 1),
        (if n.val + b.val = m.val + a.val then
          K k b (n, b) * (starRingEnd ℂ) (K k a (m, a)) else 0)).re) ≤ 4 * N + 2 := by
    linarith
  have h2 : (0:ℝ) < 2 * ((N:ℝ) + 1) := by positivity
  have : (∑ k : Fin M, (∑ a : Fin 2, ∑ b : Fin 2, ∑ n : Fin (N + 1), ∑ m : Fin (N + 1),
        (if n.val + b.val = m.val + a.val then
          K k b (n, b) * (starRingEnd ℂ) (K k a (m, a)) else 0)).re) / (2 * ((N : ℝ) + 1)) ≤
      (2 * N + 1) / (N + 1) := by
    rw [div_le_div_iff₀ h2 hNr]
    nlinarith
  linarith
