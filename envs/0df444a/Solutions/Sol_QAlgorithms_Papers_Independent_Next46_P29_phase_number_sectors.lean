-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P29.phase_number_sectors
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:46:01.606503+00:00
-- url     : https://prove2.me/submissions/45ca357d-d11a-4e04-89e9-b3e417a581c7

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

theorem solution (N : ℕ) (rho : Matrix (Fin 2) (Fin 2) ℂ)
    (hrho : IsDensityMatrix rho) :
    phaseEncoding N rho = ∑ t ∈ Finset.range (N + 2), phaseBranch N t rho ∧
    (∀ t, t ≤ N + 1 →
      (phaseBranch N t rho).trace =
        if t = 0 then rho 0 0 / (N + 1 : ℂ)
        else if t = N + 1 then rho 1 1 / (N + 1 : ℂ)
        else (N + 1 : ℂ)⁻¹) ∧
    (∀ t, t ≤ N + 1 →
      phaseDecodedBranch N t rho =
        if t = 0 then (rho 0 0 / (N + 1 : ℂ)) • Matrix.single 0 0 1
        else if t = N + 1 then (rho 1 1 / (N + 1 : ℂ)) • Matrix.single 1 1 1
        else (N + 1 : ℂ)⁻¹ • rho) ∧
    (∀ Y, phaseRecovery N Y = ∑ t ∈ Finset.range (N + 2),
      conjSuperop (numberDecoder N t) Y) := by
  have htr : rho 0 0 + rho 1 1 = 1 := by
    have := hrho.2; rw [Matrix.trace_fin_two] at this; exact this
  have hN : ((N : ℂ) + 1) ≠ 0 := by norm_cast
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x y
    rw [g61d_enc_apply, Matrix.sum_apply]
    simp_rw [g61d_branch_apply]
    rw [g61d_sum_range_ite N _ _ (by omega)]
  · intro t ht
    simp only [Matrix.trace, Matrix.diag, g61d_branch_apply, and_self]
    rw [Fintype.sum_prod_type, Finset.sum_comm, Fin.sum_univ_two]
    dsimp only
    rw [g61d_sumfin, g61d_sumfin]
    simp only [Fin.val_zero, Fin.val_one]
    by_cases h0 : t = 0
    · subst h0; simp
    · by_cases h1 : t = N + 1
      · subst h1; simp
      · rw [if_pos (by omega), if_pos (by omega), if_neg h0, if_neg h1, ← add_div, htr,
          one_div]
  · intro t ht
    ext b b'
    rw [phaseDecodedBranch, g61d_dec_conj]
    simp_rw [g61d_branch_apply]
    have hs : ∀ n m : Fin (N + 1),
        (if n.val + b.val = t ∧ m.val + b'.val = t then
          (if (n, b).1.val + (n, b).2.val = t ∧ (m, b').1.val + (m, b').2.val = t then
            rho (n, b).2 (m, b').2 / ((N : ℂ) + 1) else 0) else 0) =
        if n.val + b.val = t ∧ m.val + b'.val = t then rho b b' / ((N : ℂ) + 1) else 0 := by
      intro n m
      split_ifs <;> simp_all
    simp_rw [hs]
    rw [g61d_double]
    by_cases h0 : t = 0
    · subst h0
      fin_cases b <;> fin_cases b' <;> simp
    · by_cases h1 : t = N + 1
      · subst h1
        fin_cases b <;> fin_cases b' <;> simp
      · rw [if_neg h0, if_neg h1, Matrix.smul_apply, smul_eq_mul, if_pos (by omega)]
        field_simp
  · intro Y
    ext b b'
    rw [g61d_rec_apply, Matrix.sum_apply]
    simp_rw [g61d_dec_conj]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [g61d_sum_range_ite N _ _ (by omega)]
