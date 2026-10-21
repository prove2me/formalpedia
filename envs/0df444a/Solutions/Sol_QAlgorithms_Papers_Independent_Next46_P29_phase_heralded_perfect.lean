-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P29.phase_heralded_perfect
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:30:39.58471+00:00
-- url     : https://prove2.me/submissions/eecc16e4-c337-4922-9216-f8995618f768

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29
noncomputable section

open MeasureTheory

open scoped Kronecker Matrix ComplexConjugate ComplexOrder Manifold ContDiff Matrix.Norms.L2Operator

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

theorem g62m_kraus_cp {I J ι : Type*} [Fintype I] [Fintype J] (s : Finset ι)
    (K : ι → Matrix J I ℂ) (L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (hL : ∀ X, L X = ∑ t ∈ s, K t * X * (K t)ᴴ) : Entanglement.IsCompletelyPositive L := by
  classical
  intro r Y hY
  have h : idTensorSuperop L Y =
      ∑ t ∈ s, ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ K t) * Y * ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ K t)ᴴ := by
    ext p q
    rw [Matrix.sum_apply]
    simp only [idTensorSuperop, Matrix.of_apply, hL, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Matrix.one_apply, Matrix.of_apply, Finset.sum_mul]
    simp only [star_mul', ite_mul, one_mul, zero_mul, mul_ite, mul_zero, star_zero]
    simp only [apply_ite (star : ℂ → ℂ), star_zero, mul_ite, mul_zero]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  exact Matrix.posSemidef_sum _ (fun t _ => hY.mul_mul_conjTranspose_same _)

theorem g62m_acc_eq (N : ℕ) (Y : Matrix (Fin (N + 1) × Fin 2) (Fin (N + 1) × Fin 2) ℂ) :
    phaseAccepted N Y = ∑ t ∈ (Finset.range (N + 2)).filter (fun t => 0 < t ∧ t < N + 1),
      numberDecoder N t * Y * (numberDecoder N t)ᴴ := by
  rw [phaseAccepted, Finset.sum_filter]; rfl

theorem g62m_acc_apply (N : ℕ) (Y : Matrix (Fin (N + 1) × Fin 2) (Fin (N + 1) × Fin 2) ℂ)
    (b b' : Fin 2) :
    phaseAccepted N Y b b' = ∑ t ∈ (Finset.range (N + 2)).filter (fun t => 0 < t ∧ t < N + 1),
      ∑ n : Fin (N + 1), ∑ m : Fin (N + 1),
        if n.val + b.val = t ∧ m.val + b'.val = t then Y (n, b) (m, b') else 0 := by
  rw [g62m_acc_eq, Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  exact g61d_dec_conj N t Y b b'

def g62m_L (N : ℕ) : Matrix (Fin (N + 1) × Fin 2) (Fin (N + 1) × Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := phaseAccepted N
  map_add' X Y := by
    simp only [g62m_acc_eq, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [g62m_acc_eq, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply]

theorem solution (N : ℕ) :
    IsSubchannel (phaseAccepted N) ∧
    ∀ rho, IsDensityMatrix rho →
      phaseAccepted N (phaseEncoding N rho) = ((N : ℝ) / (N + 1) : ℂ) • rho ∧
      (phaseAccepted N (phaseEncoding N rho)).trace.re = (N : ℝ) / (N + 1) := by
  have hN : ((N : ℂ) + 1) ≠ 0 := by norm_cast
  have hfilt : ((Finset.range (N + 2)).filter (fun t => 0 < t ∧ t < N + 1)).card = N := by
    have : (Finset.range (N + 2)).filter (fun t => 0 < t ∧ t < N + 1) = Finset.Ioo 0 (N + 1) := by
      ext t; simp; omega
    rw [this]; simp
  have key : ∀ rho : Matrix (Fin 2) (Fin 2) ℂ,
      phaseAccepted N (phaseEncoding N rho) = ((N : ℝ) / (N + 1) : ℂ) • rho := by
    intro rho
    ext b b'
    rw [g62m_acc_apply]
    simp_rw [g61d_enc_apply]
    have hs : ∀ t, ∀ n m : Fin (N + 1),
        (if n.val + b.val = t ∧ m.val + b'.val = t then
          (if (n, b).1.val + (n, b).2.val = (m, b').1.val + (m, b').2.val then
            rho (n, b).2 (m, b').2 / ((N : ℂ) + 1) else 0) else 0) =
        if n.val + b.val = t ∧ m.val + b'.val = t then rho b b' / ((N : ℂ) + 1) else 0 := by
      intro t n m
      split_ifs <;> simp_all
    simp_rw [hs, g61d_double]
    have hc : ∀ t ∈ (Finset.range (N + 2)).filter (fun t => 0 < t ∧ t < N + 1),
        (if (b.val ≤ t ∧ t - b.val ≤ N) ∧ (b'.val ≤ t ∧ t - b'.val ≤ N) then
          rho b b' / ((N : ℂ) + 1) else 0) = rho b b' / ((N : ℂ) + 1) := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      have hb := b.isLt; have hb' := b'.isLt
      rw [if_pos (by omega)]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, hfilt, Matrix.smul_apply, nsmul_eq_mul,
      smul_eq_mul]
    push_cast
    field_simp
  refine ⟨⟨g62m_L N, fun X => rfl, ?_, ?_⟩, ?_⟩
  · exact g62m_kraus_cp _ _ _ (fun X => g62m_acc_eq N X)
  · intro X hX
    have htr : (phaseAccepted N X).trace = ∑ t ∈ (Finset.range (N + 2)).filter (fun t => 0 < t ∧ t < N + 1),
        ∑ b : Fin 2, ∑ n : Fin (N + 1), if n.val + b.val = t then X (n, b) (n, b) else 0 := by
      simp only [Matrix.trace, Matrix.diag, g62m_acc_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun b _ => ?_))
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [Finset.sum_eq_single n]
      · simp
      · intro m _ hmn; rw [if_neg]; intro h; apply hmn; ext; omega
      · simp
    have h2 : (phaseAccepted N X).trace = ∑ a : Fin (N + 1) × Fin 2,
        if 0 < a.1.val + a.2.val ∧ a.1.val + a.2.val < N + 1 then X a a else 0 := by
      rw [htr, Fintype.sum_prod_type_right, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_filter, Finset.mem_range]
      have hb := b.isLt; have hn := n.isLt
      by_cases h : 0 < n.val + b.val ∧ n.val + b.val < N + 1
      · rw [if_pos ⟨by omega, h⟩, if_pos h]
      · rw [if_neg (fun h' => h h'.2), if_neg h]
    rw [h2, Matrix.trace, Complex.re_sum, Complex.re_sum]
    apply Finset.sum_le_sum
    intro a _
    split_ifs
    · exact le_rfl
    · exact (Complex.le_def.1 (hX.diag_nonneg (i := a))).1
  · intro rho hrho
    refine ⟨key rho, ?_⟩
    rw [key, Matrix.trace_smul, hrho.2]
    have e : ((N : ℂ) / ((N : ℂ) + 1)) = (((N : ℝ) / ((N : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
    simp
    rw [e, Complex.ofReal_re]
