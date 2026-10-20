-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P40.recoveryTraceObjective
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T01:15:05.341703+00:00
-- url     : https://prove2.me/submissions/f7c22f72-73b9-4c10-8a70-4d8339931acb

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

lemma g52e_L1 {h k : ℕ} (M : Matrix (Fin k) (Fin h) ℂ)
    (X : Matrix (Fin h × Fin h) (Fin h × Fin h) ℂ) (x : Fin h) (y : Fin k) (q : Fin h × Fin h) :
    (Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) (M.map (fun z => conj z)) * X) (x, y) q =
      ∑ z, conj (M y z) * X (x, z) q := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single x]
  · simp [Matrix.kronecker, Matrix.one_apply]
  · intro u _ hu
    refine Finset.sum_eq_zero fun z _ => ?_
    simp [Matrix.kronecker, Matrix.one_apply, Ne.symm hu]
  · simp

lemma g52e_L2 {h k : ℕ} (M : Matrix (Fin k) (Fin h) ℂ)
    (Y : Matrix (Fin h × Fin k) (Fin h × Fin h) ℂ) (q : Fin h × Fin k) (x : Fin h) (y : Fin k) :
    (Y * Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) Mᵀ) q (x, y) =
      ∑ z, Y q (x, z) * M y z := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single x]
  · simp [Matrix.kronecker, Matrix.one_apply]
  · intro u _ hu
    refine Finset.sum_eq_zero fun z _ => ?_
    simp [Matrix.kronecker, Matrix.one_apply, hu]
  · simp

lemma g52e_L3 {h k : ℕ} (M : Matrix (Fin k) (Fin h) ℂ)
    (X : Matrix (Fin h × Fin k) (Fin h × Fin k) ℂ) (o a : Fin h) (q : Fin h × Fin k) :
    (Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) Mᵀ * X) (o, a) q =
      ∑ y, M y a * X (o, y) q := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single o]
  · simp [Matrix.kronecker, Matrix.one_apply]
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [Matrix.kronecker, Matrix.one_apply, Ne.symm hx]
  · simp

lemma g52e_L4 {h k : ℕ} (M : Matrix (Fin k) (Fin h) ℂ)
    (Y : Matrix (Fin h × Fin h) (Fin h × Fin k) ℂ) (q : Fin h × Fin h) (p b : Fin h) :
    (Y * Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) (M.map (fun z => conj z))) q (p, b) =
      ∑ y, Y q (p, y) * conj (M y b) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single p]
  · simp [Matrix.kronecker, Matrix.one_apply]
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [Matrix.kronecker, Matrix.one_apply, hx]
  · simp

lemma g52e_sandwich {h k : ℕ} (A : Matrix (Fin h) (Fin k) ℂ) (M : Matrix (Fin k) (Fin h) ℂ) :
    Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) Mᵀ * dyad (operatorKet A) (operatorKet A) *
      Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) (M.map (fun z => conj z)) =
    dyad (operatorKet (A * M)) (operatorKet (A * M)) := by
  ext ⟨o, a⟩ ⟨p, b⟩
  rw [g52e_L4]
  simp only [g52e_L3]
  simp only [dyad, operatorKet, PiLp.toLp_apply, Matrix.mul_apply, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
  ring

lemma g52e_cqf_sum {I ι : Type*} [Fintype I] (v : EuclideanSpace ℂ I) (s : Finset ι)
    (A : ι → Matrix I I ℂ) :
    complexQuadraticForm v (∑ l ∈ s, A l) = ∑ l ∈ s, complexQuadraticForm v (A l) := by
  simp only [complexQuadraticForm, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

lemma g52e_cqf_dyad {I : Type*} [Fintype I] (v w : EuclideanSpace ℂ I) :
    complexQuadraticForm v (dyad w w) =
      (∑ x, conj (v x) * w x) * conj (∑ x, conj (v x) * w x) := by
  simp only [complexQuadraticForm, dyad, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma g52e_trace_dyad {I : Type*} [Fintype I] (u w : EuclideanSpace ℂ I) :
    (dyad u u * dyad w w).trace = conj (∑ y, conj (w y) * u y) * (∑ y, conj (w y) * u y) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, dyad, map_sum, map_mul,
    Complex.conj_conj, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma g52e_sum3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

lemma g52e_fid {a h : ℕ} (ψ : EuclideanSpace ℂ (Fin a × Fin h)) (K : Matrix (Fin h) (Fin h) ℂ) :
    complexQuadraticForm ψ (idTensorSuperop (fun X => K * X * Kᴴ) (pureDensity ψ)) =
      (∑ o, ∑ i, conj (traceLeft (pureDensity ψ) o i) * K o i) *
        conj (∑ o, ∑ i, conj (traceLeft (pureDensity ψ) o i) * K o i) := by
  have hL : complexQuadraticForm ψ (idTensorSuperop (fun X => K * X * Kᴴ) (pureDensity ψ)) =
      (∑ y, ∑ p, ∑ j, ψ (y, p) * conj (K p j) * conj (ψ (y, j))) *
        (∑ x, ∑ o, ∑ i, conj (ψ (x, o)) * K o i * ψ (x, i)) := by
    simp only [complexQuadraticForm, idTensorSuperop, Matrix.of_apply, Fintype.sum_prod_type,
      Matrix.mul_apply, Matrix.conjTranspose_apply, pureDensity, Finset.sum_mul, Finset.mul_sum,
      RCLike.star_def]
    conv_lhs => enter [2, i0, 2, i1, 2, i2, 2, i3]; rw [Finset.sum_comm]
    conv_lhs => enter [2, i0, 2, i1, 2, i2]; rw [Finset.sum_comm]
    conv_lhs => enter [2, i0, 2, i1]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun o _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hG : (∑ o, ∑ i, conj (traceLeft (pureDensity ψ) o i) * K o i) =
      ∑ x, ∑ o, ∑ i, conj (ψ (x, o)) * K o i * ψ (x, i) := by
    rw [g52e_sum3]
    simp only [traceLeft, pureDensity, Matrix.of_apply, map_sum, map_mul, Complex.conj_conj,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hL, hG, mul_comm]
  congr 1
  simp only [map_sum, map_mul, Complex.conj_conj]
  try (refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun o _ =>
      Finset.sum_congr rfl fun i _ => ?_; ring)

lemma g52e_idT_sum {R ι κ L : Type*} [Fintype L] (f : L → Superop ι κ)
    (Y : Matrix (R × ι) (R × ι) ℂ) :
    idTensorSuperop (fun X => ∑ l, f l X) Y = ∑ l, idTensorSuperop (f l) Y := by
  ext p q
  simp [idTensorSuperop, Matrix.sum_apply]

lemma g52e_single_conj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (a b : Fin n) (o p : Fin m) :
    (A * Matrix.single a b (1 : ℂ) * Aᴴ) o p = A o a * star (A p b) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · rw [Matrix.conjTranspose_apply]
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [Matrix.single_apply, hc, Ne.symm hc]
    · simp
  · intro c _ hc
    have : (A * Matrix.single a b (1 : ℂ)) o c = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      simp [Matrix.single_apply, hc, Ne.symm hc]
    rw [this, zero_mul]
  · simp

/-- PDF p.4, (20)–(21): the recovery objective and both coefficient expressions. -/
theorem solution {h k a m : ℕ} (hh : 0 < h) (hk : 0 < k)
    (rho : Matrix (Fin h) (Fin h) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) (hpsi : IsPurification rho psi)
    (E : Fin m → Matrix (Fin k) (Fin h) ℂ) (hE : IsKrausFamily E)
    (R : Superop (Fin k) (Fin h)) (hR : IsChannel R) :
    recoveryCoefficient rho E =
      ∑ j, Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) ((E j).map (fun z => conj z)) *
        dyad (operatorKet rho) (operatorKet rho) *
        Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) (E j)ᵀ ∧
    purificationFidelity psi (R ∘ krausApply E) =
      (∑ j, complexQuadraticForm (operatorKet rho)
        (Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) (E j)ᵀ * outputFirstChoi R *
          Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) ((E j).map (fun z => conj z)))).re ∧
    purificationFidelity psi (R ∘ krausApply E) =
      (outputFirstChoi R * recoveryCoefficient rho E).trace.re := by
  obtain ⟨n, Rk, -, hReq⟩ := hR
  have hρ : traceLeft (pureDensity psi) = rho := hpsi.2
  have hJ : outputFirstChoi R = ∑ i, dyad (operatorKet (Rk i)) (operatorKet (Rk i)) := by
    ext ⟨o, x⟩ ⟨p, y⟩
    show R (Matrix.single x y 1) o p = _
    rw [hReq]
    simp only [krausApply, Matrix.sum_apply, dyad, operatorKet, PiLp.toLp_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [g52e_single_conj]; rfl
  let G : Matrix (Fin h) (Fin h) ℂ → ℂ := fun K => ∑ o, ∑ i, conj (rho o i) * K o i
  have hD : ∀ K : Matrix (Fin h) (Fin h) ℂ,
      (∑ x, conj ((operatorKet rho) x) * (operatorKet K) x) = G K := by
    intro K
    simp only [operatorKet, PiLp.toLp_apply, Fintype.sum_prod_type, G]
  have hF : purificationFidelity psi (R ∘ krausApply E) =
      (∑ i, ∑ j, G (Rk i * E j) * conj (G (Rk i * E j))).re := by
    have hcomp : (R ∘ krausApply E) = fun X => ∑ i, ∑ j, (Rk i * E j) * X * (Rk i * E j)ᴴ := by
      funext X
      simp only [Function.comp, hReq, krausApply, Matrix.mul_sum, Matrix.sum_mul,
        Matrix.conjTranspose_mul, Matrix.mul_assoc]
    unfold purificationFidelity
    rw [hcomp, g52e_idT_sum, g52e_cqf_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [g52e_idT_sum, g52e_cqf_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [g52e_fid, hρ]
  refine ⟨?_, ?_, ?_⟩
  · ext ⟨x, y⟩ ⟨x', y'⟩
    simp only [recoveryCoefficient, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [g52e_L2]
    simp only [g52e_L1]
    simp only [dyad, operatorKet, PiLp.toLp_apply, Matrix.mul_apply, map_sum, map_mul,
      Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_conj, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
    ring
  · rw [hF, hJ]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_sum, Matrix.sum_mul, g52e_cqf_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [g52e_sandwich, g52e_cqf_dyad, hD]
  · rw [hF, hJ]
    unfold recoveryCoefficient
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun (j : Fin m) _ => ?_)
    refine Finset.sum_congr rfl (fun (i : Fin n) _ => ?_)
    rw [g52e_trace_dyad]
    have hw : (∑ y, conj ((operatorKet (rho * (E j)ᴴ)) y) * (operatorKet (Rk i)) y) =
        G (Rk i * E j) := by
      simp only [operatorKet, PiLp.toLp_apply, Fintype.sum_prod_type, G, Matrix.mul_apply,
        Matrix.conjTranspose_apply, RCLike.star_def, map_sum, map_mul, Complex.conj_conj,
        Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [hw, mul_comm]


end

