-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P53.spectralConverse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:41:10.119648+00:00
-- url     : https://prove2.me/submissions/781542f9-557b-43fe-80e8-f85614e11aca

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open Finset
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P53

lemma g53i_inner_basis {q : ℕ} (b : OrthonormalBasis (Fin q) ℂ (EuclideanSpace ℂ (Fin q))) (j k : Fin q) :
    ∑ w, conj (b j w) * b k w = if j = k then 1 else 0 := by
  have h := orthonormal_iff_ite.mp b.orthonormal j k
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [← h]; simp [dotProduct, mul_comm]

lemma g53i_complete {q : ℕ} (b : OrthonormalBasis (Fin q) ℂ (EuclideanSpace ℂ (Fin q))) (u w : Fin q) :
    ∑ k, b k u * conj (b k w) = if u = w then 1 else 0 := by
  have h := b.sum_inner_mul_inner (EuclideanSpace.single u 1) (EuclideanSpace.single w 1)
  simp only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right, map_one,
    one_mul, mul_one] at h
  rw [h]
  by_cases huw : u = w
  · subst huw; simp
  · simp [EuclideanSpace.single_apply, huw, Ne.symm huw]

/-- quadratic form -/
def g53i_cc {q : ℕ} (D : Matrix (Fin q) (Fin q) ℂ) (b : EuclideanSpace ℂ (Fin q)) : ℂ :=
  ∑ u, ∑ w, conj (b u) * D u w * b w

lemma g53i_cc_dot {q : ℕ} (D : Matrix (Fin q) (Fin q) ℂ) (b : EuclideanSpace ℂ (Fin q)) :
    g53i_cc D b = star (b : Fin q → ℂ) ⬝ᵥ (D *ᵥ b) := by
  simp [g53i_cc, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

lemma g53i_cc_sum {q : ℕ} {ι : Type*} (t : Finset ι) (D : ι → Matrix (Fin q) (Fin q) ℂ)
    (b : EuclideanSpace ℂ (Fin q)) : g53i_cc (∑ i ∈ t, D i) b = ∑ i ∈ t, g53i_cc (D i) b := by
  simp only [g53i_cc, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ u, ∑ i ∈ t, ∑ w, conj (b u) * D i u w * b w :=
        Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

lemma g53i_cc_sub {q : ℕ} (D E : Matrix (Fin q) (Fin q) ℂ) (b : EuclideanSpace ℂ (Fin q)) :
    g53i_cc (D - E) b = g53i_cc D b - g53i_cc E b := by
  simp only [g53i_cc, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma g53i_cc_one {q : ℕ} (b : OrthonormalBasis (Fin q) ℂ (EuclideanSpace ℂ (Fin q))) (k : Fin q) :
    g53i_cc 1 (b k) = 1 := by
  simp only [g53i_cc, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [g53i_inner_basis]; simp

lemma g53i_cc_pure {q : ℕ} (b : OrthonormalBasis (Fin q) ℂ (EuclideanSpace ℂ (Fin q))) (j k : Fin q) :
    g53i_cc (pureDensity (b j)) (b k) = if j = k then 1 else 0 := by
  have : g53i_cc (pureDensity (b j)) (b k) =
      (∑ u, conj (b k u) * b j u) * (∑ w, conj (b j w) * b k w) := by
    rw [Finset.sum_mul_sum]
    simp only [g53i_cc, pureDensity, Matrix.of_apply]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun w _ => by ring))
  rw [this, g53i_inner_basis, g53i_inner_basis]
  by_cases h : j = k
  · subst h; simp
  · simp [h, Ne.symm h]

lemma g53i_tr {q : ℕ} (D : Matrix (Fin q) (Fin q) ℂ) {A : Matrix (Fin q) (Fin q) ℂ}
    (s : SpectralData A) : (D * A).trace = ∑ k, (s.value k : ℂ) * g53i_cc D (s.basis k) := by
  conv_lhs => rw [s.reconstruct]
  rw [Finset.mul_sum, Matrix.trace_sum]
  congr 1; ext k
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply, g53i_cc]
  congr 1; ext u; congr 1; ext w; ring

lemma g53i_cc_trace {q : ℕ} (D : Matrix (Fin q) (Fin q) ℂ)
    (b : OrthonormalBasis (Fin q) ℂ (EuclideanSpace ℂ (Fin q))) :
    ∑ k, g53i_cc D (b k) = D.trace := by
  calc ∑ k, g53i_cc D (b k) = ∑ u, ∑ w, D u w * ∑ k, b k w * conj (b k u) := by
        simp only [g53i_cc, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun k _ => by ring))
    _ = D.trace := by
        simp only [g53i_complete, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rfl

lemma g53i_cc_re_nonneg {q : ℕ} {D : Matrix (Fin q) (Fin q) ℂ} (hD : D.PosSemidef)
    (b : EuclideanSpace ℂ (Fin q)) : 0 ≤ (g53i_cc D b).re := by
  rw [g53i_cc_dot]
  exact (Complex.nonneg_iff.mp (hD.dotProduct_mulVec_nonneg _)).1

lemma g53i_knapsack {α : Type*} [Fintype α] [DecidableEq α] (w c : α → ℝ) (I : Finset α)
    (hne : I.Nonempty) (hc0 : ∀ z, 0 ≤ c z) (hc1 : ∀ z, c z ≤ 1) (hsum : ∑ z, c z = I.card)
    (htop : ∀ u ∈ I, ∀ v, v ∉ I → w v ≤ w u) :
    ∑ z, w z * c z ≤ ∑ z ∈ I, w z := by
  obtain ⟨u0, hu0, hmin⟩ := I.exists_min_image w hne
  set t := w u0
  have h1 : ∀ z, w z * c z - (if z ∈ I then w z else 0) ≤ t * c z - (if z ∈ I then t else 0) := by
    intro z
    by_cases hz : z ∈ I
    · simp only [hz, if_true]; have := hmin z hz; nlinarith [hc1 z]
    · simp only [hz, if_false, sub_zero]; have := htop u0 hu0 z hz; nlinarith [hc0 z]
  have h2 := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => h1 z)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul] at h2
  rw [hsum] at h2
  linarith

/-- PDF p.4 and Appendix B-A p.7, Theorem 4 (Spectral converse), including both
inequalities and the sufficient equality clause; the decoder remains a POVM. -/
theorem solution {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (s : ∀ i, SpectralData (rho i)) (I : Finset (Fin M × Fin N))
    (hI : IsTopSelection N (spectralWeight p s) I)
    (D : Fin M → Matrix (Fin N) (Fin N) ℂ) (hD : IsPOVM D) :
    success p rho D ≤ ∑ z ∈ I, spectralWeight p s z ∧
    (∑ z ∈ I, spectralWeight p s z) ≤ 1 ∧
    ((∀ i, D i = selectedProjector s I i) →
      success p rho D = ∑ z ∈ I, spectralWeight p s z) := by
  -- success formula
  have hsucc : ∀ E : Fin M → Matrix (Fin N) (Fin N) ℂ, success p rho E =
      ∑ z : Fin M × Fin N, spectralWeight p s z * (g53i_cc (E z.1) ((s z.1).basis z.2)).re := by
    intro E
    simp only [success, effectProb, Fintype.sum_prod_type, spectralWeight]
    congr 1; ext i
    rw [g53i_tr _ (s i), Complex.re_sum, Finset.mul_sum]
    congr 1; ext k
    simp only [Complex.re_ofReal_mul]; ring
  -- eigenvalues are nonnegative and sum to one
  have hval : ∀ i k, (s i).value k = (g53i_cc (rho i) ((s i).basis k)).re := by
    intro i k
    have := g53i_tr (pureDensity ((s i).basis k)) (s i)
    simp only [g53i_cc_pure] at this
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
    have h2 : (pureDensity ((s i).basis k) * rho i).trace = g53i_cc (rho i) ((s i).basis k) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply, g53i_cc]
      rw [Finset.sum_comm]; congr 1; ext u; congr 1; ext w; ring
    rw [← h2, this]; simp
  have hvnn : ∀ i k, 0 ≤ (s i).value k := fun i k => by
    rw [hval]; exact g53i_cc_re_nonneg (hrho i).1 _
  have hvsum : ∀ i, ∑ k, (s i).value k = 1 := by
    intro i
    have := g53i_tr 1 (s i)
    simp only [g53i_cc_one, mul_one, one_mul, (hrho i).2] at this
    have := congrArg Complex.re this
    simpa [Complex.re_sum] using this.symm
  have hwnn : ∀ z, 0 ≤ spectralWeight p s z := fun z => mul_nonneg (hp.1 _) (hvnn _ _)
  have hwsum : ∑ z, spectralWeight p s z = 1 := by
    simp only [spectralWeight, Fintype.sum_prod_type, ← Finset.mul_sum, hvsum, mul_one, hp.2]
  have hIne : I.Nonempty := by
    rw [← Finset.card_pos, hI.1]; exact hN
  refine ⟨?_, ?_, ?_⟩
  · rw [hsucc]
    refine g53i_knapsack _ _ I hIne (fun z => g53i_cc_re_nonneg (hD.1 _) _) ?_ ?_ hI.2
    · intro z
      have hle : (1 - D z.1).PosSemidef := by
        have : 1 - D z.1 = ∑ o ∈ Finset.univ.erase z.1, D o := by
          rw [← hD.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ z.1)]; abel
        rw [this]; exact Matrix.posSemidef_sum _ (fun o _ => hD.1 o)
      have := g53i_cc_re_nonneg hle ((s z.1).basis z.2)
      rw [g53i_cc_sub, g53i_cc_one, Complex.sub_re, Complex.one_re] at this
      linarith
    · rw [hI.1, Fintype.sum_prod_type]
      have : ∀ i, ∑ k, (g53i_cc (D i) ((s i).basis k)).re = (D i).trace.re := by
        intro i
        rw [← Complex.re_sum, g53i_cc_trace]
      simp_rw [this]
      rw [← Complex.re_sum, ← Matrix.trace_sum, hD.2, Matrix.trace_one]
      simp
  · calc ∑ z ∈ I, spectralWeight p s z ≤ ∑ z, spectralWeight p s z :=
          Finset.sum_le_univ_sum_of_nonneg hwnn
      _ = 1 := hwsum
  · intro hsel
    rw [hsucc]
    have : ∀ z : Fin M × Fin N, (g53i_cc (D z.1) ((s z.1).basis z.2)).re = if z ∈ I then 1 else 0 := by
      intro z
      rw [hsel, selectedProjector, g53i_cc_sum]
      simp only [g53i_cc_pure, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp
    simp_rw [this, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]

end
