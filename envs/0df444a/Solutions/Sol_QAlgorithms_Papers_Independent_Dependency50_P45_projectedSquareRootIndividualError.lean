-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P45.projectedSquareRootIndividualError
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T23:14:55.375165+00:00
-- url     : https://prove2.me/submissions/1adac869-f3bf-4fe9-ba23-370aef317d28

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45

open scoped ComplexConjugate Matrix
open Matrix QAlgorithms

namespace X7B11

variable {D : Type*} [Fintype D] [DecidableEq D]

lemma X7SR_qf (W : Matrix D D ℂ) (d : D → ℂ) (u : D → ℂ) :
    star u ⬝ᵥ ((W * diagonal d * star W) *ᵥ u) =
      ∑ k, d k * (star ((star W) *ᵥ u) k * ((star W) *ᵥ u) k) := by
  have h1 : star u ᵥ* W = star (star W *ᵥ u) := by
    rw [star_mulVec]; simp [star_eq_conjTranspose]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, h1]
  generalize star W *ᵥ u = c
  simp only [dotProduct, Pi.star_apply, mulVec_diagonal]
  refine Finset.sum_congr rfl fun k _ => by ring

lemma X7SR_scalar (l : ℝ) (c : ℝ) (hc : 0 ≤ c) (hl : c ≤ l) :
    3 * c - l * c ≤ 2 * ((Real.sqrt l)⁻¹ * c) := by
  rcases eq_or_lt_of_le hc with h | h
  · subst h; simp
  have hl0 : 0 < l := lt_of_lt_of_le h hl
  set y := Real.sqrt l with hy
  have hy0 : 0 < y := Real.sqrt_pos.mpr hl0
  have hyl : y ^ 2 = l := Real.sq_sqrt hl0.le
  rw [← hyl]
  have : 3 - y^2 ≤ 2 * y⁻¹ := by
    rw [← sub_nonneg]
    have : 2 * y⁻¹ - (3 - y^2) = (y - 1)^2 * (y + 2) / y := by field_simp; ring
    rw [this]; positivity
  nlinarith


lemma X7SR_sumreal (f : D → ℝ) (c : D → ℂ) :
    ∑ k, ((f k : ℝ) : ℂ) * (star c k * c k) = ((∑ k, f k * Complex.normSq (c k) : ℝ) : ℂ) := by
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]; rfl

lemma X7SR_core (phi : Matrix D D ℂ) (hphi : phi.IsHermitian) (u : D → ℂ)
    (hge : ∀ v : D → ℂ, Complex.normSq (star v ⬝ᵥ u) ≤ (star v ⬝ᵥ phi *ᵥ v).re)
    (hg : (star u ⬝ᵥ u).re ≤ 1) :
    (star u ⬝ᵥ (cfc (fun x => (Real.sqrt x)⁻¹) phi) *ᵥ u).im = 0 ∧
    1 - (star u ⬝ᵥ (cfc (fun x => (Real.sqrt x)⁻¹) phi) *ᵥ u).re ^ 2 ≤
      2 * (1 - (star u ⬝ᵥ u).re) + ((star u ⬝ᵥ phi *ᵥ u).re - ((star u ⬝ᵥ u).re) ^ 2) := by
  set W : Matrix D D ℂ := (hphi.eigenvectorUnitary : Matrix D D ℂ) with hW
  set lam := hphi.eigenvalues with hlam
  have hWW : star W * W = 1 := Unitary.coe_star_mul_self _
  have hWW' : W * star W = 1 := Unitary.coe_mul_star_self _
  have hS : cfc (fun x => (Real.sqrt x)⁻¹) phi =
      W * diagonal (fun k => (((Real.sqrt (lam k))⁻¹ : ℝ) : ℂ)) * star W := by
    rw [hphi.cfc_eq]; simp [IsHermitian.cfc, hW, hlam, Function.comp_def]
  have hP : phi = W * diagonal (fun k => ((lam k : ℝ) : ℂ)) * star W := by
    conv_lhs => rw [hphi.spectral_theorem]
    simp [hW, hlam, Function.comp_def]
  have h1 : (1 : Matrix D D ℂ) = W * diagonal (fun k => ((1 : ℝ) : ℂ)) * star W := by
    simp [hWW']
  set c := star W *ᵥ u with hc
  have eg : star u ⬝ᵥ u = ((∑ k, 1 * Complex.normSq (c k) : ℝ) : ℂ) := by
    have : star u ⬝ᵥ u = star u ⬝ᵥ (W * diagonal (fun k => ((1 : ℝ) : ℂ)) * star W) *ᵥ u := by
      rw [← h1, one_mulVec]
    rw [this, X7SR_qf, X7SR_sumreal]
  have ea : star u ⬝ᵥ (cfc (fun x => (Real.sqrt x)⁻¹) phi) *ᵥ u =
      ((∑ k, (Real.sqrt (lam k))⁻¹ * Complex.normSq (c k) : ℝ) : ℂ) := by
    rw [hS, X7SR_qf, X7SR_sumreal]
  have eq : star u ⬝ᵥ phi *ᵥ u = ((∑ k, lam k * Complex.normSq (c k) : ℝ) : ℂ) := by
    rw [hP, X7SR_qf, X7SR_sumreal]
  have hk : ∀ k, Complex.normSq (c k) ≤ lam k := by
    intro k
    have := hge (W *ᵥ Pi.single k 1)
    have e1 : star (W *ᵥ Pi.single k 1) ⬝ᵥ u = c k := by
      rw [star_mulVec, ← dotProduct_mulVec]
      simp [hc, star_eq_conjTranspose, dotProduct, Pi.single_apply]
    have e2 : star W *ᵥ (W *ᵥ Pi.single k (1 : ℂ)) = Pi.single k 1 := by
      rw [mulVec_mulVec, hWW, one_mulVec]
    rw [e1, hP, X7SR_qf, e2, X7SR_sumreal] at this
    simpa [Pi.single_apply, Complex.normSq_apply] using this
  rw [ea, eg, eq]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and, one_mul]
  have hsum : 3 * (∑ k, Complex.normSq (c k)) - (∑ k, lam k * Complex.normSq (c k)) ≤
      2 * (∑ k, (Real.sqrt (lam k))⁻¹ * Complex.normSq (c k)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun k _ => X7SR_scalar _ _ (Complex.normSq_nonneg _) (hk k)
  rw [eg] at hg
  simp only [Complex.ofReal_re, one_mul] at hg
  have hg0 : 0 ≤ ∑ k, Complex.normSq (c k) := Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _
  set g := ∑ k, Complex.normSq (c k)
  set a := ∑ k, (Real.sqrt (lam k))⁻¹ * Complex.normSq (c k)
  set Q := ∑ k, lam k * Complex.normSq (c k)
  nlinarith [sq_nonneg (1 - a), mul_nonneg hg0 (sub_nonneg.mpr hg)]

lemma X7SR_pd (w : EuclideanSpace ℂ D) :
    pureDensity w = vecMulVec (WithLp.ofLp w) (star (WithLp.ofLp w)) := by
  ext a b; simp [pureDensity, vecMulVec_apply]

lemma X7SR_conj (x y : D → ℂ) : star x ⬝ᵥ y = conj (star y ⬝ᵥ x) := by
  simp only [dotProduct, Pi.star_apply, map_sum, map_mul, RCLike.star_def, Complex.conj_conj]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma X7SR_pdqf (v : D → ℂ) (w : EuclideanSpace ℂ D) :
    star v ⬝ᵥ (pureDensity w *ᵥ v) = ((Complex.normSq (star v ⬝ᵥ WithLp.ofLp w) : ℝ) : ℂ) := by
  rw [X7SR_pd, vecMulVec_mulVec, dotProduct_smul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, X7SR_conj (WithLp.ofLp w) v, Complex.mul_conj]

lemma X7SR_ep (m t : EuclideanSpace ℂ D) :
    effectProb (pureDensity m) (pureDensity t) =
      Complex.normSq (star (WithLp.ofLp m) ⬝ᵥ WithLp.ofLp t) := by
  unfold effectProb
  rw [X7SR_pd t, mul_vecMulVec, trace_vecMulVec, dotProduct_comm, X7SR_pdqf,
    X7SR_conj, Complex.normSq_conj, Complex.ofReal_re]

lemma X7SR_SP (phi P : Matrix D D ℂ) (hphi : phi.IsHermitian) (hPh : P.IsHermitian)
    (hPphi : P * phi = phi) :
    cfc (fun x => (Real.sqrt x)⁻¹) phi * P = cfc (fun x => (Real.sqrt x)⁻¹) phi := by
  set W : Matrix D D ℂ := (hphi.eigenvectorUnitary : Matrix D D ℂ) with hW
  set lam := hphi.eigenvalues with hlam
  have hWW : star W * W = 1 := Unitary.coe_star_mul_self _
  have hS : cfc (fun x => (Real.sqrt x)⁻¹) phi =
      W * diagonal (fun k => (((Real.sqrt (lam k))⁻¹ : ℝ) : ℂ)) * star W := by
    rw [hphi.cfc_eq]; simp [IsHermitian.cfc, hW, hlam, Function.comp_def]
  have hP : phi = W * diagonal (fun k => ((lam k : ℝ) : ℂ)) * star W := by
    conv_lhs => rw [hphi.spectral_theorem]
    simp [hW, hlam, Function.comp_def]
  set T := W * diagonal (fun k => ((((Real.sqrt (lam k))⁻¹) ^ 3 : ℝ) : ℂ)) * star W
  have hST : cfc (fun x => (Real.sqrt x)⁻¹) phi = phi * T := by
    rw [hS, hP]
    simp only [T]
    have : W * diagonal (fun k => ((lam k : ℝ) : ℂ)) * star W *
        (W * diagonal (fun k => ((((Real.sqrt (lam k))⁻¹) ^ 3 : ℝ) : ℂ)) * star W) =
        W * (diagonal (fun k => ((lam k : ℝ) : ℂ)) *
          diagonal (fun k => ((((Real.sqrt (lam k))⁻¹) ^ 3 : ℝ) : ℂ))) * star W := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star W) W, hWW, Matrix.one_mul]
    have hfun : (fun k => (((Real.sqrt (lam k))⁻¹ : ℝ) : ℂ)) =
        fun k => ((lam k : ℝ) : ℂ) * ((((Real.sqrt (lam k))⁻¹) ^ 3 : ℝ) : ℂ) := by
      funext k
      rw [← Complex.ofReal_mul]
      congr 1
      rcases le_or_gt (lam k) 0 with h | h
      · simp [Real.sqrt_eq_zero'.mpr h]
      · have h1 : (0 : ℝ) < Real.sqrt (lam k) := Real.sqrt_pos.mpr h
        have h2 : Real.sqrt (lam k) ^ 2 = lam k := Real.sq_sqrt h.le
        calc (Real.sqrt (lam k))⁻¹ = Real.sqrt (lam k) ^ 2 * ((Real.sqrt (lam k))⁻¹) ^ 3 := by
              field_simp
          _ = _ := by rw [h2]
    rw [this, diagonal_mul_diagonal, hfun]
  have hSH : (cfc (fun x => (Real.sqrt x)⁻¹) phi).IsHermitian :=
    (cfc_predicate (fun x => (Real.sqrt x)⁻¹) phi : IsSelfAdjoint _)
  have hPS : P * cfc (fun x => (Real.sqrt x)⁻¹) phi = cfc (fun x => (Real.sqrt x)⁻¹) phi := by
    rw [hST, ← Matrix.mul_assoc, hPphi]
  calc cfc (fun x => (Real.sqrt x)⁻¹) phi * P
      = (P * cfc (fun x => (Real.sqrt x)⁻¹) phi)ᴴ := by
        rw [conjTranspose_mul, hSH.eq, hPh.eq]
    _ = _ := by rw [hPS, hSH.eq]

open QAlgorithms.Papers.Independent.Dependency50.P45 in
lemma X7SR_glue {O : Type*} [Fintype O] [DecidableEq O] (t : O → EuclideanSpace ℂ D)
    (P : Matrix D D ℂ) (hPh : P.IsHermitian) (hPP : P * P = P) (ht : ∀ i, ‖t i‖ ≤ 1) (i : O) :
    1 - effectProb (squareRootPOVM t P (some i)) (pureDensity (t i)) ≤
      2 * (1 - (inner ℂ (t i) (act P (t i))).re) +
        ∑ j ∈ Finset.univ.erase i, ‖inner ℂ (t i) (act P (t j))‖ ^ 2 := by
  set phi : Matrix D D ℂ := ∑ j, pureDensity (act P (t j)) with hphi_def
  set u : O → D → ℂ := fun j => P *ᵥ WithLp.ofLp (t j) with hu
  have hact : ∀ j, WithLp.ofLp (act P (t j)) = u j := fun j => rfl
  have hinner : ∀ j, inner ℂ (t i) (act P (t j)) = star (u i) ⬝ᵥ u j := by
    intro j
    rw [EuclideanSpace.inner_eq_star_dotProduct, hact, dotProduct_comm]
    symm; simp only [hu]
    rw [star_mulVec, ← dotProduct_mulVec, hPh.eq, mulVec_mulVec, hPP]
  have hpdH : ∀ w : EuclideanSpace ℂ D, (pureDensity w).IsHermitian := by
    intro w; ext a b; simp [pureDensity, conjTranspose_apply, mul_comm]
  have hphiH : phi.IsHermitian := by
    rw [hphi_def, IsHermitian, conjTranspose_sum]
    exact Finset.sum_congr rfl fun j _ => (hpdH _).eq
  have hqf : ∀ v, star v ⬝ᵥ phi *ᵥ v = ((∑ j, Complex.normSq (star v ⬝ᵥ u j) : ℝ) : ℂ) := by
    intro v
    rw [hphi_def, sum_mulVec, dotProduct_sum]
    push_cast
    exact Finset.sum_congr rfl fun j _ => by rw [X7SR_pdqf, hact]
  have hge : ∀ v : D → ℂ, Complex.normSq (star v ⬝ᵥ u i) ≤ (star v ⬝ᵥ phi *ᵥ v).re := by
    intro v
    rw [hqf, Complex.ofReal_re]
    exact Finset.single_le_sum (f := fun j => Complex.normSq (star v ⬝ᵥ u j))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  -- norms
  set N := ‖act P (t i)‖ with hN
  have huu : star (u i) ⬝ᵥ u i = ((N ^ 2 : ℝ) : ℂ) := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (act P (t i))
    rw [EuclideanSpace.inner_eq_star_dotProduct, hact, dotProduct_comm] at this
    rw [this]; push_cast; rfl
  have hN1 : N ≤ 1 := by
    have h1 : (inner ℂ (t i) (act P (t i))).re ≤ ‖t i‖ * N :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    rw [hinner, huu, Complex.ofReal_re] at h1
    have hN0 : 0 ≤ N := norm_nonneg _
    nlinarith [ht i]
  have hg : (star (u i) ⬝ᵥ u i).re ≤ 1 := by
    rw [huu, Complex.ofReal_re]; have := norm_nonneg (act P (t i)); nlinarith
  obtain ⟨him, hcore⟩ := X7SR_core phi hphiH (u i) hge hg
  -- P phi = phi
  have hPphi : P * phi = phi := by
    rw [hphi_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [X7SR_pd, mul_vecMulVec, hact, hu]
    simp only [mulVec_mulVec, hPP]
  have hSP := X7SR_SP phi P hphiH hPh hPphi
  have hSH : (cfc (fun x => (Real.sqrt x)⁻¹) phi).IsHermitian :=
    (cfc_predicate (fun x => (Real.sqrt x)⁻¹) phi : IsSelfAdjoint _)
  have hep : effectProb (squareRootPOVM t P (some i)) (pureDensity (t i)) =
      Complex.normSq (star (u i) ⬝ᵥ (cfc (fun x => (Real.sqrt x)⁻¹) phi) *ᵥ u i) := by
    simp only [squareRootPOVM, squareRootVector]
    rw [X7SR_ep]
    congr 1
    change star ((cfc (fun x => (Real.sqrt x)⁻¹) phi) *ᵥ u i) ⬝ᵥ WithLp.ofLp (t i) = _
    rw [star_mulVec, ← dotProduct_mulVec, hSH.eq, hu]
    simp only
    rw [mulVec_mulVec, hSP]
  rw [hep, Complex.normSq_apply, him, mul_zero, add_zero, hinner]
  have hsplit : ∑ j ∈ Finset.univ.erase i, ‖inner ℂ (t i) (act P (t j))‖ ^ 2 =
      (star (u i) ⬝ᵥ phi *ᵥ u i).re - Complex.normSq (star (u i) ⬝ᵥ u i) := by
    rw [hqf, Complex.ofReal_re, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [hinner, Complex.sq_norm, add_sub_cancel_left]
  rw [hsplit]
  have : Complex.normSq (star (u i) ⬝ᵥ u i) = ((star (u i) ⬝ᵥ u i).re) ^ 2 := by
    rw [huu, Complex.normSq_ofReal, Complex.ofReal_re]; ring
  rw [this]
  nlinarith [hcore]

open QAlgorithms.Papers.Independent.Dependency50.P45 in
lemma X7SR_ortho {A : Type*} [Fintype A] [DecidableEq A] (U : Matrix.unitaryGroup A ℂ) {n : ℕ}
    (z z' : Fin n → A) :
    star (WithLp.ofLp (eigenWord U z)) ⬝ᵥ WithLp.ofLp (eigenWord U z') =
      if z = z' then 1 else 0 := by
  have hUU : star (U : Matrix A A ℂ) * (U : Matrix A A ℂ) = 1 := Unitary.coe_star_mul_self _
  have : star (WithLp.ofLp (eigenWord U z)) ⬝ᵥ WithLp.ofLp (eigenWord U z') =
      ∏ i, (star (U : Matrix A A ℂ) * (U : Matrix A A ℂ)) (z i) (z' i) := by
    simp only [Matrix.mul_apply, Fintype.prod_sum, dotProduct, eigenWord, Pi.star_apply,
      star_apply, RCLike.star_def]
    refine Fintype.sum_congr _ _ fun x => ?_
    rw [map_prod, ← Finset.prod_mul_distrib]
  rw [this, hUU]
  split_ifs with h
  · subst h; simp
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ z' i := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [one_apply, hi])

open QAlgorithms.Papers.Independent.Dependency50.P45 in
lemma X7SR_proj {A : Type*} [Fintype A] [DecidableEq A] (U : Matrix.unitaryGroup A ℂ)
    (lam : A → ℝ) (n : ℕ) (delta : ℝ) :
    (typicalProjector U lam n delta).IsHermitian ∧
      typicalProjector U lam n delta * typicalProjector U lam n delta =
        typicalProjector U lam n delta := by
  have hpdH : ∀ w : EuclideanSpace ℂ (Fin n → A), (pureDensity w).IsHermitian := by
    intro w; ext a b; simp [pureDensity, conjTranspose_apply, mul_comm]
  constructor
  · unfold typicalProjector
    rw [IsHermitian, conjTranspose_sum]
    exact Finset.sum_congr rfl fun j _ => (hpdH _).eq
  · unfold typicalProjector
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [Finset.mul_sum]
    have : ∀ z' ∈ typicalWords lam n delta, pureDensity (eigenWord U z) * pureDensity (eigenWord U z') =
        if z = z' then pureDensity (eigenWord U z) else 0 := by
      intro z' _
      rw [X7SR_pd, X7SR_pd, mul_vecMulVec, vecMulVec_mulVec, X7SR_ortho]
      split_ifs with h
      · subst h; simp
      · ext a b; simp [vecMulVec_apply]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    simp [hz]

open QAlgorithms.Papers.Independent.Dependency50.P45 in
lemma X7SR_kw {A B K : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (U : Matrix.unitaryGroup A ℂ) (E : K → Matrix B A ℂ) {n : ℕ}
    (alpha : Fin n → A) (beta : Fin n → K)
    (hpos : ∀ j, 0 < ‖rectangularAct (E (beta j))
      (WithLp.toLp 2 fun a => (U : Matrix A A ℂ) a (alpha j))‖) :
    ‖krausWord U E alpha beta‖ ≤ 1 := by
  have h2 : ‖krausWord U E alpha beta‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [krausWord, norm_prod, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_norm, ← Finset.prod_pow]
    refine Eq.trans (Fintype.prod_sum (fun j b => (‖WithLp.ofLp (rectangularAct (E (beta j))
      (WithLp.toLp 2 fun a => (U : Matrix A A ℂ) a (alpha j))) b‖ / ‖rectangularAct (E (beta j))
      (WithLp.toLp 2 fun a => (U : Matrix A A ℂ) a (alpha j))‖) ^ 2)).symm ?_
    refine Finset.prod_eq_one fun j _ => ?_
    simp only [div_pow, ← Finset.sum_div]
    rw [← EuclideanSpace.norm_sq_eq]
    exact div_self (pow_pos (hpos j) 2).ne'
  nlinarith [norm_nonneg (krausWord U E alpha beta)]

end X7B11

noncomputable section

open scoped ComplexConjugate Matrix

open Filter MeasureTheory

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P76 (dampingChannel)

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P45 X7B11 in
theorem solution {A B K O : Type*}
    [Fintype A] [Fintype B] [Fintype K] [Fintype O]
    [DecidableEq A] [DecidableEq B] [DecidableEq K] [DecidableEq O]
    [Nonempty A] [Nonempty B] [Nonempty K] [Nonempty O]
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho)
    (U : Matrix.unitaryGroup A ℂ) (lam : A → ℝ) (hspec : IsSpectralData rho U lam)
    (E : K → Matrix B A ℂ) (hE : IsKrausFamily E)
    (V : Matrix.unitaryGroup B ℂ) (mu : B → ℝ)
    (hout : IsSpectralData (krausApply E rho) V mu)
    (n : ℕ) (hn : 0 < n) (delta1 delta2 : ℝ) (hd1 : 0 < delta1) (hd2 : 0 < delta2)
    (alpha : O → Fin n → A) (beta : O → Fin n → K)
    (halpha : ∀ i, alpha i ∈ typicalWords lam n delta1)
    (hpositive : ∀ i j, 0 < ‖rectangularAct (E (beta i j))
      (WithLp.toLp 2 fun a => (U : Matrix A A ℂ) a (alpha i j))‖) :
    let t := fun i => krausWord U E (alpha i) (beta i)
    let P := typicalProjector V mu n delta2
    ∀ i, 1 - effectProb (squareRootPOVM t P (some i)) (pureDensity (t i)) ≤
      2 * (1 - (inner ℂ (t i) (act P (t i))).re) +
        ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), ‖inner ℂ (t i) (act P (t j))‖ ^ 2 := by
  intro t P i
  obtain ⟨hPh, hPP⟩ := X7SR_proj V mu n delta2
  have h := X7SR_glue t P hPh hPP (fun i => X7SR_kw U E (alpha i) (beta i) (hpositive i)) i
  convert h using 3
  ext j
  simp

end
