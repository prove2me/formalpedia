-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P12.lemma2_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:34:13.362013+00:00
-- url     : https://prove2.me/submissions/a857466a-d3c7-4ac2-886a-9c48511cde89

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7A13W

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Information100.P32 (Op)
open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)
open Matrix

/-- small-t exponential moment bound -/
lemma X7W_exists_t {ι : Type*} [Fintype ι] (μ g : ι → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (hs : ∑ a, μ a = 1) (d : ℝ) (hd : 0 < d) (hm : ∑ a, μ a * g a = -d) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1/2 ∧ ∑ a, μ a * Real.exp (t * g a) < 1 := by
  set B : ℝ := 1 + ∑ a, g a ^ 2 with hB
  have hB1 : 1 ≤ B := by
    have : 0 ≤ ∑ a, g a ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
    linarith
  have hBpos : 0 < B := by linarith
  have hgB1 : ∀ a, g a ^ 2 + 1 ≤ B := by
    intro a
    have := Finset.single_le_sum (f := fun a => g a ^ 2) (fun a _ => sq_nonneg _)
      (Finset.mem_univ a)
    linarith
  have hgB : ∀ a, g a ^ 2 ≤ B := fun a => by linarith [hgB1 a]
  have habsB : ∀ a, |g a| ≤ B := by
    intro a
    have h1 : |g a| ≤ 1 + g a ^ 2 := by
      have := sq_nonneg (|g a| - 1)
      have h2 : |g a| ^ 2 = g a ^ 2 := sq_abs _
      nlinarith
    have := hgB1 a
    linarith
  set t : ℝ := min (1 / (2 * B)) (d / (2 * B)) with ht
  have htpos : 0 < t := lt_min (by positivity) (by positivity)
  have ht1 : t ≤ 1 / (2 * B) := min_le_left _ _
  have ht2 : t ≤ d / (2 * B) := min_le_right _ _
  have hthalf : t ≤ 1/2 := by
    refine le_trans ht1 ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine ⟨t, htpos, hthalf, ?_⟩
  have hexp : ∀ a, Real.exp (t * g a) ≤ 1 + t * g a + (t * g a) ^ 2 := by
    intro a
    have hle : |t * g a| ≤ 1 := by
      rw [abs_mul, abs_of_pos htpos]
      calc t * |g a| ≤ (1 / (2 * B)) * B :=
            mul_le_mul ht1 (habsB a) (abs_nonneg _) (by positivity)
        _ = 1/2 := by field_simp
        _ ≤ 1 := by norm_num
    have := Real.abs_exp_sub_one_sub_id_le hle
    have := (abs_le.mp this).2
    linarith
  calc ∑ a, μ a * Real.exp (t * g a)
      ≤ ∑ a, μ a * (1 + t * g a + (t * g a) ^ 2) :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hexp a) (hμ a))
    _ = ∑ a, μ a + t * ∑ a, μ a * g a + t ^ 2 * ∑ a, μ a * g a ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun a _ => by ring)
    _ ≤ 1 + t * (-d) + t ^ 2 * B := by
        rw [hs, hm]
        have : ∑ a, μ a * g a ^ 2 ≤ B := by
          calc ∑ a, μ a * g a ^ 2 ≤ ∑ a, μ a * B :=
                Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hgB a) (hμ a))
            _ = B := by rw [← Finset.sum_mul, hs, one_mul]
        nlinarith [sq_nonneg t]
    _ < 1 := by
        have : t * B ≤ d / 2 := by
          calc t * B ≤ (d / (2 * B)) * B := mul_le_mul_of_nonneg_right ht2 hBpos.le
            _ = d / 2 := by field_simp
        nlinarith

/-- sum of a function over the (ascending) eigenvalues of a unitarily diagonalised Hermitian matrix -/
lemma X7W_sum_asc {J : Type*} [Fintype J] [DecidableEq J] (A W : Matrix J J ℂ) (lam : J → ℝ)
    (hW : star W * W = 1) (hA : A = W * diagonal (fun x => (lam x : ℂ)) * star W)
    (hH : A.IsHermitian) (g : ℝ → ℝ) :
    ∑ i, g (ascEigenvalues A i) = ∑ x, g (lam x) := by
  have h1 : ∑ i, g (ascEigenvalues A i) = ∑ j, g (hH.eigenvalues j) := by
    have : ascEigenvalues A = fun k => hH.eigenvalues₀ (Fin.rev k) := by
      unfold ascEigenvalues; rw [dif_pos hH]
    rw [this]
    rw [show (∑ i, g (hH.eigenvalues₀ (Fin.rev i))) = ∑ i, g (hH.eigenvalues₀ i) from
      Equiv.sum_comp Fin.revPerm (fun i => g (hH.eigenvalues₀ i))]
    unfold Matrix.IsHermitian.eigenvalues
    exact (Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun i => g (hH.eigenvalues₀ i))).symm
  rw [h1]
  have hcp : A.charpoly = (diagonal (fun x => (lam x : ℂ))).charpoly := by
    rw [hA, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hW, Matrix.mul_one]
  rw [hH.charpoly_eq, Matrix.charpoly_diagonal] at hcp
  have key : ∀ (s : Multiset J) (f : J → ℂ),
      ((s.map (fun j => Polynomial.X - Polynomial.C (f j))).prod).roots = s.map f := by
    intro s f
    rw [← Polynomial.roots_multiset_prod_X_sub_C (s.map f), Multiset.map_map]
    rfl
  have hms : (Finset.univ.val.map (fun j => ((hH.eigenvalues j : ℝ) : ℂ))) =
      (Finset.univ.val.map (fun x => ((lam x : ℝ) : ℂ))) := by
    rw [← key, ← key]
    congr 1
  calc ∑ j, g (hH.eigenvalues j)
      = ((Finset.univ.val.map (fun j => ((hH.eigenvalues j : ℝ) : ℂ))).map
          (fun z : ℂ => g z.re)).sum := by rw [Multiset.map_map]; rfl
    _ = ((Finset.univ.val.map (fun x => ((lam x : ℝ) : ℂ))).map
          (fun z : ℂ => g z.re)).sum := by rw [hms]
    _ = ∑ x, g (lam x) := by rw [Multiset.map_map]; rfl


lemma X7W_mp_mul {I : Type*} [Fintype I] (A B : Matrix I I ℂ) (n : ℕ) :
    matrixPower (A * B) n = matrixPower A n * matrixPower B n := by
  ext x y
  simp only [matrixPower, Matrix.mul_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]

lemma X7W_mp_star {I : Type*} [Fintype I] (A : Matrix I I ℂ) (n : ℕ) :
    matrixPower (star A) n = star (matrixPower A n) := by
  ext x y
  simp only [matrixPower, Matrix.star_apply, star_prod]

lemma X7W_mp_diag {I : Type*} [Fintype I] [DecidableEq I] (d : I → ℂ) (n : ℕ)
    [DecidableEq (Fin n → I)] :
    matrixPower (diagonal d) n = diagonal (fun x : Fin n → I => ∏ i, d (x i)) := by
  ext x y
  simp only [matrixPower, diagonal_apply]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra h; push Not at h; exact hxy (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma X7W_mp_one {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ) [DecidableEq (Fin n → I)] :
    matrixPower (1 : Matrix I I ℂ) n = 1 := by
  rw [← diagonal_one, X7W_mp_diag]; simp

lemma X7W_prod_sum {I : Type*} [Fintype I] (h : I → ℝ) (m : ℕ) :
    ∑ x : Fin m → I, ∏ i, h (x i) = (∑ a, h a) ^ m := by
  rw [← Fin.prod_const, Finset.prod_univ_sum]
  simp [Fintype.piFinset_univ]

/-- pointwise tail bound -/
lemma X7W_point (P lo hi t1 t2 : ℝ) (hP : 0 ≤ P) (hlo : 0 < lo) (hhi : 0 < hi)
    (ht1 : 0 < t1) (ht1' : t1 ≤ 1/2) (ht2 : 0 < t2) :
    P - (if lo ≤ P ∧ P ≤ hi then P else 0) ≤
      lo ^ t1 * P ^ (1 - t1) + hi ^ (-t2) * P ^ (1 + t2) := by
  have h1 : 0 ≤ lo ^ t1 * P ^ (1 - t1) := by positivity
  have h2 : 0 ≤ hi ^ (-t2) * P ^ (1 + t2) := by positivity
  split_ifs with hw
  · linarith
  · rcases hP.eq_or_lt with h0 | hpos
    · rw [← h0] at h1 h2 ⊢; linarith
    rw [not_and_or, not_le, not_le] at hw
    rcases hw with hw | hw
    · have : P ≤ lo ^ t1 * P ^ (1 - t1) := by
        have e : P = P ^ t1 * P ^ (1 - t1) := by
          rw [← Real.rpow_add hpos]; simp
        have hle : P ^ t1 ≤ lo ^ t1 := Real.rpow_le_rpow hP hw.le ht1.le
        calc P = P ^ t1 * P ^ (1 - t1) := e
          _ ≤ lo ^ t1 * P ^ (1 - t1) := mul_le_mul_of_nonneg_right hle (by positivity)
      linarith
    · have : P ≤ hi ^ (-t2) * P ^ (1 + t2) := by
        have hle : hi ^ t2 ≤ P ^ t2 := Real.rpow_le_rpow hhi.le hw.le ht2.le
        have e : hi ^ (-t2) * P ^ (1 + t2) = P * (P ^ t2 / hi ^ t2) := by
          rw [Real.rpow_neg hhi.le, Real.rpow_add hpos, Real.rpow_one]; ring
        rw [e]
        have : 1 ≤ P ^ t2 / hi ^ t2 := by
          rw [le_div_iff₀ (by positivity)]; linarith
        nlinarith
      linarith

/-- rewriting the moment sums -/
lemma X7W_mom (μ : ℝ) (hμ : 0 ≤ μ) (s e : ℝ) (he : e ≠ 0) :
    μ ^ e * Real.exp s = μ * Real.exp ((e - 1) * Real.log μ + s) := by
  rcases hμ.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow he]; simp
  · rw [Real.rpow_def_of_pos hpos, Real.exp_add,
      show Real.log μ * e = Real.log μ + (e - 1) * Real.log μ by ring, Real.exp_add,
      Real.exp_log hpos]
    ring

theorem X7W_main {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho : Op I) (hrho : IsDensityMatrix rho) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ,
      |entropyWindowMass rho m delta - 1| ≤ 2 * Real.exp (-c * (m : ℝ)) := by
  have H : rho.IsHermitian := hrho.1.isHermitian
  set μ := H.eigenvalues with hμdef
  set U : Matrix I I ℂ := (H.eigenvectorUnitary : Matrix I I ℂ) with hUdef
  have hspec : rho = U * diagonal (fun a => (μ a : ℂ)) * star U := by
    have := H.spectral_theorem
    simpa [Function.comp_def, hUdef, hμdef] using this
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self H.eigenvectorUnitary
  have hμ0 : ∀ a, 0 ≤ μ a := fun a => hrho.1.eigenvalues_nonneg a
  have hμ1 : ∑ a, μ a = 1 := by
    have := H.trace_eq_sum_eigenvalues
    rw [hrho.2] at this
    have := congrArg Complex.re this
    simpa using this.symm
  set S := vnEntropy rho with hSdef
  have hS : S = -(∑ a, μ a * Real.logb 2 (μ a)) := by
    rw [hSdef, vnEntropy, H.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    rw [show (star (H.eigenvectorUnitary : unitary (Matrix I I ℂ)) : Matrix I I ℂ) *
        (H.eigenvectorUnitary : Matrix I I ℂ) = 1 from
        Unitary.coe_star_mul_self H.eigenvectorUnitary, Matrix.one_mul, Matrix.trace_diagonal]
    simp [Function.comp_def, hμdef]
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hSlog : ∑ a, μ a * Real.log (μ a) = -(Real.log 2 * S) := by
    rw [hS, mul_neg, neg_neg, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Real.logb]
    field_simp
  -- upper tail exponent
  obtain ⟨t1, ht1, ht1', hq1⟩ := X7W_exists_t μ
    (fun a => -Real.log (μ a) - Real.log 2 * (S + delta)) hμ0 hμ1 (Real.log 2 * delta)
    (by positivity) (by
      have m1 : ∑ a, μ a * (-Real.log (μ a) - Real.log 2 * (S + delta)) =
          -(∑ a, μ a * Real.log (μ a)) - Real.log 2 * (S + delta) * ∑ a, μ a := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun a _ => by ring)
      rw [m1, hSlog, hμ1]; ring)
  obtain ⟨t2, ht2, ht2', hq2⟩ := X7W_exists_t μ
    (fun a => Real.log (μ a) + Real.log 2 * (S - delta)) hμ0 hμ1 (Real.log 2 * delta)
    (by positivity) (by
      have m1 : ∑ a, μ a * (Real.log (μ a) + Real.log 2 * (S - delta)) =
          (∑ a, μ a * Real.log (μ a)) + Real.log 2 * (S - delta) * ∑ a, μ a := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun a _ => by ring)
      rw [m1, hSlog, hμ1]; ring)
  set q1 := ∑ a, μ a * Real.exp (t1 * (-Real.log (μ a) - Real.log 2 * (S + delta))) with hq1def
  set q2 := ∑ a, μ a * Real.exp (t2 * (Real.log (μ a) + Real.log 2 * (S - delta))) with hq2def
  have hq1n : 0 ≤ q1 := Finset.sum_nonneg (fun a _ => mul_nonneg (hμ0 a) (Real.exp_pos _).le)
  have hq2n : 0 ≤ q2 := Finset.sum_nonneg (fun a _ => mul_nonneg (hμ0 a) (Real.exp_pos _).le)
  set r := max (max q1 q2) (1/2) with hr
  have hr1 : r < 1 := max_lt (max_lt hq1 hq2) (by norm_num)
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨-Real.log r, by have := Real.log_neg hr0 hr1; linarith, fun m => ?_⟩
  -- spectral rewriting
  set W := matrixPower U m with hW
  have hWW : star W * W = 1 := by
    rw [hW, ← X7W_mp_star, ← X7W_mp_mul, hUU, X7W_mp_one]
  have hA : matrixPower rho m =
      W * diagonal (fun x : Fin m → I => ((∏ i, μ (x i) : ℝ) : ℂ)) * star W := by
    rw [hspec, X7W_mp_mul, X7W_mp_mul, X7W_mp_star, X7W_mp_diag]
    simp only [Complex.ofReal_prod, hW]
  have hAH : (matrixPower rho m).IsHermitian := by
    show (matrixPower rho m)ᴴ = matrixPower rho m
    rw [← Matrix.star_eq_conjTranspose, ← X7W_mp_star, Matrix.star_eq_conjTranspose, H.eq]
  set lo : ℝ := (2 : ℝ) ^ (-(m : ℝ) * (S + delta)) with hlo
  set hi : ℝ := (2 : ℝ) ^ (-(m : ℝ) * (S - delta)) with hhi
  set P : (Fin m → I) → ℝ := fun x => ∏ i, μ (x i) with hP
  have hmass : entropyWindowMass rho m delta =
      ∑ x, (if lo ≤ P x ∧ P x ≤ hi then P x else 0) := by
    unfold entropyWindowMass
    convert X7W_sum_asc (matrixPower rho m) W P hWW hA hAH
      (fun s => if lo ≤ s ∧ s ≤ hi then s else 0) using 1
  have hP0 : ∀ x, 0 ≤ P x := fun x => Finset.prod_nonneg (fun i _ => hμ0 _)
  have hPsum : ∑ x, P x = 1 := by rw [hP, X7W_prod_sum, hμ1, one_pow]
  have hupper : entropyWindowMass rho m delta ≤ 1 := by
    rw [hmass, ← hPsum]
    refine Finset.sum_le_sum (fun x _ => ?_)
    split_ifs <;> linarith [hP0 x]
  have hlopos : 0 < lo := by positivity
  have hhipos : 0 < hi := by positivity
  have htail : 1 - entropyWindowMass rho m delta ≤ q1 ^ m + q2 ^ m := by
    rw [hmass]
    conv_lhs => rw [← hPsum]
    rw [← Finset.sum_sub_distrib]
    calc ∑ x, (P x - if lo ≤ P x ∧ P x ≤ hi then P x else 0)
        ≤ ∑ x, (lo ^ t1 * P x ^ (1 - t1) + hi ^ (-t2) * P x ^ (1 + t2)) :=
          Finset.sum_le_sum (fun x _ => X7W_point _ _ _ _ _ (hP0 x) hlopos hhipos ht1 ht1' ht2)
      _ = q1 ^ m + q2 ^ m := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          have e1 : ∀ x, P x ^ (1 - t1) = ∏ i, μ (x i) ^ (1 - t1) := fun x =>
            (Real.finsetProd_rpow Finset.univ (fun i => μ (x i)) (fun i _ => hμ0 _) _).symm
          have e2 : ∀ x, P x ^ (1 + t2) = ∏ i, μ (x i) ^ (1 + t2) := fun x =>
            (Real.finsetProd_rpow Finset.univ (fun i => μ (x i)) (fun i _ => hμ0 _) _).symm
          simp only [e1, e2]
          rw [X7W_prod_sum (fun a => μ a ^ (1 - t1)) m, X7W_prod_sum (fun a => μ a ^ (1 + t2)) m]
          have hlo' : lo ^ t1 = (Real.exp (-(t1 * (Real.log 2 * (S + delta))))) ^ m := by
            rw [hlo, ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num),
              ← Real.exp_nat_mul]
            congr 1; ring
          have hhi' : hi ^ (-t2) = (Real.exp (t2 * (Real.log 2 * (S - delta)))) ^ m := by
            rw [hhi, ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num),
              ← Real.exp_nat_mul]
            congr 1; ring
          rw [hlo', hhi', ← mul_pow, ← mul_pow, Finset.mul_sum, Finset.mul_sum]
          congr 2
          · refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [mul_comm, X7W_mom _ (hμ0 a) _ _ (by linarith)]
            congr 2; ring
          · refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [mul_comm, X7W_mom _ (hμ0 a) _ _ (by linarith)]
            congr 2; ring
  have hrm : ∀ q : ℝ, 0 ≤ q → q ≤ r → q ^ m ≤ Real.exp (-(-Real.log r) * (m : ℝ)) := by
    intro q hq hqr
    have e : Real.exp (-(-Real.log r) * (m : ℝ)) = r ^ m := by
      rw [neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hr0]
    rw [e]; exact pow_le_pow_left₀ hq hqr m
  have hb1 := hrm q1 hq1n (le_trans (le_max_left _ _) (le_max_left _ _))
  have hb2 := hrm q2 hq2n (le_trans (le_max_right _ _) (le_max_left _ _))
  rw [abs_of_nonpos (by linarith)]
  linarith

end X7A13W

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P12 in
open QAlgorithms.Papers.Independent.Information100.P32 (Op) in
theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho : Op I) (hrho : IsDensityMatrix rho) (delta : ℝ) (hdelta : 0 < delta) :
    Tendsto (fun n => entropyWindowMass rho (n+1) delta) atTop (nhds 1) ∧
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      |entropyWindowMass rho (n+1) delta - 1| ≤ C * Real.exp (-c * ((n+1 : ℕ) : ℝ)) := by
  obtain ⟨c, hc, hb⟩ := X7A13W.X7W_main rho hrho delta hdelta
  refine ⟨?_, c, 2, hc, by norm_num, 0, fun n _ => hb (n+1)⟩
  have hlim : Tendsto (fun n : ℕ => 2 * Real.exp (-c * ((n+1 : ℕ) : ℝ))) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n : ℕ => -c * ((n+1 : ℕ) : ℝ)) atTop atBot :=
      h1.const_mul_atTop_of_neg (by linarith)
    simpa using (Real.tendsto_exp_atBot.comp h2).const_mul 2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => by
    rw [Real.norm_eq_abs]; exact hb (n+1)) hlim
