-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P07.psi_convex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:02:42.480259+00:00
-- url     : https://prove2.me/submissions/be58d6b5-989f-4bec-87c7-249dfb504f45

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P07
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Advance50.P07

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD petzD)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative Density elog)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P19 (marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Support50.P21 (PositiveTensorBasis)

end QAlgorithms.Papers.Independent.Advance50.P07

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Advance50.P07
open QAlgorithms (IsEffect)

lemma s109c2_holder {K : Type} [Fintype K] (c x y : K → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hx : ∀ k, 0 ≤ x k) (hy : ∀ k, 0 ≤ y k) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hA : 0 < ∑ k, c k * x k) (hB : 0 < ∑ k, c k * y k) :
    ∑ k, c k * (x k ^ a * y k ^ b) ≤ (∑ k, c k * x k) ^ a * (∑ k, c k * y k) ^ b := by
  set A := ∑ k, c k * x k
  set B := ∑ k, c k * y k
  have hAB : 0 < A ^ a * B ^ b := mul_pos (Real.rpow_pos_of_pos hA a) (Real.rpow_pos_of_pos hB b)
  have hterm : ∀ k, x k ^ a * y k ^ b ≤ A ^ a * B ^ b * (a * (x k / A) + b * (y k / B)) := by
    intro k
    have h := Real.geom_mean_le_arith_mean2_weighted ha hb (div_nonneg (hx k) hA.le)
      (div_nonneg (hy k) hB.le) hab
    rw [Real.div_rpow (hx k) hA.le, Real.div_rpow (hy k) hB.le] at h
    have e : x k ^ a * y k ^ b = A ^ a * B ^ b * (x k ^ a / A ^ a * (y k ^ b / B ^ b)) := by
      have h1 : A ^ a ≠ 0 := (Real.rpow_pos_of_pos hA a).ne'
      have h2 : B ^ b ≠ 0 := (Real.rpow_pos_of_pos hB b).ne'
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h hAB.le
  calc ∑ k, c k * (x k ^ a * y k ^ b)
      ≤ ∑ k, c k * (A ^ a * B ^ b * (a * (x k / A) + b * (y k / B))) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hterm k) (hc k)
    _ = ∑ k, ((A ^ a * B ^ b * (a / A)) * (c k * x k) + (A ^ a * B ^ b * (b / B)) * (c k * y k)) :=
        Finset.sum_congr rfl fun k _ => by ring
    _ = (A ^ a * B ^ b * (a / A)) * A + (A ^ a * B ^ b * (b / B)) * B := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = A ^ a * B ^ b := by
        field_simp
        linarith

lemma s109c2_logconv {K : Type} [Fintype K] (c : K → ℝ) (hc : ∀ k, 0 ≤ c k)
    (u : K → ℝ → ℝ) (hu0 : ∀ k t, 0 ≤ u k t)
    (hmul : ∀ k α β a b, 0 < a → 0 < b → a + b = 1 →
      u k (a * α + b * β) = u k α ^ a * u k β ^ b)
    (F : ℝ → ℝ) (hF : ∀ α, F α = ∑ k, c k * u k α) (hpos : ∀ α, 0 < α → 0 < F α) :
    ConvexOn ℝ (Set.Ioi 0) (fun α => Real.logb 2 (F α)) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have hFx := hpos x hx
      have hFy := hpos y hy
      have hle : F (a • x + b • y) ≤ F x ^ a * F y ^ b := by
        rw [hF, hF x, hF y]
        simp only [smul_eq_mul]
        rw [Finset.sum_congr rfl fun k _ => by rw [hmul k x y a b ha' hb' hab]]
        exact s109c2_holder c (fun k => u k x) (fun k => u k y) hc (fun k => hu0 k x)
          (fun k => hu0 k y) a b ha hb hab (by rw [← hF]; exact hFx) (by rw [← hF]; exact hFy)
      have hpos' : 0 < F (a • x + b • y) := hpos _ ((convex_Ioi 0) hx hy ha hb hab)
      simp only [smul_eq_mul]
      calc Real.logb 2 (F (a • x + b • y)) ≤ Real.logb 2 (F x ^ a * F y ^ b) :=
            Real.logb_le_logb_of_le (by norm_num) hpos' hle
        _ = a * Real.logb 2 (F x) + b * Real.logb 2 (F y) := by
            rw [Real.logb_mul (Real.rpow_pos_of_pos hFx a).ne' (Real.rpow_pos_of_pos hFy b).ne',
              Real.logb_rpow_eq_mul_logb_of_pos hFx, Real.logb_rpow_eq_mul_logb_of_pos hFy]
    · subst hb'; rw [add_zero] at hab; subst hab; simp
  · subst ha'; rw [zero_add] at hab; subst hab; simp

lemma s109c2_trace {I : Type} [Fintype I] [DecidableEq I] (rho sigma R : Mat I)
    (hr : rho.IsHermitian) (hs : sigma.IsHermitian) (hR : R.IsHermitian) (f g : ℝ → ℝ) :
    (R * cfc f rho * R * cfc g sigma).trace.re =
      ∑ i, ∑ j, Complex.normSq
        (((star (hr.eigenvectorUnitary : Mat I)) * R * (hs.eigenvectorUnitary : Mat I)) i j) *
        (f (hr.eigenvalues i) * g (hs.eigenvalues j)) := by
  rw [hr.cfc_eq, hs.cfc_eq, Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
  set U : Mat I := (hr.eigenvectorUnitary : Mat I)
  set V : Mat I := (hs.eigenvectorUnitary : Mat I)
  set D : Mat I := Matrix.diagonal (RCLike.ofReal ∘ f ∘ hr.eigenvalues)
  set E : Mat I := Matrix.diagonal (RCLike.ofReal ∘ g ∘ hs.eigenvalues)
  set A : Mat I := star U * R * V
  have hBA : star V * R * U = Aᴴ := by
    simp only [A, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, hR.eq, Matrix.mul_assoc]
  have e1 : R * (U * D * star U) * R * (V * E * star V) =
      (R * U * D * star U * R * V * E) * star V := by simp only [Matrix.mul_assoc]
  have e2 : star V * (R * U * D * star U * R * V * E) = (star V * R * U) * D * A * E := by
    simp only [A, Matrix.mul_assoc]
  rw [e1, Matrix.trace_mul_comm, e2, hBA]
  simp only [D, E, Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Function.comp_apply,
    Finset.sum_mul, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diagonal_apply, Function.comp_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.zero_re]
  have key : ∀ a : ℂ, ∀ x y : ℝ, ((starRingEnd ℂ) a * (x:ℂ) * a * (y:ℂ)).re =
      Complex.normSq a * (x * y) := by
    intro a x y
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp), if_pos rfl]
  exact key _ _ _

lemma s109c2_hpow (x : ℝ) (hx : 0 ≤ x) (α β a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (if x = 0 then 0 else Real.rpow x (a * α + b * β)) =
      (if x = 0 then 0 else Real.rpow x α) ^ a * (if x = 0 then 0 else Real.rpow x β) ^ b := by
  split_ifs with h
  · rw [Real.zero_rpow ha.ne', zero_mul]
  · have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm h)
    show x ^ (a * α + b * β) = (x ^ α) ^ a * (x ^ β) ^ b
    rw [Real.rpow_add hx', ← Real.rpow_mul hx'.le, ← Real.rpow_mul hx'.le, mul_comm a, mul_comm b]

lemma s109c2_hnn (x : ℝ) (hx : 0 ≤ x) (t : ℝ) :
    0 ≤ (if x = 0 then 0 else Real.rpow x t) := by
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg hx t

theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma P : Mat I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (hP : IsEffect P) (hfinite : ∀ alpha : ℝ, 0 < alpha → 0 < quasiMoment rho sigma P alpha) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (quasiLogMoment rho sigma P) := by
  have hR : (cfc Real.sqrt P).IsHermitian := cfc_predicate Real.sqrt P
  set A : Mat I := (star (hrho.1.eigenvectorUnitary : Mat I)) * cfc Real.sqrt P *
    (hsigma.1.eigenvectorUnitary : Mat I)
  let h : ℝ → ℝ → ℝ := fun x t => if x = 0 then 0 else Real.rpow x t
  let c : I × I → ℝ := fun p => Complex.normSq (A p.1 p.2)
  let u : I × I → ℝ → ℝ := fun p α =>
    h (hrho.1.eigenvalues p.1) α * h (hsigma.1.eigenvalues p.2) (1 - α)
  have hl := hrho.eigenvalues_nonneg
  have hm := hsigma.eigenvalues_nonneg
  have hF : ∀ α, quasiMoment rho sigma P α = ∑ p, c p * u p α := by
    intro α
    unfold quasiMoment supportPower
    rw [s109c2_trace rho sigma _ hrho.1 hsigma.1 hR, Fintype.sum_prod_type]
  have hconv := s109c2_logconv c (fun p => Complex.normSq_nonneg _) u
    (fun p t => mul_nonneg (s109c2_hnn _ (hl _) _) (s109c2_hnn _ (hm _) _))
    (by
      intro p α β a b ha hb hab
      simp only [u, h]
      rw [show 1 - (a * α + b * β) = a * (1 - α) + b * (1 - β) by
        linear_combination -hab]
      rw [s109c2_hpow _ (hl _) α β a b ha hb, s109c2_hpow _ (hm _) _ _ a b ha hb,
        Real.mul_rpow (s109c2_hnn _ (hl _) _) (s109c2_hnn _ (hm _) _),
        Real.mul_rpow (s109c2_hnn _ (hl _) _) (s109c2_hnn _ (hm _) _)]
      ring)
    (quasiMoment rho sigma P) hF hfinite
  exact hconv
