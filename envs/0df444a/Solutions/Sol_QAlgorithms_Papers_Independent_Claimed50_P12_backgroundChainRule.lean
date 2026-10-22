-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P12.backgroundChainRule
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T10:13:12.468405+00:00
-- url     : https://prove2.me/submissions/1fdf0eb5-09f2-44e7-af6a-b0fd95c7366c

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12
noncomputable section
open Filter MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Information100.P32 (Op)
open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)
open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

lemma g68m_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) (htr : ∀ k : ℕ, (P ^ (k + 1)).trace = (Q ^ (k + 1)).trace) :
    (cfc f P).trace = (cfc f Q).trace := by
  classical
  set S : Finset ℝ := (P.finite_real_spectrum.union Q.finite_real_spectrum).toFinset ∪ {0} with hS
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hp
  have hev : ∀ x ∈ S, p.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Set.injOn_id _) hx
    exact this
  have hPe : cfc f P = Polynomial.aeval P p := by
    rw [← cfc_polynomial p P hP.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have hQe : cfc f Q = Polynomial.aeval Q p := by
    rw [← cfc_polynomial p Q hQ.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev 0 (by simp [hS]), hf]
  rw [hPe, hQe, Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [h0]
  · rw [htr k]

lemma g68m_ent_reindex {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (M : Matrix Y Y ℂ) : vnEntropy (M.submatrix e e) = vnEntropy M := by
  unfold vnEntropy
  have hpow : ∀ k : ℕ, (M.submatrix e e) ^ k = (M ^ k).submatrix e e := by
    intro k
    induction k with
    | zero => simp [Matrix.submatrix_one_equiv]
    | succ k ih => rw [pow_succ, ih, Matrix.submatrix_mul_equiv, pow_succ]
  have htr : ∀ N : Matrix Y Y ℂ, (N.submatrix e e).trace = N.trace := by
    intro N
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact e.sum_comp (fun y => N y y)
  by_cases hM : M.IsHermitian
  · have hM' : (M.submatrix e e).IsHermitian := hM.submatrix e
    rw [g68m_trace_cfc_eq _ _ hM' hM _ (by simp) (fun k => by rw [hpow, htr])]
  · have hM' : ¬ (M.submatrix e e).IsHermitian := by
      intro h
      apply hM
      have := h.submatrix e.symm
      simpa [Matrix.submatrix_submatrix] using this
    have h1 : cfc (fun x : ℝ => x * Real.logb 2 x) (M.submatrix e e) = 0 :=
      cfc_apply_of_not_predicate _ (fun h => hM' h)
    have h2 : cfc (fun x : ℝ => x * Real.logb 2 x) M = 0 :=
      cfc_apply_of_not_predicate _ (fun h => hM h)
    erw [h1, h2]; simp


attribute [local instance] Classical.propDecidable Classical.decEq

def g68m_eN (n : ℕ) (H : Fin n → Type*) :
    ((i : {j : Fin n // j.val < n}) → H i.val) ≃ ((i : Fin n) → H i) where
  toFun a i := a ⟨i, i.2⟩
  invFun x i := x i.val
  left_inv a := rfl
  right_inv x := rfl

lemma g68m_pm_top {n : ℕ} {H : Fin n → Type*} {B C : Type*} [∀ i, Fintype (H i)]
    (rho : Op (((i : Fin n) → H i) × (B × C))) :
    prefixMarginal rho n = rho.submatrix (Prod.map (g68m_eN n H) id) (Prod.map (g68m_eN n H) id) := by
  ext a b
  simp only [prefixMarginal, Matrix.submatrix_apply, Prod.map_fst, Prod.map_snd, id]
  have hc : ∀ x y : (i : Fin n) → H i,
      ((∀ (i : Fin n) (h : i.val < n), x i = a.1 ⟨i, h⟩ ∧ y i = b.1 ⟨i, h⟩) ∧
        (∀ i : Fin n, n ≤ i.val → x i = y i)) ↔
      (x = g68m_eN n H a.1 ∧ y = g68m_eN n H b.1) := by
    intro x y
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨funext fun i => (h1 i i.2).1, funext fun i => (h1 i i.2).2⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨fun i h => ⟨rfl, rfl⟩, fun i hi => absurd i.2 (not_lt.mpr hi)⟩
  simp_rw [hc, ite_and]
  simp
  rfl

instance g68m_unique0 {n : ℕ} (H : Fin n → Type*) :
    Unique ((i : {j : Fin n // j.val < 0}) → H i.val) where
  default := fun i => absurd i.2 (Nat.not_lt_zero _)
  uniq := fun a => funext fun i => absurd i.2 (Nat.not_lt_zero _)

lemma g68m_pm_zero {n : ℕ} {H : Fin n → Type*} {B C : Type*} [∀ i, Fintype (H i)]
    (rho : Op (((i : Fin n) → H i) × (B × C))) :
    prefixMarginal rho 0 = (traceLeft rho).submatrix Prod.snd Prod.snd := by
  ext a b
  simp only [prefixMarginal, Matrix.submatrix_apply, traceLeft, Matrix.of_apply]
  have hc : ∀ x y : (i : Fin n) → H i,
      ((∀ (i : Fin n) (h : i.val < 0), x i = a.1 ⟨i, h⟩ ∧ y i = b.1 ⟨i, h⟩) ∧
        (∀ i : Fin n, 0 ≤ i.val → x i = y i)) ↔ x = y := by
    intro x y
    constructor
    · rintro ⟨-, h2⟩; exact funext fun i => h2 i (Nat.zero_le _)
    · rintro rfl; exact ⟨fun i h => absurd h (Nat.not_lt_zero _), fun i _ => rfl⟩
  simp_rw [hc]
  simp

lemma g68m_mAB_sub {X X' B C : Type*} [Fintype C] (e : X' ≃ X) (M : Op (X × (B × C))) :
    marginalAB (M.submatrix (Prod.map e id) (Prod.map e id)) =
      (marginalAB M).submatrix (Prod.map e id) (Prod.map e id) := by
  ext a b; rfl

lemma g68m_mAB_zero {X0 B C : Type*} [Fintype B] [Fintype C] {A : Type*} [Fintype A]
    (rho : Op (A × (B × C))) :
    marginalAB ((traceLeft rho).submatrix (Prod.snd : X0 × (B × C) → B × C) Prod.snd) =
      (traceRight (traceLeft rho)).submatrix (Prod.snd : X0 × B → B) Prod.snd := by
  ext a b; rfl

lemma g68m_ent_unique {X0 K : Type*} [Unique X0] [Fintype K] [DecidableEq K] [Fintype X0]
    [DecidableEq (X0 × K)] (M : Matrix K K ℂ) :
    vnEntropy (M.submatrix (Prod.snd : X0 × K → K) Prod.snd) = vnEntropy M := by
  have := g68m_ent_reindex (Equiv.uniqueProd K X0) M
  convert this using 2
  ext a b; rfl


theorem solution {n : ℕ} {H : Fin n → Type*} {B C : Type*}
    [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)] [∀ i, Nonempty (H i)]
    [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C] [Nonempty B] [Nonempty C]
    (rho : Op (((i : Fin n) → H i) × (B × C))) (hrho : IsDensityMatrix rho) :
    cmi rho = ∑ i : Fin n,
      (vnEntropy (marginalAB (prefixMarginal rho (i.val+1))) +
        vnEntropy (prefixMarginal rho i.val) -
        vnEntropy (marginalAB (prefixMarginal rho i.val)) -
        vnEntropy (prefixMarginal rho (i.val+1))) := by
  set g : ℕ → ℝ := fun k => vnEntropy (marginalAB (prefixMarginal rho k)) -
    vnEntropy (prefixMarginal rho k) with hg
  have hsum : (∑ i : Fin n,
      (vnEntropy (marginalAB (prefixMarginal rho (i.val+1))) +
        vnEntropy (prefixMarginal rho i.val) -
        vnEntropy (marginalAB (prefixMarginal rho i.val)) -
        vnEntropy (prefixMarginal rho (i.val+1)))) = ∑ i : Fin n, (g (i.val + 1) - g i.val) := by
    apply Finset.sum_congr rfl; intro i _; simp only [hg]; ring
  rw [hsum, Fin.sum_univ_eq_sum_range (fun i => g (i + 1) - g i), Finset.sum_range_sub]
  have hn : g n = vnEntropy (marginalAB rho) - vnEntropy rho := by
    simp only [hg]
    rw [g68m_pm_top, g68m_mAB_sub]
    have e1 := g68m_ent_reindex ((g68m_eN n H).prodCongr (Equiv.refl (B × C))) rho
    have e2 := g68m_ent_reindex ((g68m_eN n H).prodCongr (Equiv.refl B)) (marginalAB rho)
    rw [← e1, ← e2]
    rfl
  have h0 : g 0 = vnEntropy (traceRight (traceLeft rho)) - vnEntropy (traceLeft rho) := by
    simp only [hg]
    rw [g68m_pm_zero, g68m_mAB_zero, g68m_ent_unique, g68m_ent_unique]
  rw [hn, h0, cmi]
  ring

end
