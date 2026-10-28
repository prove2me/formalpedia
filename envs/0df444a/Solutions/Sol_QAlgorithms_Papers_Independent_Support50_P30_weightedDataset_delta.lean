-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P30.weightedDataset_delta
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:16:20.519771+00:00
-- url     : https://prove2.me/submissions/30164505-b34d-440c-a401-dfea951d23a7

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

open scoped Matrix ComplexConjugate

namespace X8WD

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P30

variable {d : ℕ}

/-- centered matrix as a Euclidean vector -/
noncomputable def cen (A : Matrix (Fin d) (Fin d) ℂ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun p => (A - (A.trace / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) p.1 p.2)

lemma cen_add (A B : Matrix (Fin d) (Fin d) ℂ) : cen (A + B) = cen A + cen B := by
  ext p; simp [cen, Matrix.trace_add, add_div, add_smul]; ring

lemma cen_smul (c : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) : cen (c • A) = c • cen A := by
  ext p; simp [cen, Matrix.trace_smul, mul_div_assoc, smul_smul]; ring

lemma cen_sum {M : ℕ} (c : Fin M → ℂ) (A : Fin M → Matrix (Fin d) (Fin d) ℂ) :
    cen (∑ i, c i • A i) = ∑ i, c i • cen (A i) := by
  induction (Finset.univ : Finset (Fin M)) using Finset.induction_on with
  | empty => ext p; simp [cen]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cen_add, cen_smul, ih]

lemma delta_eq (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    centeredDelta A = ‖cen A‖ ^ 2 := by
  set t := A.trace with ht
  set s : ℂ := t / (d : ℂ) with hs
  have htc : (starRingEnd ℂ) t = t := by
    have := Matrix.trace_conjTranspose A
    rw [hA.eq] at this; exact this.symm
  have hsc : (starRingEnd ℂ) s = s := by
    rw [hs, map_div₀, htc, Complex.conj_natCast]
  have hBc : ∀ i j, (starRingEnd ℂ) ((A - s • (1 : Matrix (Fin d) (Fin d) ℂ)) i j) =
      (A - s • (1 : Matrix (Fin d) (Fin d) ℂ)) j i := by
    intro i j
    have hA' : (starRingEnd ℂ) (A i j) = A j i := by
      have := congrFun (congrFun hA.eq j) i
      simpa [Matrix.conjTranspose_apply] using this
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, map_sub, hA']
    by_cases h : i = j
    · subst h; simp [hsc]
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  set B := A - s • (1 : Matrix (Fin d) (Fin d) ℂ) with hB
  have hn : ‖cen A‖ ^ 2 = ((B * B).trace).re := by
    rw [EuclideanSpace.norm_sq_eq]
    have : ∀ p : Fin d × Fin d, ‖(cen A) p‖ ^ 2 = (B p.1 p.2 * B p.2 p.1).re := by
      intro p
      have e : (cen A) p = B p.1 p.2 := rfl
      rw [e, ← hBc p.1 p.2, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    simp_rw [this]
    rw [Fintype.sum_prod_type, Matrix.trace, Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  rw [hn]
  unfold centeredDelta deltaPair
  congr 1
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp [Matrix.trace]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have e : B * B = A * A - (2 * s) • A + (s * s) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    rw [hB]; simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    module
  rw [e, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, ← ht, hs]
  simp only [smul_eq_mul]
  field_simp
  ring

lemma herm_sum {ι : Type*} (u : Finset ι) (f : ι → Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ i, (f i).IsHermitian) : (∑ i ∈ u, f i).IsHermitian := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

lemma herm_agg {n : ℕ} (S : SchurFrame n) (m : Sector n) (A : QnnOperator n) (hA : A.IsHermitian) :
    (aggregate S m A).IsHermitian := by
  unfold aggregate schurCompression
  apply herm_sum
  intro nu
  exact Matrix.isHermitian_mul_mul_conjTranspose _ hA

lemma agg_lin {n M : ℕ} (S : SchurFrame n) (m : Sector n) (c : Fin M → ℝ) (rho : Fin M → QnnDensity n) :
    aggregate S m (dataOperator c rho) = ∑ i, (c i : ℂ) • aggregate S m (rho i).val := by
  unfold aggregate schurCompression dataOperator
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem x8_main {n M : ℕ} (S : SchurFrame n) (m : Sector n)
    (rho : Fin M → QnnDensity n) (c : Fin M → ℝ) :
    centeredDelta (aggregate S m (dataOperator c rho)) ≤
      (∑ i, |c i| * Real.sqrt (centeredDelta (aggregate S m (rho i).val))) ^ 2 := by
  have hH : ∀ i, (aggregate S m (rho i).val).IsHermitian := fun i =>
    herm_agg S m _ (rho i).2.1.1
  have hHs : (aggregate S m (dataOperator c rho)).IsHermitian := by
    rw [agg_lin]
    apply herm_sum
    intro i
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, (hH i).eq]
    simp
  rw [delta_eq _ hHs]
  have hsq : ∀ i, Real.sqrt (centeredDelta (aggregate S m (rho i).val)) = ‖cen (aggregate S m (rho i).val)‖ := by
    intro i; rw [delta_eq _ (hH i), Real.sqrt_sq (norm_nonneg _)]
  simp_rw [hsq]
  rw [agg_lin, cen_sum]
  apply pow_le_pow_left₀ (norm_nonneg _)
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl; intro i _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

end X8WD

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P30 in
theorem solution {n M : ℕ} (S : SchurFrame n) (m : Sector n)
    (rho : Fin M → QnnDensity n) (c : Fin M → ℝ) :
    centeredDelta (aggregate S m (dataOperator c rho)) ≤
      (∑ i, |c i| * Real.sqrt (centeredDelta (aggregate S m (rho i).val))) ^ 2 :=
  X8WD.x8_main S m rho c
