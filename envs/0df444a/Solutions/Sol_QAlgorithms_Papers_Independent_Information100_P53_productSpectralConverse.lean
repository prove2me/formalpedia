-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P53.productSpectralConverse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:15:37.597199+00:00
-- url     : https://prove2.me/submissions/a4a936da-98e0-4ec3-bdcc-6a292f5f2ca4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53
noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

namespace A3PS

theorem trace_pure {ι : Type*} [Fintype ι] (D : Matrix ι ι ℂ) (b : EuclideanSpace ℂ ι) :
    (D * pureDensity b).trace = star (fun a => b a) ⬝ᵥ (D *ᵥ (fun a => b a)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [RCLike.star_def]; ring

theorem c_nonneg {ι : Type*} [Fintype ι] (D : Matrix ι ι ℂ) (hD : D.PosSemidef)
    (b : EuclideanSpace ℂ ι) : 0 ≤ (D * pureDensity b).trace.re := by
  rw [trace_pure]
  exact (Complex.nonneg_iff.mp (hD.dotProduct_mulVec_nonneg _)).1

theorem trace_pure_one {N : ℕ} (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (j : Fin N) : (pureDensity (b j)).trace = 1 := by
  have h := b.inner_eq_one j
  rw [PiLp.inner_apply] at h
  rw [← h]
  simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [RCLike.inner_apply]

theorem sum_pure {N : ℕ} (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    ∑ j, pureDensity (b j) = 1 := by
  ext a c
  have h := b.sum_inner_mul_inner (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)
  simp only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right, map_one,
    one_mul, PiLp.single_apply] at h
  rw [Matrix.sum_apply]
  simp only [pureDensity, Matrix.of_apply, Matrix.one_apply]
  rw [h]
  by_cases hac : a = c
  · subst hac; simp
  · simp [hac, Ne.symm hac]

/-- General fractional-knapsack converse. -/
theorem knap {M : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hM : 0 < M) (p : Fin M → ℝ) (rho : Fin M → Matrix ι ι ℂ) (v : Fin M → κ → ℝ)
    (b : Fin M → κ → EuclideanSpace ℂ ι)
    (hb1 : ∀ i k, (pureDensity (b i k)).trace = 1)
    (hbc : ∀ i, ∑ k, pureDensity (b i k) = 1)
    (hrec : ∀ i, rho i = ∑ k, (v i k : ℂ) • pureDensity (b i k))
    (I : Finset (Fin M × κ)) (hne : I.Nonempty) (hcard : I.card = Fintype.card ι)
    (htop : ∀ u ∈ I, ∀ v', v' ∉ I → p v'.1 * v v'.1 v'.2 ≤ p u.1 * v u.1 u.2) :
    mixedOptSuccess p rho ≤ ∑ z ∈ I, p z.1 * v z.1 z.2 := by
  classical
  set w : Fin M × κ → ℝ := fun z => p z.1 * v z.1 z.2 with hw
  change mixedOptSuccess p rho ≤ ∑ z ∈ I, w z
  set m := I.inf' hne w with hm
  have hmle : ∀ u ∈ I, m ≤ w u := fun u hu => Finset.inf'_le _ hu
  have hgem : ∀ v, v ∉ I → w v ≤ m := fun v hv => Finset.le_inf' _ _ fun u hu => htop u hu v hv
  have : Nonempty {D : Fin M → Matrix ι ι ℂ // IsPOVM D} := by
    refine ⟨⟨fun i => if i = ⟨0, hM⟩ then 1 else 0, fun o => ?_, ?_⟩⟩
    · dsimp only
      split_ifs
      · exact Matrix.PosSemidef.one
      · exact Matrix.PosSemidef.zero
    · simp
  apply ciSup_le
  rintro ⟨D, hDpsd, hDsum⟩
  let c : Fin M × κ → ℝ := fun z => (D z.1 * pureDensity (b z.1 z.2)).trace.re
  have hc0 : ∀ z, 0 ≤ c z := fun z => c_nonneg _ (hDpsd _) _
  have hccol : ∀ i j, ∑ i', (D i' * pureDensity (b i j)).trace.re = 1 := by
    intro i j
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hDsum, one_mul, hb1]; simp
  have hc1 : ∀ z, c z ≤ 1 := by
    intro z
    rw [← hccol z.1 z.2]
    exact Finset.single_le_sum (f := fun i' => (D i' * pureDensity (b z.1 z.2)).trace.re)
      (fun i' _ => c_nonneg _ (hDpsd _) _) (Finset.mem_univ z.1)
  have hsumc : ∑ z, c z = Fintype.card ι := by
    rw [Fintype.sum_prod_type]
    have : ∀ i, ∑ j, c (i, j) = (D i).trace.re := fun i => by
      simp only [c]
      rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum, hbc, Matrix.mul_one]
    simp only [this]
    rw [← Complex.re_sum, ← Matrix.trace_sum, hDsum]
    simp
  have heff : ∀ i, p i * effectProb (D i) (rho i) = ∑ j, w (i, j) * c (i, j) := by
    intro i
    unfold effectProb
    rw [hrec i, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    simp only [hw, c]; ring
  simp only [heff]
  rw [← Fintype.sum_prod_type (f := fun z => w z * c z)]
  have hpt : ∀ z, w z * c z ≤ (if z ∈ I then w z else 0) + m * (c z - if z ∈ I then 1 else 0) := by
    intro z
    by_cases hz : z ∈ I
    · simp only [hz, if_true]
      nlinarith [hmle z hz, hc1 z]
    · simp only [hz, if_false]
      nlinarith [hgem z hz, hc0 z]
  refine (Finset.sum_le_sum fun z _ => hpt z).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hsumc,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_boole]
  simp [hcard]

section product

variable {n q : ℕ} {F : Type*} {rho : F → Matrix (Fin q) (Fin q) ℂ}

theorem pd_apply (s : ∀ a, SpectralData (rho a)) (x : Fin n → F) (j : Fin n → Fin q)
    (u u' : Fin n → Fin q) :
    pureDensity (productVector s x j) u u' =
      ∏ l, pureDensity ((s (x l)).basis (j l)) (u l) (u' l) := by
  simp [pureDensity, productVector, Finset.prod_mul_distrib, map_prod]

theorem prod_one (u u' : Fin n → Fin q) :
    ∏ l, (1 : Matrix (Fin q) (Fin q) ℂ) (u l) (u' l) =
      (1 : Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ) u u' := by
  by_cases h : u = u'
  · subst h; simp
  · obtain ⟨l, hl⟩ := Function.ne_iff.mp h
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (Matrix.one_apply_ne hl)

theorem prod_sum_pure (s : ∀ a, SpectralData (rho a)) (x : Fin n → F) :
    ∑ j, pureDensity (productVector s x j) = 1 := by
  ext u u'
  rw [Matrix.sum_apply]
  simp only [pd_apply]
  rw [← Fintype.prod_sum (fun l a => pureDensity ((s (x l)).basis a) (u l) (u' l)), ← prod_one]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← Matrix.sum_apply, sum_pure]

theorem prod_trace (s : ∀ a, SpectralData (rho a)) (x : Fin n → F) (j : Fin n → Fin q) :
    (pureDensity (productVector s x j)).trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, pd_apply]
  rw [← Fintype.prod_sum (fun l a => pureDensity ((s (x l)).basis (j l)) a a)]
  refine Finset.prod_eq_one fun l _ => ?_
  have := trace_pure_one (s (x l)).basis (j l)
  simpa [Matrix.trace] using this

theorem prod_rec (s : ∀ a, SpectralData (rho a)) (x : Fin n → F) :
    productMatrix rho x =
      ∑ j, ((∏ l, (s (x l)).value (j l) : ℝ) : ℂ) • pureDensity (productVector s x j) := by
  have hr : ∀ a c d, rho a c d =
      ∑ k, ((s a).value k : ℂ) * pureDensity ((s a).basis k) c d := by
    intro a c d
    conv_lhs => rw [(s a).reconstruct]
    simp [Matrix.sum_apply]
  ext u u'
  simp only [productMatrix, hr]
  rw [Fintype.prod_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, pd_apply, smul_eq_mul, Finset.prod_mul_distrib]
  push_cast
  rfl

end product

theorem main {n q M : ℕ} (hn : 0 < n) (hq2 : 2 ≤ q)
    (hM : 0 < M) {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hq : Fintype.card F = q) (rho : F → Matrix (Fin q) (Fin q) ℂ)
    (hrho : ∀ a, IsDensityMatrix (rho a)) (s : ∀ a, SpectralData (rho a))
    (code : Fin M → Fin n → F) (hcode : Function.Injective code)
    (p : Fin M → ℝ) (hp : IsPrior p) (I : Finset (Fin M × (Fin n → Fin q)))
    (hI : IsTopSelection (q ^ n) (productWeight p (fun a => (s a).value) code) I) :
    mixedOptSuccess p (fun m => productMatrix rho (code m)) ≤
      ∑ z ∈ I, productWeight p (fun a => (s a).value) code z := by
  obtain ⟨hcard, htop⟩ := hI
  have hne : I.Nonempty := by
    rw [← Finset.card_pos, hcard]; exact pow_pos (by omega) n
  have hc : I.card = Fintype.card (Fin n → Fin q) := by
    rw [hcard, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have htop' : ∀ u ∈ I, ∀ v', v' ∉ I →
      p v'.1 * (∏ l, (s (code v'.1 l)).value (v'.2 l)) ≤
        p u.1 * (∏ l, (s (code u.1 l)).value (u.2 l)) := fun u hu v hv => htop u hu v hv
  have k1 := fun m j => prod_trace s (code m) j
  have k2 := fun m => prod_sum_pure s (code m)
  have k3 := fun m => prod_rec s (code m)
  exact knap (ι := Fin n → Fin q) (κ := Fin n → Fin q) hM p
    (fun m => productMatrix rho (code m)) _ _ k1 k2 k3 I hne hc htop'

end A3PS

end QAlgorithms.Papers.Independent.Information100.P53

end

theorem solution {n q M : ℕ} (hn : 0 < n) (hq2 : 2 ≤ q)
    (hM : 0 < M) {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hq : Fintype.card F = q) (rho : F → Matrix (Fin q) (Fin q) ℂ)
    (hrho : ∀ a, QAlgorithms.IsDensityMatrix (rho a))
    (s : ∀ a, QAlgorithms.Papers.Independent.Information100.P53.SpectralData (rho a))
    (code : Fin M → Fin n → F) (hcode : Function.Injective code)
    (p : Fin M → ℝ) (hp : QAlgorithms.Papers.Independent.Information100.P53.IsPrior p)
    (I : Finset (Fin M × (Fin n → Fin q)))
    (hI : QAlgorithms.Papers.Independent.Information100.P53.IsTopSelection (q ^ n)
      (QAlgorithms.Papers.Independent.Information100.P53.productWeight p
        (fun a => (s a).value) code) I) :
    QAlgorithms.mixedOptSuccess p
        (fun m => QAlgorithms.Papers.Independent.Information100.P53.productMatrix rho (code m)) ≤
      ∑ z ∈ I, QAlgorithms.Papers.Independent.Information100.P53.productWeight p
        (fun a => (s a).value) code z :=
  QAlgorithms.Papers.Independent.Information100.P53.A3PS.main hn hq2 hM hq rho hrho s code
    hcode p hp I hI
