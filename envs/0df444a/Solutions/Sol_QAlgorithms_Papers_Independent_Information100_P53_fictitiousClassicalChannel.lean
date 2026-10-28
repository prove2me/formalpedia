-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P53.fictitiousClassicalChannel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:10:08.898609+00:00
-- url     : https://prove2.me/submissions/83b3c851-db19-415b-b424-1d7150897ce6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53
noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

namespace A3FC

theorem trace_pure {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ) (b : EuclideanSpace ℂ (Fin N)) :
    (D * pureDensity b).trace = star (fun a => b a) ⬝ᵥ (D *ᵥ (fun a => b a)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [RCLike.star_def]; ring

theorem c_nonneg {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ) (hD : D.PosSemidef)
    (b : EuclideanSpace ℂ (Fin N)) : 0 ≤ (D * pureDensity b).trace.re := by
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

theorem main {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (s : ∀ i, SpectralData (rho i)) (I : Finset (Fin M × Fin N))
    (hI : IsTopSelection N (spectralWeight p s) I) :
    ∃ sigma : Fin M → Equiv.Perm (Fin N),
      (∀ j, ∃! i, (i, sigma i j) ∈ I) ∧
      classicalSuccess p (fun i j => (s i).value (sigma i j)) =
        ∑ z ∈ I, spectralWeight p s z ∧
      mixedOptSuccess p rho ≤ classicalSuccess p (fun i j => (s i).value (sigma i j)) := by
  classical
  obtain ⟨hcard, htop⟩ := hI
  set w := spectralWeight p s with hw
  let e : Fin N ≃ I := (finCongr hcard.symm).trans I.equivFin.symm
  let f : ∀ i : Fin M, {j : Fin N // (e j).1.1 = i} ≃ {k : Fin N // (i, k) ∈ I} := fun i =>
    Equiv.ofBijective (fun j => ⟨(e j.1).1.2, by
      have h1 := (e j.1).2
      have h2 : (e j.1).1 = (i, (e j.1).1.2) := Prod.ext j.2 rfl
      rw [h2] at h1; exact h1⟩) (by
      constructor
      · rintro ⟨j, hj⟩ ⟨j', hj'⟩ h
        simp only [Subtype.mk.injEq] at h
        have : e j = e j' := Subtype.ext (Prod.ext (hj.trans hj'.symm) h)
        exact Subtype.ext (e.injective this)
      · rintro ⟨k, hk⟩
        refine ⟨⟨e.symm ⟨(i, k), hk⟩, by simp⟩, ?_⟩
        simp)
  let sigma : Fin M → Equiv.Perm (Fin N) := fun i => (f i).extendSubtype
  have hsig : ∀ j, sigma (e j).1.1 j = (e j).1.2 := fun j => by
    exact (Equiv.extendSubtype_apply_of_mem (f (e j).1.1) j rfl).trans rfl
  have hiff : ∀ i j, (i, sigma i j) ∈ I ↔ (e j).1.1 = i := fun i j => by
    constructor
    · intro h
      by_contra hne
      exact Equiv.extendSubtype_not_mem (f i) j hne h
    · intro h
      subst h
      rw [hsig]
      exact (e j).2
  have hsupj : ∀ j, (⨆ i, p i * (s i).value (sigma i j)) = w (e j).1 := fun j => by
    have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
    apply le_antisymm
    · apply ciSup_le
      intro i
      by_cases h : (i, sigma i j) ∈ I
      · have hi := (hiff i j).1 h
        subst hi
        rw [hsig]
        exact le_rfl
      · exact htop _ (e j).2 _ h
    · refine le_trans (le_of_eq ?_) (le_ciSup (Finite.bddAbove_range _) (e j).1.1)
      show w (e j).1 = _
      conv_lhs => rw [show (e j).1 = ((e j).1.1, sigma (e j).1.1 j) by rw [hsig]]
      rfl
  have hclass : classicalSuccess p (fun i j => (s i).value (sigma i j)) = ∑ z ∈ I, w z := by
    unfold classicalSuccess
    simp only [hsupj]
    rw [← Finset.sum_coe_sort I]
    exact Equiv.sum_comp e (fun z : I => w z.1)
  refine ⟨sigma, fun j => ⟨(e j).1.1, (hiff _ j).2 rfl, fun i h => ((hiff i j).1 h).symm⟩,
    hclass, ?_⟩
  rw [hclass]
  -- quantum bound
  have hne : I.Nonempty := by
    rw [← Finset.card_pos, hcard]; exact hN
  set m := I.inf' hne w with hm
  have hmle : ∀ u ∈ I, m ≤ w u := fun u hu => Finset.inf'_le _ hu
  have hgem : ∀ v, v ∉ I → w v ≤ m := fun v hv => Finset.le_inf' _ _ fun u hu => htop u hu v hv
  have : Nonempty {D : Fin M → Matrix (Fin N) (Fin N) ℂ // IsPOVM D} := by
    refine ⟨⟨fun i => if i = ⟨0, hM⟩ then 1 else 0, fun o => ?_, ?_⟩⟩
    · dsimp only
      split_ifs
      · exact Matrix.PosSemidef.one
      · exact Matrix.PosSemidef.zero
    · simp
  apply ciSup_le
  rintro ⟨D, hDpsd, hDsum⟩
  let c : Fin M × Fin N → ℝ := fun z => (D z.1 * pureDensity ((s z.1).basis z.2)).trace.re
  have hc0 : ∀ z, 0 ≤ c z := fun z => c_nonneg _ (hDpsd _) _
  have hccol : ∀ i j, ∑ i', (D i' * pureDensity ((s i).basis j)).trace.re = 1 := by
    intro i j
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hDsum, one_mul,
      trace_pure_one]; simp
  -- c ≤ 1
  have hc1 : ∀ z, c z ≤ 1 := by
    intro z
    rw [← hccol z.1 z.2]
    exact Finset.single_le_sum (f := fun i' => (D i' * pureDensity ((s z.1).basis z.2)).trace.re)
      (fun i' _ => c_nonneg _ (hDpsd _) _) (Finset.mem_univ z.1)
  have hsumc : ∑ z, c z = N := by
    rw [Fintype.sum_prod_type]
    have : ∀ i, ∑ j, c (i, j) = (D i).trace.re := fun i => by
      simp only [c]
      rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum, sum_pure, Matrix.mul_one]
    simp only [this]
    rw [← Complex.re_sum, ← Matrix.trace_sum, hDsum]
    simp
  have heff : ∀ i, p i * effectProb (D i) (rho i) = ∑ j, w (i, j) * c (i, j) := by
    intro i
    unfold effectProb
    rw [(s i).reconstruct, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    simp only [hw, spectralWeight, c]; ring
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

end A3FC

end QAlgorithms.Papers.Independent.Information100.P53

end

theorem solution {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : QAlgorithms.Papers.Independent.Information100.P53.IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ)
    (hrho : ∀ i, QAlgorithms.IsDensityMatrix (rho i))
    (s : ∀ i, QAlgorithms.Papers.Independent.Information100.P53.SpectralData (rho i))
    (I : Finset (Fin M × Fin N))
    (hI : QAlgorithms.Papers.Independent.Information100.P53.IsTopSelection N
      (QAlgorithms.Papers.Independent.Information100.P53.spectralWeight p s) I) :
    ∃ sigma : Fin M → Equiv.Perm (Fin N),
      (∀ j, ∃! i, (i, sigma i j) ∈ I) ∧
      QAlgorithms.Papers.Independent.Information100.P53.classicalSuccess p
          (fun i j => (s i).value (sigma i j)) =
        ∑ z ∈ I, QAlgorithms.Papers.Independent.Information100.P53.spectralWeight p s z ∧
      QAlgorithms.mixedOptSuccess p rho ≤
        QAlgorithms.Papers.Independent.Information100.P53.classicalSuccess p
          (fun i j => (s i).value (sigma i j)) :=
  QAlgorithms.Papers.Independent.Information100.P53.A3FC.main hM hN p hp rho hrho s I hI

