-- Prove2me | solution 1 for SparseNLO.IHT.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:35:09.72932+00:00
-- url     : https://prove2.me/submissions/5a99b6b9-7f9b-410d-8bcd-2b4d582c7b6b

import Mathlib
import Definitions.Def_SparseNLO_IHT_Setting

set_option autoImplicit false
open Filter Topology
open SparseNLO.IHT SparseNLO.CWOpt

theorem sn_fLI_grad {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    gradient (fLI A b) x i = 2 * inner ℝ (Matrix.toEuclideanLin A x - b)
      (Matrix.toEuclideanLin A (EuclideanSpace.single i 1)) := by
  set T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) with hT
  have hTx : ∀ v, T v = Matrix.toEuclideanLin A v := fun v => rfl
  have h1 : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin n) => T v - b) T x :=
    T.hasFDerivAt.sub_const b
  have h2 := h1.norm_sq
  have h3 : fLI A b = fun v => ‖T v - b‖ ^ 2 := by
    funext v; simp [fLI, hTx]
  rw [h3]
  have h4 : ∀ w, inner ℝ (gradient (fun v => ‖T v - b‖ ^ 2) x) w =
      2 * inner ℝ (T x - b) (T w) := by
    intro w
    have : fderiv ℝ (fun v => ‖T v - b‖ ^ 2) x w = inner ℝ (gradient (fun v => ‖T v - b‖ ^ 2) x) w := by
      simp [gradient, InnerProductSpace.toDual_symm_apply]
    rw [← this, h2.fderiv]
    simp [inner_sub_left]
  have h5 := h4 (EuclideanSpace.single i 1)
  rw [EuclideanSpace.inner_single_right] at h5
  simpa [hTx] using h5

theorem sn_inj {m n s : ℕ} (hsn : s < n) (A : Matrix (Fin m) (Fin n) ℝ) (hA : IsSRegular s A)
    (I : Finset (Fin n)) (hI : I.card ≤ s) (d : EuclideanSpace ℝ (Fin n))
    (hd : ∀ i, d i ≠ 0 → i ∈ I) (hAd : Matrix.toEuclideanLin A d = 0) : d = 0 := by
  obtain ⟨J, hIJ, -, hJ⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ I) hI
    (by simpa using hsn.le : s ≤ (Finset.univ : Finset (Fin n)).card)
  have hli := hA J hJ
  rw [Fintype.linearIndependent_iff] at hli
  have key := hli (fun j => d j) (by
    funext r
    have h1 : (Matrix.toEuclideanLin A d).ofLp r = 0 := by rw [hAd]; rfl
    rw [Matrix.ofLp_toEuclideanLin_apply] at h1
    simp only [Matrix.mulVec, dotProduct] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have e : ∑ x : (J : Set (Fin n)), d x * A r x = ∑ x ∈ J, d x * A r x :=
      Finset.sum_coe_sort J (fun j => d j * A r j)
    rw [e, ← h1]
    rw [Finset.sum_subset (Finset.subset_univ J)]
    · refine Finset.sum_congr rfl fun j _ => by ring
    · intro j _ hj
      have : d j = 0 := by
        by_contra h0; exact hj (hIJ (hd j h0))
      simp [this])
  ext j
  by_cases hj : j ∈ J
  · exact key ⟨j, hj⟩
  · by_contra h0
    exact hj (hIJ (hd j h0))

theorem sn_bf_unique {m n s : ℕ} (hsn : s < n) (A : Matrix (Fin m) (Fin n) ℝ) (hA : IsSRegular s A)
    (b : EuclideanSpace ℝ (Fin m)) (x x' : EuclideanSpace ℝ (Fin n))
    (hx : IsBF (fLI A b) s x) (hx' : IsBF (fLI A b) s x') (hI : I1 x = I1 x') : x = x' := by
  have hgr : ∀ y : EuclideanSpace ℝ (Fin n), IsBF (fLI A b) s y → ∀ i ∈ I1 y,
      gradient (fLI A b) y i = 0 := by
    intro y hy i hi
    obtain ⟨hC, h1, h2⟩ := hy
    rcases lt_or_eq_of_le (show l0 y ≤ s from hC) with hlt | heq
    · simp [h1 hlt]
    · exact h2 heq i hi
  have hip : ∀ i ∈ I1 x, inner ℝ (Matrix.toEuclideanLin A x - b) (Matrix.toEuclideanLin A (EuclideanSpace.single i 1)) = 0 := by
    intro i hi
    have := hgr x hx i hi
    rw [sn_fLI_grad] at this
    linarith
  have hip' : ∀ i ∈ I1 x, inner ℝ (Matrix.toEuclideanLin A x' - b) (Matrix.toEuclideanLin A (EuclideanSpace.single i 1)) = 0 := by
    intro i hi
    have := hgr x' hx' i (hI ▸ hi)
    rw [sn_fLI_grad] at this
    linarith
  set d := x - x' with hd
  have hdi : ∀ i ∈ I1 x, inner ℝ (Matrix.toEuclideanLin A d) (Matrix.toEuclideanLin A (EuclideanSpace.single i 1)) = 0 := by
    intro i hi
    have h1 := hip i hi
    have h2 := hip' i hi
    have : Matrix.toEuclideanLin A d = (Matrix.toEuclideanLin A x - b) - (Matrix.toEuclideanLin A x' - b) := by
      simp [hd]
    rw [this, inner_sub_left, h1, h2]; simp
  have hdz : ∀ i, i ∉ I1 x → d i = 0 := by
    intro i hi
    have h1 : x i = 0 := by simpa [I1] using hi
    have h2 : x' i = 0 := by
      have : i ∉ I1 x' := hI ▸ hi
      simpa [I1] using this
    simp [hd, h1, h2]
  have hsum : d = ∑ i, d i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hAd : Matrix.toEuclideanLin A d = 0 := by
    have h0 : inner ℝ (Matrix.toEuclideanLin A d) (Matrix.toEuclideanLin A d) = 0 := by
      have e : Matrix.toEuclideanLin A d = ∑ i, d i • Matrix.toEuclideanLin A (EuclideanSpace.single i (1 : ℝ)) := by
        conv_lhs => rw [hsum]
        simp [map_sum, map_smul]
      have e2 : inner ℝ (Matrix.toEuclideanLin A d) (Matrix.toEuclideanLin A d) =
          inner ℝ (Matrix.toEuclideanLin A d)
            (∑ i, d i • Matrix.toEuclideanLin A (EuclideanSpace.single i (1 : ℝ))) := by
        rw [← e]
      rw [e2, inner_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [inner_smul_right]
      by_cases hi : i ∈ I1 x
      · rw [hdi i hi]; simp
      · rw [hdz i hi]; simp
    exact inner_self_eq_zero.mp h0
  have := sn_inj hsn A hA (I1 x) (show l0 x ≤ s from hx.1) d (by
    intro i hi
    by_contra h0
    exact hi (hdz i h0)) hAd
  exact sub_eq_zero.mp this

theorem solution {m n s : ℕ} (hs : 0 < s) (hsn : s < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) (hA : IsSRegular s A) :
    {x : EuclideanSpace ℝ (Fin n) | SparseNLO.CWOpt.IsBF (fLI A b) s x}.Finite := by
  refine Set.Finite.subset (Set.finite_iUnion (fun I : Finset (Fin n) =>
    (Set.Subsingleton.finite (s := {x : EuclideanSpace ℝ (Fin n) | IsBF (fLI A b) s x ∧ I1 x = I}) ?_))) ?_
  · rintro x ⟨hx, hxI⟩ x' ⟨hx', hx'I⟩
    exact sn_bf_unique hsn A hA b x x' hx hx' (hxI.trans hx'I.symm)
  · intro x hx
    exact Set.mem_iUnion.mpr ⟨I1 x, hx, rfl⟩
