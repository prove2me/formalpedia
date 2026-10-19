-- Prove2me | solution 1 for QAlgorithms.Childs.clockPathMatrix_eigenvalue_localization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T20:47:12.856058+00:00
-- url     : https://prove2.me/submissions/30eaa9d2-b715-4de3-b6d6-4433d6bc315a

import Theorems.Thm_Polynomial_Chebyshev_U_rank_one_root_localization
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Eigenspace.Matrix

open Matrix Polynomial
open Polynomial.Chebyshev
set_option autoImplicit false

private lemma clock_hermitian (k : ℕ) (s : ℝ) :
    (QAlgorithms.clockPathMatrix k s).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  simp only [Matrix.transpose_apply, QAlgorithms.clockPathMatrix, Matrix.of_apply]
  simp only [and_comm, or_comm]

private lemma clock_row (k : ℕ) (s : ℝ) (v : Fin (k+1) → ℝ) (i : Fin (k+1)) :
    (QAlgorithms.clockPathMatrix k s *ᵥ v) i =
      (if i = 0 then (s-1) * v 0 else 0) +
      (if h : 0 < i.val then -s * v ⟨i.val-1, by omega⟩ else 0) +
      (if h : i.val < k then -s * v ⟨i.val+1, by omega⟩ else 0) := by
  have he (j : Fin (k+1)) :
      QAlgorithms.clockPathMatrix k s i j * v j =
        (if i = 0 ∧ j = 0 then (s-1)*v j else 0) +
        (if j.val+1 = i.val then -s*v j else 0) +
        (if i.val+1 = j.val then -s*v j else 0) := by
    simp only [QAlgorithms.clockPathMatrix, Matrix.of_apply]
    split_ifs <;> simp_all
    all_goals omega
  simp only [Matrix.mulVec, dotProduct, he, Finset.sum_add_distrib]
  congr 2
  · by_cases h : i = 0 <;> simp [h]
  · by_cases h : 0 < i.val
    · have hj (j : Fin (k+1)) : j.val+1 = i.val ↔ j = ⟨i.val-1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ := by
        simp only [Fin.ext_iff]; omega
      simp [h, hj]
    · have hj (j : Fin (k+1)) : ¬ j.val+1 = i.val := by omega
      simp [h, hj]
  · by_cases h : i.val < k
    · have hj (j : Fin (k+1)) : i.val+1 = j.val ↔ j = ⟨i.val+1, Nat.succ_lt_succ h⟩ := by
        simp only [Fin.ext_iff]; omega
      simp [h, hj]
    · have hj (j : Fin (k+1)) : ¬ i.val+1 = j.val := by omega
      simp [h, hj]

private lemma cheb_recurrence (n : ℕ) (x : ℝ) :
    (U ℝ ((n+2 : ℕ) : ℤ)).eval x = 2*x*(U ℝ ((n+1 : ℕ) : ℤ)).eval x - (U ℝ n).eval x := by
  have h := congrArg (Polynomial.eval x) (U_add_two ℝ (n : ℤ))
  simpa only [Int.natCast_add, Nat.cast_ofNat, Nat.cast_one, eval_sub, eval_mul, eval_ofNat, eval_X] using h

private lemma clock_cheb_eigenvector (k : ℕ) (hk : 1 ≤ k) (s x a : ℝ)
    (ha : s*a = 1-s)
    (hx : (U ℝ ((k+1 : ℕ) : ℤ)).eval x = a * (U ℝ k).eval x) :
    QAlgorithms.clockPathMatrix k s *ᵥ (fun i => (U ℝ ((k-i.val : ℕ) : ℤ)).eval x) =
      (-2*s*x) • (fun i : Fin (k+1) => (U ℝ ((k-i.val : ℕ) : ℤ)).eval x) := by
  ext i
  rw [clock_row]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hi : i = 0
  · subst i
    simp only [Fin.val_zero, Nat.sub_zero, lt_self_iff_false, ↓reduceDIte, ↓reduceIte]
    simp only [show 0 < k from hk, ↓reduceDIte, zero_add]
    have hr := cheb_recurrence (k-1) x
    rw [show k-1+2 = k+1 by omega, show k-1+1 = k by omega] at hr
    linear_combination -s * hr + s * hx + (U ℝ k).eval x * ha
  · have hpos : 0 < i.val := by
      have hne : i.val ≠ 0 := fun h => hi (Fin.ext h)
      omega
    simp only [hi, ↓reduceIte, hpos, ↓reduceDIte, zero_add]
    by_cases hik : i.val < k
    · simp only [hik, ↓reduceDIte]
      have hr := cheb_recurrence (k-i.val-1) x
      rw [show k-i.val-1+2 = k-(i.val-1) by omega,
        show k-i.val-1+1 = k-i.val by omega,
        show k-i.val-1 = k-(i.val+1) by omega] at hr
      linear_combination -s * hr
    · have hieq : i.val = k := by omega
      simp [hieq, show k-(k-1)=1 by omega]
      ring

private lemma clock_cheb_spectrum (k : ℕ) (hk : 1 ≤ k) (s x a : ℝ)
    (ha : s*a = 1-s)
    (hx : (U ℝ ((k+1 : ℕ) : ℤ)).eval x = a * (U ℝ k).eval x) :
    -2*s*x ∈ spectrum ℝ (QAlgorithms.clockPathMatrix k s) := by
  let v : Fin (k+1) → ℝ := fun i => (U ℝ ((k-i.val : ℕ) : ℤ)).eval x
  have hv : v ≠ 0 := by
    intro h
    have he := congrFun h (Fin.last k)
    simp [v] at he
  have he : Module.End.HasEigenvector (QAlgorithms.clockPathMatrix k s).toLin' (-2*s*x) v := by
    refine ⟨?_, hv⟩
    rw [Module.End.mem_eigenspace_iff]
    exact clock_cheb_eigenvector k hk s x a ha hx
  have := (Module.End.hasEigenvalue_of_hasEigenvector he).mem_spectrum
  rwa [Matrix.spectrum_toLin'] at this

private lemma sorted_spectrum_match {n : ℕ} (f g : Fin n → ℝ)
    (hf : StrictMono f) (hg : Monotone g) (hfg : ∀ i, ∃ j, g j = f i) : f = g := by
  classical
  choose u hu using hfg
  have hinj : Function.Injective u := by
    intro i j hij
    apply hf.injective
    rw [← hu i, ← hu j, hij]
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective u
    ((Finite.injective_iff_bijective).mp hinj)
  have he : g ∘ e = f := funext hu
  have h : g ∘ e = g ∘ Equiv.refl _ :=
    Tuple.unique_monotone (by simpa [he] using hf.monotone) hg
  rw [he] at h
  exact h

private lemma min_eigenvalue_le_diagonal {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (i : Fin n) :
    hA.eigenvalues₀ ⟨n-1, by simp only [Fintype.card_fin]; omega⟩ ≤ A i i := by
  classical
  let c := hA.eigenvalues₀ ⟨n-1, by simp only [Fintype.card_fin]; omega⟩
  have hc (j : Fin n) : c ≤ hA.eigenvalues j := by
    apply hA.eigenvalues₀_antitone
    have hall (p : Fin (Fintype.card (Fin n))) : p.val ≤ n-1 := by
      have hp := p.isLt
      simp only [Fintype.card_fin] at hp
      omega
    exact hall _

  have hD : (Matrix.diagonal (fun j => hA.eigenvalues j - c)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun j => sub_nonneg.mpr (hc j)
  have hP := hD.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  have heq : (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.diagonal (fun j => hA.eigenvalues j - c) *
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).conjTranspose = A - c • 1 := by
    rw [show Matrix.diagonal (fun j => hA.eigenvalues j - c) =
      Matrix.diagonal hA.eigenvalues - c • 1 by ext j l; by_cases h : j=l <;> simp [h]]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    have hs := hA.spectral_theorem
    simp only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq,
      Unitary.conjStarAlgAut_apply] at hs
    change A = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.diagonal hA.eigenvalues *
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).conjTranspose at hs
    have hu : (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
        (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).conjTranspose = 1 :=
      Unitary.coe_mul_star_self hA.eigenvectorUnitary
    rw [← hs, Matrix.mul_one, hu]
  rw [heq] at hP
  simpa using hP.diag_nonneg (i := i)

private lemma diagonal_sorted_eigenvalues {n : ℕ} (d : Fin n → ℝ) (hd : Antitone d)
    (hD : (Matrix.diagonal d).IsHermitian) :
    List.ofFn hD.eigenvalues₀ = List.ofFn d := by
  have hr : (Matrix.diagonal d).charpoly.roots = (List.ofFn d : Multiset ℝ) := by
    rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero (d i))
  rw [← hD.sort_roots_charpoly_eq_eigenvalues₀, hr]
  change ((Multiset.map id (List.ofFn d : Multiset ℝ)).sort (· ≥ ·)) = List.ofFn d
  rw [Multiset.map_id, Multiset.coe_sort]
  exact List.mergeSort_eq_self _ hd.sortedGE_ofFn.pairwise

private lemma clock_zero_spectrum (k : ℕ) (hk : 1 ≤ k) :
    QAlgorithms.ascEigenvalues (QAlgorithms.clockPathMatrix k 0) ⟨0, by simp⟩ = -1 ∧
    QAlgorithms.ascEigenvalues (QAlgorithms.clockPathMatrix k 0) ⟨1, by simpa using Nat.succ_lt_succ hk⟩ = 0 := by
  let d : Fin (k+1) → ℝ := fun i => if i.val = k then -1 else 0
  have hd : Antitone d := by
    intro i j hij
    dsimp [d]
    split_ifs <;> simp_all
    all_goals omega
  have hD : (Matrix.diagonal d).IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    exact IsSelfAdjoint.all _
  have hdiag : QAlgorithms.clockPathMatrix k 0 =
      Matrix.diagonal (fun i : Fin (k+1) => if i = 0 then (-1 : ℝ) else 0) := by
    ext i j
    by_cases hi : i=0 <;> by_cases hj : j=0 <;>
      simp [QAlgorithms.clockPathMatrix, Matrix.diagonal_apply, hi, hj, eq_comm]
  have hc : (QAlgorithms.clockPathMatrix k 0).charpoly = (Matrix.diagonal d).charpoly := by
    rw [hdiag, Matrix.charpoly_diagonal, Matrix.charpoly_diagonal,
      Fin.prod_univ_succ, Fin.prod_univ_castSucc]
    simp [d, Fin.ext_iff, ne_of_lt (Fin.isLt _), mul_comm]
  have he0 : (clock_hermitian k 0).eigenvalues₀ = hD.eigenvalues₀ := by
    apply List.ofFn_injective
    rw [← (clock_hermitian k 0).sort_roots_charpoly_eq_eigenvalues₀,
      ← hD.sort_roots_charpoly_eq_eigenvalues₀, hc]
  have hvals := diagonal_sorted_eigenvalues d hd hD
  have hget (i : Fin (k+1)) : hD.eigenvalues₀ ⟨i.val, by simpa using i.isLt⟩ = d i := by
    have h := congrArg (fun l : List ℝ => l[i.val]?) hvals
    simp only [List.getElem?_ofFn, Fintype.card_fin, dif_pos i.isLt, Option.some.injEq] at h
    convert h using 1
    congr 1
  simp only [QAlgorithms.ascEigenvalues, dif_pos (clock_hermitian k 0), he0]
  constructor
  · have h := hget (Fin.last k)
    simpa [d, Fin.rev, Fintype.card_fin] using h
  · have h := hget ⟨k-1, by omega⟩
    simpa [d, Fin.rev, Fintype.card_fin, show k-1 ≠ k by omega] using h

theorem solution
    (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    let E₀ := QAlgorithms.ascEigenvalues (QAlgorithms.clockPathMatrix k s)
      ⟨0, by simp⟩
    let E₁ := QAlgorithms.ascEigenvalues (QAlgorithms.clockPathMatrix k s)
      ⟨1, by simpa using Nat.succ_lt_succ hk⟩
    E₀ ≤ s - 1 ∧ -2 * s ≤ E₁ ∧
    E₀ ≤ -2 * s * Real.cos (Real.pi / ((k : ℝ) + 2)) ∧
    (s ≤ ((k : ℝ) + 1) / (2 * (k : ℝ) + 3) →
      E₀ ≤ -2 * s ∧
      -2 * s * Real.cos (Real.pi / ((k : ℝ) + 1)) ≤ E₁) ∧
    (∀ θ ∈ Set.Ioo (Real.pi / ((k : ℝ) + 1)) (2 * Real.pi / ((k : ℝ) + 1)),
      0 < s → (1 - s) / s <
        Real.sin (((k : ℝ) + 2) * θ) / Real.sin (((k : ℝ) + 1) * θ) →
      -2 * s * Real.cos θ ≤ E₁) := by
  classical
  dsimp only
  let A := QAlgorithms.clockPathMatrix k s
  have hA := clock_hermitian k s
  let energies : Fin (k+1) → ℝ := fun i => hA.eigenvalues₀ ⟨k-i.val, by simp only [Fintype.card_fin]; omega⟩
  have henergies (i : Fin (k+1)) :
      QAlgorithms.ascEigenvalues A ⟨i.val, by simpa using i.isLt⟩ = energies i := by
    dsimp only [A]
    simp only [QAlgorithms.ascEigenvalues, dif_pos hA, energies]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev, Fintype.card_fin]
    omega
  have hRay : energies 0 ≤ s-1 := by
    have hh := min_eigenvalue_le_diagonal (by omega : 0 < k+1) A hA 0
    simpa [energies, A, QAlgorithms.clockPathMatrix] using hh
  rw [henergies ⟨0, by omega⟩, henergies ⟨1, by omega⟩]
  simp only [Fin.mk_zero]
  by_cases hs0 : s=0
  · have hz := clock_zero_spectrum k hk
    subst s
    rw [henergies ⟨0, by omega⟩, henergies ⟨1, by omega⟩] at hz
    simp only [Fin.mk_zero] at hz
    rcases hz with ⟨h0,h1⟩
    simp [h0,h1]
  · have hsp : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    let a := (1-s)/s
    have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hs.2) hs.1
    have hsa : s*a=1-s := by dsimp [a]; field_simp
    obtain ⟨x,hx,hroot,hpole,hground,hthreshold,htest⟩ :=
      Polynomial.Chebyshev.U_rank_one_root_localization k hk a ha
    have hf : StrictMono (fun i => -2*s*x i) := by
      intro i j hij
      exact mul_lt_mul_of_neg_left (hx hij) (by linarith)
    have hmono : Monotone energies := by
      intro i j hij
      apply hA.eigenvalues₀_antitone
      simp only [Fin.le_def] at hij ⊢
      omega
    have hm : ∀ i, ∃ j, energies j = -2*s*x i := by
      intro i
      have hm := clock_cheb_spectrum k hk s (x i) a hsa (hroot i)
      rw [hA.spectrum_real_eq_range_eigenvalues] at hm
      obtain ⟨j,hj⟩ := hm
      let q : Fin (Fintype.card (Fin (k+1))) :=
        (Fintype.equivOfCardEq (Fintype.card_fin _)).symm j
      have hq : q.val ≤ k := by have h := q.isLt; simp only [Fintype.card_fin] at h; omega
      refine ⟨⟨k-q.val, by omega⟩, ?_⟩
      change hA.eigenvalues₀ _ = _
      convert hj using 1
      congr 1
      apply Fin.ext
      change k-(k-q.val) = q.val
      omega
    have he := sorted_spectrum_match (fun i => -2*s*x i) energies hf hmono hm
    have h0 : energies 0 = -2*s*x 0 := (congrFun he 0).symm
    have h1 : energies ⟨1, by omega⟩ = -2*s*x ⟨1, by omega⟩ := (congrFun he _).symm
    refine ⟨hRay, ?_, ?_, ?_, ?_⟩
    · rw [h1]
      have := mul_le_mul_of_nonpos_left (hpole.trans (Real.cos_le_one _)) (by linarith : -2*s ≤ 0)
      nlinarith
    · rw [h0]
      exact mul_le_mul_of_nonpos_left hground (by linarith)
    · intro hsmall
      have hkpos : (0 : ℝ) < k+1 := by positivity
      have hkden : (0 : ℝ) < 2*k+3 := by positivity
      have hsmall' := (le_div_iff₀ hkden).mp hsmall
      have ht : ((k : ℝ)+2)/((k : ℝ)+1) ≤ a := by
        dsimp [a]
        apply (div_le_div_iff₀ hkpos hsp).mpr
        nlinarith
      constructor
      · rw [h0]
        have ht' := hthreshold ht
        nlinarith
      · rw [h1]
        exact mul_le_mul_of_nonpos_left hpole (by linarith)
    · intro θ hθ _ haθ
      rw [h1]
      exact mul_le_mul_of_nonpos_left (htest θ hθ haθ) (by linarith)
