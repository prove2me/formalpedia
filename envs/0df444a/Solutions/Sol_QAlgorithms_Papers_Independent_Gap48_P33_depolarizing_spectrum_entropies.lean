-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P33.depolarizing_spectrum_entropies
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T23:24:56.883324+00:00
-- url     : https://prove2.me/submissions/79a420e8-b048-4a73-9b5a-9355d50ca9ea

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33



open Polynomial

namespace X6G41D

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma spec_sub (d : n → ℝ) : spectrum ℝ (Matrix.diagonal (fun i => (d i : ℂ))) ⊆ Set.range d := by
  intro μ hμ
  by_contra hc
  rw [spectrum.mem_iff] at hμ
  apply hμ
  have e : (μ • 1 : Matrix n n ℂ) = Matrix.diagonal (fun _ => (μ : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Complex.real_smul]
    · simp [Matrix.one_apply, h]
  rw [Algebra.algebraMap_eq_smul_one, e, Matrix.diagonal_sub,
    Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro i
  simp only [isUnit_iff_ne_zero, ne_eq, sub_eq_zero]
  intro h
  apply hc
  refine ⟨i, ?_⟩
  have := congrArg Complex.re h
  simpa using this.symm

lemma aeval_diag (d : n → ℝ) (P : ℝ[X]) :
    aeval (Matrix.diagonal (fun i => (d i : ℂ))) P =
      Matrix.diagonal (fun i => ((P.eval (d i) : ℝ) : ℂ)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, Matrix.diagonal_add]
  | monomial k a =>
    rw [aeval_monomial, Matrix.diagonal_pow, Algebra.algebraMap_eq_smul_one, smul_one_mul,
      ← Matrix.diagonal_smul]
    congr 1; funext i
    simp only [eval_monomial, Pi.smul_apply, Pi.pow_apply, Complex.real_smul]
    push_cast; ring

lemma cfc_diag (d : n → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  classical
  set S := Finset.univ.image d
  set P := Lagrange.interpolate S id f
  have hP : ∀ i, P.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f)
      (Set.injOn_id _) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    rwa [id] at this
  have hsa : IsSelfAdjoint (Matrix.diagonal (fun i => (d i : ℂ))) := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  rw [cfc_congr (g := fun t => P.eval t), cfc_polynomial P _ hsa, aeval_diag]
  · congr 1; funext i; rw [hP]
  · intro t ht
    obtain ⟨i, rfl⟩ := spec_sub d ht
    exact (hP i).symm

end X6G41D

namespace X6P33S
open QAlgorithms Real Polynomial

theorem roots_eq {κ : Type*} [Fintype κ] (μ : κ → ℝ) :
    (∏ j, (X - C ((μ j : ℝ) : ℂ))).roots = Multiset.map (fun j => ((μ j : ℝ) : ℂ)) Finset.univ.val := by
  rw [Finset.prod_eq_multiset_prod]
  have : Multiset.map (fun j => X - C ((μ j : ℝ) : ℂ)) Finset.univ.val =
      Multiset.map (fun a => X - C a) (Multiset.map (fun j => ((μ j : ℝ) : ℂ)) Finset.univ.val) := by
    rw [Multiset.map_map]; rfl
  rw [this, Polynomial.roots_multiset_prod_X_sub_C]

theorem sum_eig {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    {κ : Type*} [Fintype κ] (μ : κ → ℝ) (h : A.charpoly = ∏ j, (X - C ((μ j : ℝ) : ℂ)))
    (g : ℝ → ℝ) : ∑ i, g (hA.eigenvalues i) = ∑ j, g (μ j) := by
  have h1 := hA.roots_charpoly_eq_eigenvalues
  rw [h, roots_eq] at h1
  have h2 := congrArg (fun s : Multiset ℂ => (s.map (fun z => g z.re)).sum) h1
  simp only [Multiset.map_map] at h2
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  have e1 : Multiset.map (fun i => g (hA.eigenvalues i)) Finset.univ.val =
      Multiset.map ((fun z : ℂ => g z.re) ∘ RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val :=
    Multiset.map_congr rfl (fun x _ => by simp)
  have e2 : Multiset.map (fun j => g (μ j)) Finset.univ.val =
      Multiset.map ((fun z : ℂ => g z.re) ∘ fun j => ((μ j : ℝ) : ℂ)) Finset.univ.val :=
    Multiset.map_congr rfl (fun x _ => by simp)
  rw [e1, e2]; exact h2.symm

theorem vn_charpoly {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    {κ : Type*} [Fintype κ] (μ : κ → ℝ) (h : A.charpoly = ∏ j, (X - C ((μ j : ℝ) : ℂ))) :
    vnEntropy A = ∑ j, negMulLog (μ j) / log 2 := by
  unfold vnEntropy
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal,
    Complex.re_sum, ← Finset.sum_neg_distrib]
  rw [← sum_eig hA μ h (fun x => negMulLog x / log 2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp, negMulLog, Real.logb]
  rw [show ∀ x : ℝ, (RCLike.ofReal x : ℂ).re = x from fun x => Complex.ofReal_re x]
  ring

end X6P33S

namespace X6P33S
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P33 Real Polynomial

def σ1 : Fin 2 ⊕ Fin 2 ≃ Bool × Bool where
  toFun
    | .inl 0 => (false, false) | .inl 1 => (true, true)
    | .inr 0 => (false, true) | .inr 1 => (true, false)
  invFun
    | (false, false) => .inl 0 | (true, true) => .inl 1
    | (false, true) => .inr 0 | (true, false) => .inr 1
  left_inv := by intro x; rcases x with x | x <;> fin_cases x <;> rfl
  right_inv := by intro x; rcases x with ⟨a, b⟩; cases a <;> cases b <;> rfl

theorem quad (u v T D : ℂ) (hT : u + v = T) (hD : u * v = D) :
    (X - C u) * (X - C v) = X ^ 2 - C T * X + C D := by
  subst hT hD; simp only [map_add, map_mul]; ring

theorem charpoly_blocks {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Fin 2 ⊕ Fin 2 ≃ ι)
    (M : Matrix ι ι ℂ) (A D : Matrix (Fin 2) (Fin 2) ℂ)
    (h : Matrix.reindex σ.symm σ.symm M = Matrix.fromBlocks A 0 0 D) :
    M.charpoly = A.charpoly * D.charpoly := by
  rw [← Matrix.charpoly_reindex σ.symm M, h, Matrix.charpoly_fromBlocks_zero₂₁]

theorem out_blocks (p q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Matrix.reindex σ1.symm σ1.symm (depolarizingOutput p q) = Matrix.fromBlocks
      !![((2 * p * (1 - q) / 3 : ℝ) : ℂ), 0; 0, ((2 * p * q / 3 : ℝ) : ℂ)] 0 0
      !![(((1 - q) * (1 - 2 * p / 3) : ℝ) : ℂ),
          ((-(Real.sqrt q * Real.sqrt (1 - q)) * (1 - 4 * p / 3) : ℝ) : ℂ);
        ((-(Real.sqrt q * Real.sqrt (1 - q)) * (1 - 4 * p / 3) : ℝ) : ℂ),
          ((q * (1 - 2 * p / 3) : ℝ) : ℂ)] := by
  have s1 : ((Real.sqrt q : ℂ)) ^ 2 = (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq]
  have s2 : ((Real.sqrt (1 - q) : ℂ)) ^ 2 = 1 - (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [σ1, depolarizingOutput, idTensorSuperop, pauliDepolarizing, pureDensity, pauliX, pauliY,
      pauliZ, qBasis, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.diagonal] <;>
    ring_nf <;> (try simp only [s1, s2, Complex.I_sq]) <;> ring_nf

theorem charpoly2 (a b c d : ℂ) (u v : ℂ) (hT : u + v = a + d) (hD : u * v = a * d - b * c) :
    (!![a, b; c, d]).charpoly = (X - C u) * (X - C v) := by
  rw [Matrix.charpoly_fin_two, quad u v (a + d) (a * d - b * c) hT hD, Matrix.trace_fin_two_of,
    Matrix.det_fin_two_of]

theorem disc_sq (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    QAlgorithms.Papers.Independent.Gap48.P33.discriminant p q ^ 2 = (1 - 2 * p / 3) ^ 2 - (16 / 3 : ℝ) * p * (1 - p) * q * (1 - q) := by
  unfold QAlgorithms.Papers.Independent.Gap48.P33.discriminant
  apply Real.sq_sqrt
  have h1 : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
  have h2 : 0 ≤ p * (1 - p) := by nlinarith
  nlinarith [sq_nonneg (1 - 4 * p / 3)]

theorem spec_charpoly (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) (σ : Fin 2 ⊕ Fin 2 ≃ Bool × Bool)
    (a b c d t : ℝ) (hab : (a = 2 * p * (1 - q) / 3 ∧ b = 2 * p * q / 3) ∨
      (a = 2 * p * q / 3 ∧ b = 2 * p * (1 - q) / 3))
    (hcd : c + d = 1 - 2 * p / 3) (hcd2 : c * d - t ^ 2 = 4 / 3 * p * (1 - p) * q * (1 - q))
    (h : Matrix.reindex σ.symm σ.symm M = Matrix.fromBlocks
      !![(a : ℂ), 0; 0, (b : ℂ)] 0 0 !![(c : ℂ), (t : ℂ); (t : ℂ), (d : ℂ)]) :
    M.charpoly = ∏ j, (X - C ((depolarizingSpectrum p q j : ℝ) : ℂ)) := by
  rw [charpoly_blocks σ M _ _ h, Fin.prod_univ_four]
  have hd := disc_sq p q hp hp1
  simp only [depolarizingSpectrum, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [charpoly2 _ _ _ _ ((2 * p * (1 - q) / 3 : ℝ) : ℂ) ((2 * p * q / 3 : ℝ) : ℂ)
        (by rw [ha, hb] <;> push_cast <;> ring) (by rw [ha, hb] <;> push_cast <;> ring),
      charpoly2 _ _ _ _ (((1 - 2 * p / 3 + QAlgorithms.Papers.Independent.Gap48.P33.discriminant p q) / 2 : ℝ) : ℂ)
        (((1 - 2 * p / 3 - QAlgorithms.Papers.Independent.Gap48.P33.discriminant p q) / 2 : ℝ) : ℂ)
        (by rw [← Complex.ofReal_add, ← Complex.ofReal_add, hcd]; push_cast; ring)
        (by
          rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
          congr 1
          nlinarith [hd, hcd2])]
    ring
  · rw [charpoly2 _ _ _ _ ((2 * p * (1 - q) / 3 : ℝ) : ℂ) ((2 * p * q / 3 : ℝ) : ℂ)
        (by rw [ha, hb] <;> push_cast <;> ring) (by rw [ha, hb] <;> push_cast <;> ring),
      charpoly2 _ _ _ _ (((1 - 2 * p / 3 + QAlgorithms.Papers.Independent.Gap48.P33.discriminant p q) / 2 : ℝ) : ℂ)
        (((1 - 2 * p / 3 - QAlgorithms.Papers.Independent.Gap48.P33.discriminant p q) / 2 : ℝ) : ℂ)
        (by rw [← Complex.ofReal_add, ← Complex.ofReal_add, hcd]; push_cast; ring)
        (by
          rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
          congr 1
          nlinarith [hd, hcd2])]
    ring

end X6P33S

namespace X6P33S
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P33 Real Polynomial
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open scoped ComplexOrder

theorem herm_of_blocks {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Fin 2 ⊕ Fin 2 ≃ ι)
    (M : Matrix ι ι ℂ) (A D : Matrix (Fin 2) (Fin 2) ℂ)
    (h : Matrix.reindex σ.symm σ.symm M = Matrix.fromBlocks A 0 0 D)
    (hA : A.IsHermitian) (hD : D.IsHermitian) : M.IsHermitian := by
  have : M = (Matrix.fromBlocks A 0 0 D).submatrix σ.symm σ.symm := by
    rw [← h]; ext i j; simp
  rw [this]
  exact (Matrix.IsHermitian.fromBlocks hA (by simp) hD).submatrix _

theorem herm2 (a b c : ℝ) : (!![(a : ℂ), (b : ℂ); (b : ℂ), (c : ℂ)]).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

theorem shannon_eq {Y : Type} [Fintype Y] (q : Y → ℝ) :
    shannon q = ∑ i, negMulLog (q i) / log 2 := by
  unfold shannon
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Real.logb, negMulLog]
  ring

theorem vn_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) :
    vnEntropy (Matrix.diagonal fun i => (f i : ℂ)) = ∑ i, negMulLog (f i) / log 2 := by
  unfold vnEntropy
  rw [X6G41D.cfc_diag, Matrix.trace_diagonal, Complex.re_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.ofReal_re, Real.logb, negMulLog]
  ring

theorem h2_eq (x : ℝ) : binEntropy2 x = (negMulLog x + negMulLog (1 - x)) / log 2 := by
  rw [binEntropy2, binEntropy_eq_negMulLog_add_negMulLog_one_sub]

theorem vn_out (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (depolarizingOutput p q).IsHermitian ∧
    (depolarizingOutput p q).charpoly = ∏ j, (X - C ((depolarizingSpectrum p q j : ℝ) : ℂ)) ∧
    vnEntropy (depolarizingOutput p q) = shannon (depolarizingSpectrum p q) := by
  have h := out_blocks p q hq hq1
  have hs : (Real.sqrt q * Real.sqrt (1 - q)) ^ 2 = q * (1 - q) := by
    rw [mul_pow, Real.sq_sqrt hq, Real.sq_sqrt (by linarith)]
  have hc := spec_charpoly p q hp hp1 hq hq1 _ σ1 _ _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (by ring)
    (by rw [mul_pow, neg_sq, hs]; ring) h
  have hH := herm_of_blocks σ1 _ _ _ h (herm2 _ 0 _ |>.symm ▸ by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]) (herm2 _ _ _)
  refine ⟨hH, hc, ?_⟩
  rw [X6P33S.vn_charpoly hH _ hc, shannon_eq]

theorem decomp (p q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    depolarizingOutput p q = ((1 - p : ℝ) : ℂ) • pureDensity (qBasis 0 q) +
      ((p / 3 : ℝ) : ℂ) • (pureDensity (qBasis 1 q) +
        pureDensity (qBasis 2 (1 - q)) + pureDensity (qBasis 3 (1 - q))) := by
  have s1 : ((Real.sqrt q : ℂ)) ^ 2 = (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq]
  have s2 : ((Real.sqrt (1 - q) : ℂ)) ^ 2 = 1 - (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [depolarizingOutput, idTensorSuperop, pauliDepolarizing, pureDensity, pauliX, pauliY,
      pauliZ, qBasis, Matrix.mul_apply, Matrix.diagonal] <;>
    ring_nf <;> (try simp only [s1, s2, Complex.I_sq]) <;> ring_nf

theorem pd_psd {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) : (pureDensity v).PosSemidef := by
  have : pureDensity v = Matrix.vecMulVec (v : ι → ℂ) (star (v : ι → ℂ)) := by
    ext i j; simp [pureDensity, Matrix.vecMulVec_apply]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _

theorem density (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    IsDensityMatrix (depolarizingOutput p q) := by
  refine ⟨?_, ?_⟩
  · rw [decomp p q hq hq1]
    have c1 : (0 : ℂ) ≤ ((1 - p : ℝ) : ℂ) := by exact_mod_cast (by linarith : (0 : ℝ) ≤ 1 - p)
    have c2 : (0 : ℂ) ≤ ((p / 3 : ℝ) : ℂ) := by exact_mod_cast (by positivity : (0 : ℝ) ≤ p / 3)
    exact ((pd_psd _).smul c1).add ((((pd_psd _).add (pd_psd _)).add (pd_psd _)).smul c2)
  · have h := out_blocks p q hq hq1
    have E : ∀ i j, depolarizingOutput p q (σ1 i) (σ1 j) =
        Matrix.reindex σ1.symm σ1.symm (depolarizingOutput p q) i j := fun i j => by simp
    rw [Matrix.trace, ← Equiv.sum_comp σ1]
    simp only [Matrix.diag_apply, E, h, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
    simp
    push_cast; ring

noncomputable def psi2 (q : ℝ) : EuclideanSpace ℂ (Bool × Bool) :=
  WithLp.toLp 2 fun z => if z.1 = z.2 then ((Real.sqrt (if z.1 then 1 - q else q) : ℝ) : ℂ) else 0

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange) in
open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification) in
theorem exch_eq (p q : ℝ) : entropyExchange (pauliDepolarizing p) (diagonalSource q) =
    vnEntropy (idTensorSuperop (R := Bool) (pauliDepolarizing p) (pureDensity (psi2 q))) := by
  unfold entropyExchange
  dsimp only
  set e := Fintype.equivFin Bool
  have hr : ∀ i j, diagonalSource q (e.symm i) (e.symm j) =
      Matrix.diagonal (fun i => (((if e.symm i then 1 - q else q : ℝ)) : ℂ)) i j := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp only [diagonalSource, Matrix.diagonal_apply_eq]; split_ifs <;> simp
    · have : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
      rw [Matrix.diagonal_apply_ne _ hij, diagonalSource, Matrix.diagonal_apply_ne _ this]
  have hr' : (fun i j => diagonalSource q (e.symm i) (e.symm j)) =
      Matrix.diagonal (fun i => (((if e.symm i then 1 - q else q : ℝ)) : ℂ)) := by
    funext i j; exact hr i j
  rw [hr']
  congr 3
  ext z
  simp only [canonicalPurification]
  rw [X6G41D.cfc_diag]
  rcases z with ⟨a, b⟩
  by_cases hab : a = b
  · subst hab; simp only [psi2]; rw [Matrix.diagonal_apply_eq, e.symm_apply_apply]; simp
  · have : e b ≠ e a := fun h => hab (e.injective h).symm
    rw [Matrix.diagonal_apply_ne _ this]
    simp [psi2, hab]

def σ2 : Fin 2 ⊕ Fin 2 ≃ Bool × Bool where
  toFun
    | .inl 0 => (false, true) | .inl 1 => (true, false)
    | .inr 0 => (false, false) | .inr 1 => (true, true)
  invFun
    | (false, true) => .inl 0 | (true, false) => .inl 1
    | (false, false) => .inr 0 | (true, true) => .inr 1
  left_inv := by intro x; rcases x with x | x <;> fin_cases x <;> rfl
  right_inv := by intro x; rcases x with ⟨a, b⟩; cases a <;> cases b <;> rfl

theorem exch_blocks (p q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Matrix.reindex σ2.symm σ2.symm
      (idTensorSuperop (R := Bool) (pauliDepolarizing p) (pureDensity (psi2 q))) = Matrix.fromBlocks
      !![((2 * p * q / 3 : ℝ) : ℂ), 0; 0, ((2 * p * (1 - q) / 3 : ℝ) : ℂ)] 0 0
      !![((q * (1 - 2 * p / 3) : ℝ) : ℂ),
          (((Real.sqrt q * Real.sqrt (1 - q)) * (1 - 4 * p / 3) : ℝ) : ℂ);
        (((Real.sqrt q * Real.sqrt (1 - q)) * (1 - 4 * p / 3) : ℝ) : ℂ),
          (((1 - q) * (1 - 2 * p / 3) : ℝ) : ℂ)] := by
  have s1 : ((Real.sqrt q : ℂ)) ^ 2 = (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq]
  have s2 : ((Real.sqrt (1 - q) : ℂ)) ^ 2 = 1 - (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [σ2, psi2, idTensorSuperop, pauliDepolarizing, pureDensity, pauliX, pauliY,
      pauliZ, Matrix.mul_apply, Matrix.diagonal] <;>
    ring_nf <;> (try simp only [s1, s2, Complex.I_sq]) <;> ring_nf

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange) in
theorem exch_vn (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    entropyExchange (pauliDepolarizing p) (diagonalSource q) = shannon (depolarizingSpectrum p q) := by
  rw [exch_eq]
  have h := exch_blocks p q hq hq1
  have hs : (Real.sqrt q * Real.sqrt (1 - q)) ^ 2 = q * (1 - q) := by
    rw [mul_pow, Real.sq_sqrt hq, Real.sq_sqrt (by linarith)]
  have hc := spec_charpoly p q hp hp1 hq hq1 _ σ2 _ _ _ _ _ (Or.inr ⟨rfl, rfl⟩) (by ring)
    (by rw [mul_pow, hs]; ring) h
  have hH := herm_of_blocks σ2 _ _ _ h (herm2 _ 0 _ |>.symm ▸ by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]) (herm2 _ _ _)
  rw [X6P33S.vn_charpoly hH _ hc, shannon_eq]

theorem tl_out (p q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    traceLeft (depolarizingOutput p q) = Matrix.diagonal (fun b =>
      (((if b then 1 - (q + (2 * p / 3) * (1 - 2 * q)) else q + (2 * p / 3) * (1 - 2 * q)) : ℝ) : ℂ)) := by
  have s1 : ((Real.sqrt q : ℂ)) ^ 2 = (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq]
  have s2 : ((Real.sqrt (1 - q) : ℂ)) ^ 2 = 1 - (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
  ext b c
  cases b <;> cases c <;>
    simp [traceLeft, depolarizingOutput, idTensorSuperop, pauliDepolarizing, pureDensity, pauliX,
      pauliY, pauliZ, qBasis, Matrix.mul_apply, Matrix.diagonal] <;>
    ring_nf <;> (try simp only [s1, s2, Complex.I_sq]) <;> ring_nf

theorem tr_out (p q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    traceRight (depolarizingOutput p q) = Matrix.diagonal (fun b =>
      (((if b then q else 1 - q) : ℝ) : ℂ)) := by
  have s1 : ((Real.sqrt q : ℂ)) ^ 2 = (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq]
  have s2 : ((Real.sqrt (1 - q) : ℂ)) ^ 2 = 1 - (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
  ext b c
  cases b <;> cases c <;>
    simp [traceRight, depolarizingOutput, idTensorSuperop, pauliDepolarizing, pureDensity, pauliX,
      pauliY, pauliZ, qBasis, Matrix.mul_apply, Matrix.diagonal] <;>
    ring_nf <;> (try simp only [s1, s2, Complex.I_sq]) <;> ring_nf

theorem ds_eq (q : ℝ) : diagonalSource q = Matrix.diagonal (fun b => (((if b then 1 - q else q) : ℝ) : ℂ)) := by
  unfold diagonalSource; congr 1; funext b; split_ifs <;> simp

theorem N_ds (p q : ℝ) : pauliDepolarizing p (diagonalSource q) = Matrix.diagonal (fun b =>
      (((if b then 1 - (q + (2 * p / 3) * (1 - 2 * q)) else q + (2 * p / 3) * (1 - 2 * q)) : ℝ) : ℂ)) := by
  ext b c
  cases b <;> cases c <;>
    simp [diagonalSource, pauliDepolarizing, pauliX, pauliY, pauliZ, Matrix.mul_apply, Matrix.diagonal] <;>
    ring_nf <;> (try simp only [Complex.I_sq]) <;> ring_nf

theorem vn_bin (x : ℝ) : vnEntropy (Matrix.diagonal (fun b : Bool =>
      (((if b then 1 - x else x) : ℝ) : ℂ))) = binEntropy2 x := by
  rw [vn_diag, h2_eq, Fintype.sum_bool]; simp; ring

theorem vn_bin' (x : ℝ) : vnEntropy (Matrix.diagonal (fun b : Bool =>
      (((if b then x else 1 - x) : ℝ) : ℂ))) = binEntropy2 x := by
  rw [vn_diag, h2_eq, Fintype.sum_bool]; simp; ring

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange) in
open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation) in
theorem main (p q : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    depolarizingOutput p q = ((1 - p : ℝ) : ℂ) • pureDensity (qBasis 0 q) +
      ((p / 3 : ℝ) : ℂ) • (pureDensity (qBasis 1 q) +
        pureDensity (qBasis 2 (1 - q)) + pureDensity (qBasis 3 (1 - q))) ∧
    IsDensityMatrix (depolarizingOutput p q) ∧
    (depolarizingOutput p q).charpoly =
      (∏ j : Fin 4, (Polynomial.X - Polynomial.C (depolarizingSpectrum p q j : ℂ))) ∧
    vnEntropy (depolarizingOutput p q) = shannon (depolarizingSpectrum p q) ∧
    entropyExchange (pauliDepolarizing p) (diagonalSource q) = shannon (depolarizingSpectrum p q) ∧
    vnEntropy (traceLeft (depolarizingOutput p q)) =
      binEntropy2 (q + (2 * p / 3) * (1 - 2 * q)) ∧
    vnEntropy (diagonalSource q) = binEntropy2 q ∧
    loss (pauliDepolarizing p) (diagonalSource q) = binEntropy2 q -
      binEntropy2 (q + (2 * p / 3) * (1 - 2 * q)) + shannon (depolarizingSpectrum p q) ∧
    mutualInformation (depolarizingOutput p q) =
      2 * binEntropy2 q - loss (pauliDepolarizing p) (diagonalSource q) := by
  obtain ⟨_, hc, hv⟩ := vn_out p q hp hp1 hq hq1
  have hx := exch_vn p q hp hp1 hq hq1
  have htl : vnEntropy (traceLeft (depolarizingOutput p q)) =
      binEntropy2 (q + (2 * p / 3) * (1 - 2 * q)) := by rw [tl_out p q hq hq1, vn_bin]
  have hds : vnEntropy (diagonalSource q) = binEntropy2 q := by rw [ds_eq, vn_bin]
  have hloss : loss (pauliDepolarizing p) (diagonalSource q) = binEntropy2 q -
      binEntropy2 (q + (2 * p / 3) * (1 - 2 * q)) + shannon (depolarizingSpectrum p q) := by
    unfold loss; rw [hds, hx, N_ds, vn_bin]; ring
  refine ⟨decomp p q hq hq1, density p q hp hp1 hq hq1, hc, hv, hx, htl, hds, hloss, ?_⟩
  unfold mutualInformation
  rw [tr_out p q hq hq1, vn_bin', htl, hv, hloss]
  ring

end X6P33S

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P33
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation)
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

theorem solution (p q : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    depolarizingOutput p q = ((1 - p : ℝ) : ℂ) • pureDensity (qBasis 0 q) +
      ((p / 3 : ℝ) : ℂ) • (pureDensity (qBasis 1 q) +
        pureDensity (qBasis 2 (1 - q)) + pureDensity (qBasis 3 (1 - q))) ∧
    IsDensityMatrix (depolarizingOutput p q) ∧
    (depolarizingOutput p q).charpoly =
      (∏ j : Fin 4, (Polynomial.X - Polynomial.C (depolarizingSpectrum p q j : ℂ))) ∧
    vnEntropy (depolarizingOutput p q) = shannon (depolarizingSpectrum p q) ∧
    entropyExchange (pauliDepolarizing p) (diagonalSource q) = shannon (depolarizingSpectrum p q) ∧
    vnEntropy (traceLeft (depolarizingOutput p q)) =
      binEntropy2 (q + (2 * p / 3) * (1 - 2 * q)) ∧
    vnEntropy (diagonalSource q) = binEntropy2 q ∧
    loss (pauliDepolarizing p) (diagonalSource q) = binEntropy2 q -
      binEntropy2 (q + (2 * p / 3) * (1 - 2 * q)) + shannon (depolarizingSpectrum p q) ∧
    mutualInformation (depolarizingOutput p q) =
      2 * binEntropy2 q - loss (pauliDepolarizing p) (diagonalSource q) :=
  X6P33S.main p q hp hp1 hq hq1
