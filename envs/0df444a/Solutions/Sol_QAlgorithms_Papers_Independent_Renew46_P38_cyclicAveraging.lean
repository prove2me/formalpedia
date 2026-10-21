-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P38.cyclicAveraging
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:34:17.429974+00:00
-- url     : https://prove2.me/submissions/5f3a3e6a-a53c-4af9-8ed7-c2bb9bab6375

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38
noncomputable section
open QAlgorithms.Papers.Independent.Renew46.P38


theorem g64e_prim (n : ℕ) (hn : 1 ≤ n) : IsPrimitiveRoot (cyclicRoot n) n := by
  unfold cyclicRoot
  exact Complex.isPrimitiveRoot_exp n (by omega)

theorem g64e_star_mul (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    star (cyclicRoot n ^ m) * cyclicRoot n ^ m = 1 := by
  have h := (g64e_prim n hn).norm'_eq_one (by omega)
  rw [show star (cyclicRoot n ^ m) = (starRingEnd ℂ) (cyclicRoot n ^ m) from rfl,
    Complex.conj_mul', norm_pow, h]; simp

theorem g64e_rootsum (n : ℕ) (hn : 1 ≤ n) (i j : Fin n) :
    ∑ k : Fin n, (star (cyclicRoot n ^ (i.val + 1))) ^ (k.val + 1) *
      (cyclicRoot n ^ (j.val + 1)) ^ (k.val + 1) = if i = j then (n : ℂ) else 0 := by
  set θ := cyclicRoot n
  have hθ := g64e_prim n hn
  set w := star (θ ^ (i.val + 1)) * θ ^ (j.val + 1) with hw
  have hterm : ∀ k : Fin n, (star (θ ^ (i.val + 1))) ^ (k.val + 1) *
      (θ ^ (j.val + 1)) ^ (k.val + 1) = w ^ (k.val + 1) := fun k => by rw [hw, mul_pow]
  simp only [hterm]
  split_ifs with hij
  · subst hij
    have : w = 1 := g64e_star_mul n hn _
    simp [this]
  · have hwn : w ^ n = 1 := by
      have e1 : (θ ^ (j.val+1)) ^ n = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hθ.pow_eq_one, one_pow]
      have e2 : (star (θ ^ (i.val+1))) ^ n = 1 := by
        rw [← star_pow, ← pow_mul, mul_comm, pow_mul, hθ.pow_eq_one, one_pow, star_one]
      rw [hw, mul_pow, e1, e2, one_mul]
    have hw1 : w ≠ 1 := by
      intro h1
      apply hij
      have h2 : θ ^ (j.val + 1) = θ ^ (i.val + 1) := by
        have := congrArg (fun z => θ ^ (i.val + 1) * z) h1
        simp only [hw, ← mul_assoc] at this
        rw [mul_comm (θ ^ (i.val + 1)) (star _), g64e_star_mul n hn] at this
        simpa using this
      rw [pow_succ, pow_succ] at h2
      have hθ0 : θ ≠ 0 := hθ.ne_zero (by omega)
      have h3 := mul_right_cancel₀ hθ0 h2
      exact Fin.ext (hθ.pow_inj i.isLt j.isLt h3.symm)
    rw [Fin.sum_univ_eq_sum_range (fun k => w ^ (k + 1)) n]
    simp_rw [pow_succ, ← Finset.sum_mul, geom_sum_eq hw1, hwn]; simp

theorem g64e_avg (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ) (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) (Operators H)) :
    IsUnitaryMatrix (cyclicE n) ∧ IsUnitaryMatrix (operatorCyclicE H n) ∧
    (n : ℂ)⁻¹ • (∑ k : Fin n,
      (star (operatorCyclicE H n)) ^ (k.val + 1) * A *
        (operatorCyclicE H n) ^ (k.val + 1)) = Matrix.diagonal (fun i => A i i) := by
  have hs := g64e_star_mul n hn
  have hs' : ∀ m, cyclicRoot n ^ m * star (cyclicRoot n ^ m) = 1 := fun m => by
    rw [mul_comm]; exact hs m
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · simp only [cyclicE, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]; congr 1; funext i; exact hs _
  · simp only [cyclicE, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]; congr 1; funext i; exact hs' _
  · simp only [operatorCyclicE, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]; congr 1; funext i
    simp only [Pi.star_apply, star_smul, star_one, smul_mul_smul_comm, mul_one]
    rw [hs, one_smul]
  · simp only [operatorCyclicE, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]; congr 1; funext i
    simp only [Pi.star_apply, star_smul, star_one, smul_mul_smul_comm, mul_one]
    rw [hs', one_smul]
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.smul_apply, Matrix.sum_apply]
    have hk : ∀ k : Fin n, ((star (operatorCyclicE H n)) ^ (k.val+1) * A *
        (operatorCyclicE H n) ^ (k.val+1)) i j =
        ((star (cyclicRoot n ^ (i.val+1))) ^ (k.val+1) * (cyclicRoot n ^ (j.val+1)) ^ (k.val+1)) • A i j := by
      intro k
      simp only [operatorCyclicE, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_pow, Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.pow_apply, Pi.star_apply,
        star_smul, star_one, smul_pow, one_pow, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
        smul_smul]
      (try congr 1) <;> (try simp only [star_pow]) <;> (try ring)
    rw [Finset.sum_congr rfl (fun k _ => hk k), ← Finset.sum_smul, g64e_rootsum n hn i j,
      Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast (show n ≠ 0 by omega)), one_smul]
    · simp

theorem g64e_Qentry (n : ℕ) (k : Fin n) (i j : Fin n) :
    cyclicProjection n k i j = (star (cyclicRoot n ^ (i.val + 1))) ^ (k.val + 1) * (n : ℂ)⁻¹ *
      (cyclicRoot n ^ (j.val + 1)) ^ (k.val + 1) := by
  simp only [cyclicProjection, cyclicE, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_pow, Matrix.diagonal_mul, Matrix.mul_diagonal, uniformProjection, Pi.pow_apply,
    Pi.star_apply]

theorem g64e_rank_unif (n : ℕ) (hn : 1 ≤ n) :
    Set.range (Matrix.mulVec (uniformProjection n)) =
      (Submodule.span ℂ ({fun _ : Fin n => (1 : ℂ)} : Set (Fin n → ℂ)) : Set (Fin n → ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  ext v
  simp only [Set.mem_range, SetLike.mem_coe, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨(n : ℂ)⁻¹ * ∑ i, w i, ?_⟩
    ext i; simp [Matrix.mulVec, dotProduct, uniformProjection, Finset.mul_sum]
  · rintro ⟨c, rfl⟩
    refine ⟨fun _ => c, ?_⟩
    ext i; simp [Matrix.mulVec, dotProduct, uniformProjection]
    field_simp

theorem g64e_proj (n : ℕ) (hn : 1 ≤ n) :
    IsStarProjection (uniformProjection n) ∧ (uniformProjection n).rank = 1 ∧
    (Set.range (Matrix.mulVec (uniformProjection n)) =
      (Submodule.span ℂ ({fun _ : Fin n => (1 : ℂ)} : Set (Fin n → ℂ)) :
        Set (Fin n → ℂ))) ∧
    (∀ k : Fin n, IsStarProjection (cyclicProjection n k) ∧ (cyclicProjection n k).rank = 1) ∧
    (∀ k l : Fin n, k ≠ l → cyclicProjection n k * cyclicProjection n l = 0) ∧
    (∑ k : Fin n, cyclicProjection n k) = 1 := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hR := g64e_rank_unif n hn
  have hrank : (uniformProjection n).rank = 1 := by
    rw [Matrix.rank]
    have : LinearMap.range (uniformProjection n).mulVecLin =
        Submodule.span ℂ ({fun _ : Fin n => (1 : ℂ)} : Set (Fin n → ℂ)) := by
      refine SetLike.ext fun v => ?_
      rw [LinearMap.mem_range, ← SetLike.mem_coe, ← hR]
      simp [Matrix.mulVecLin_apply]
    rw [this, finrank_span_singleton]
    intro h; have := congrFun h ⟨0, by omega⟩; simp at this
  -- products: entries
  have hprod : ∀ k l : Fin n, cyclicProjection n k * cyclicProjection n l =
      if k = l then cyclicProjection n k else 0 := by
    intro k l
    ext i j
    rw [Matrix.mul_apply]
    simp only [g64e_Qentry]
    have hsum := g64e_rootsum n hn l k
    have hre : ∀ m : Fin n, (star (cyclicRoot n ^ (i.val + 1))) ^ (k.val + 1) * (n : ℂ)⁻¹ *
        (cyclicRoot n ^ (m.val + 1)) ^ (k.val + 1) *
        ((star (cyclicRoot n ^ (m.val + 1))) ^ (l.val + 1) * (n : ℂ)⁻¹ *
        (cyclicRoot n ^ (j.val + 1)) ^ (l.val + 1)) =
        ((star (cyclicRoot n ^ (i.val + 1))) ^ (k.val + 1) * (n : ℂ)⁻¹ * (n : ℂ)⁻¹ *
        (cyclicRoot n ^ (j.val + 1)) ^ (l.val + 1)) *
        ((star (cyclicRoot n ^ (l.val + 1))) ^ (m.val + 1) * (cyclicRoot n ^ (k.val + 1)) ^ (m.val + 1)) := by
      intro m
      simp only [star_pow, ← pow_mul]
      rw [mul_comm (m.val + 1) (k.val + 1), mul_comm (m.val + 1) (l.val + 1)]; ring
    simp only [hre, ← Finset.mul_sum, hsum]
    by_cases h : k = l
    · subst h; rw [if_pos rfl, if_pos rfl, g64e_Qentry]; field_simp
    · rw [if_neg (Ne.symm h), if_neg h]; simp
  refine ⟨⟨?_, ?_⟩, hrank, hR, fun k => ⟨⟨?_, ?_⟩, ?_⟩, fun k l h => by rw [hprod, if_neg h], ?_⟩
  · unfold IsIdempotentElem; ext i j
    simp [Matrix.mul_apply, uniformProjection]; field_simp
  · ext i j; simp [uniformProjection, Matrix.star_apply]
  · unfold IsIdempotentElem; rw [hprod, if_pos rfl]
  · ext i j
    rw [Matrix.star_apply, g64e_Qentry, g64e_Qentry]
    simp only [star_mul', star_pow, star_star, star_inv₀, star_natCast]; ring
  · unfold cyclicProjection
    have hdet : ∀ m, IsUnit ((cyclicE n) ^ m).det := fun m => by
      rw [Matrix.det_pow, cyclicE, Matrix.det_diagonal]
      exact (IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ =>
        pow_ne_zero _ ((g64e_prim n hn).ne_zero (by omega)))).pow m
    have hdet' : ∀ m, IsUnit ((star (cyclicE n)) ^ m).det := fun m => by
      rw [Matrix.det_pow, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
      have h1 : IsUnit (cyclicE n).det := by simpa using hdet 1
      exact (h1.star).pow m
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (hdet _),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (hdet' _), hrank]
  · ext i j
    rw [Matrix.sum_apply]
    simp only [g64e_Qentry]
    have := g64e_rootsum n hn i j
    have hre : ∀ k : Fin n, (star (cyclicRoot n ^ (i.val + 1))) ^ (k.val + 1) * (n : ℂ)⁻¹ *
      (cyclicRoot n ^ (j.val + 1)) ^ (k.val + 1) = (n : ℂ)⁻¹ * ((star (cyclicRoot n ^ (i.val + 1))) ^ (k.val + 1) *
      (cyclicRoot n ^ (j.val + 1)) ^ (k.val + 1)) := fun k => by ring
    simp only [hre, ← Finset.mul_sum, this, Matrix.one_apply]
    split_ifs <;> simp [hn0]



open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

open QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, Lemma 3.1, PDF p. 6, display (13).
Operator-valued blocks are arbitrary. Powers k.val+1 cover exactly k=1,...,n. -/
theorem solution (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ) (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) (Operators H)) :
    IsUnitaryMatrix (cyclicE n) ∧ IsUnitaryMatrix (operatorCyclicE H n) ∧
    (n : ℂ)⁻¹ • (∑ k : Fin n,
      (star (operatorCyclicE H n)) ^ (k.val + 1) * A *
        (operatorCyclicE H n) ^ (k.val + 1)) = Matrix.diagonal (fun i => A i i) := by
  exact g64e_avg H n hn A


end
