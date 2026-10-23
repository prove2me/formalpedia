-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.surjectiveHomomorphism
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:47:53.9667+00:00
-- url     : https://prove2.me/submissions/04d496c4-fa92-480b-aa00-549a915e47f6

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

theorem g79b_pure_props {I : Type} [Fintype I] {M : Matrix I I ℂ} (h : IsPure M) :
    Mᴴ = M ∧ M * M = M ∧ M.trace = 1 := by
  obtain ⟨v, hv, rfl⟩ := h
  have hs : ∑ i, (starRingEnd ℂ) (v i) * v i = 1 := by
    have h2 : ∑ i, ‖v i‖ ^ 2 = 1 := by
      have := EuclideanSpace.norm_eq v
      rw [hv] at this
      have h3 := congrArg (· ^ 2) this
      simp only [one_pow] at h3
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))] at h3
      exact h3.symm
    have : ∑ i, (starRingEnd ℂ) (v i) * v i = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [this, h2]; simp
  refine ⟨?_, ?_, ?_⟩
  · ext a b; simp [pureDensity, Matrix.conjTranspose_apply, mul_comm]
  · ext a b
    simp only [pureDensity, Matrix.mul_apply, Matrix.of_apply]
    calc ∑ j, v a * (starRingEnd ℂ) (v j) * (v j * (starRingEnd ℂ) (v b))
        = v a * (starRingEnd ℂ) (v b) * ∑ j, (starRingEnd ℂ) (v j) * v j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ = _ := by rw [hs, mul_one]
  · rw [Matrix.trace]; simp only [Matrix.diag, pureDensity, Matrix.of_apply]
    rw [← hs]; refine Finset.sum_congr rfl fun j _ => ?_; ring

theorem g79b_zero_of_herm_idem_trace_zero {I : Type} [Fintype I] {N : Matrix I I ℂ}
    (hh : Nᴴ = N) (hi : N * N = N) (ht : N.trace = 0) : N = 0 := by
  have : (Nᴴ * N).trace = 0 := by rw [hh, hi, ht]
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp this

theorem g79b_pure_of_props {I : Type} [Fintype I] [DecidableEq I] {M : Matrix I I ℂ}
    (hh : Mᴴ = M) (hi : M * M = M) (ht : M.trace = 1) : IsPure M := by
  obtain ⟨k, -, hk⟩ : ∃ k ∈ (Finset.univ : Finset I), M k k ≠ 0 := by
    apply Finset.exists_ne_zero_of_sum_ne_zero
    rw [show ∑ i, M i i = M.trace from rfl, ht]; exact one_ne_zero
  have hMkk : M k k = ((∑ x, Complex.normSq (M x k) : ℝ) : ℂ) := by
    conv_lhs => rw [← hi]
    rw [Matrix.mul_apply]; push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    have : M k x = (starRingEnd ℂ) (M x k) := by
      conv_lhs => rw [← hh]
      rfl
    rw [this, mul_comm, Complex.mul_conj]
  set r : ℝ := ∑ x, Complex.normSq (M x k) with hr
  have hr0 : r ≠ 0 := by intro h0; apply hk; rw [hMkk, h0]; simp
  have hrpos : 0 < r := lt_of_le_of_ne (Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _) (Ne.symm hr0)
  set E : Matrix I I ℂ := Matrix.single k k 1
  set P : Matrix I I ℂ := ((r : ℂ)⁻¹) • (M * E * M) with hP
  have hEME : E * M * E = (r : ℂ) • E := by
    simp only [E, Matrix.single_mul_mul_single, one_mul, mul_one]
    rw [hMkk, Matrix.smul_single, smul_eq_mul, mul_one]
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
  have hMP : M * P = P := by
    simp only [hP, Matrix.mul_smul, ← Matrix.mul_assoc, hi]
  have hPM : P * M = P := by
    simp only [hP, Matrix.smul_mul, Matrix.mul_assoc, hi]
  have hPP : P * P = P := by
    simp only [hP, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have : M * E * M * (M * E * M) = (r : ℂ) • (M * E * M) := by
      calc M * E * M * (M * E * M) = M * (E * (M * M) * E) * M := by
            simp only [Matrix.mul_assoc]
        _ = (r : ℂ) • (M * E * M) := by
            rw [hi, hEME, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [this, smul_smul]; congr 1; field_simp
  have hPh : Pᴴ = P := by
    simp only [hP, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hh, E,
      Matrix.conjTranspose_single, star_one, Matrix.mul_assoc]
    congr 1; simp
  have htrP : P.trace = 1 := by
    rw [hP, Matrix.trace_smul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hi]
    simp only [E, Matrix.trace_mul_single]
    rw [hMkk]; simp [hrc]
  have hN : M - P = 0 := by
    apply g79b_zero_of_herm_idem_trace_zero
    · rw [Matrix.conjTranspose_sub, hh, hPh]
    · rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hi, hMP, hPM, hPP]; abel
    · rw [Matrix.trace_sub, ht, htrP, sub_self]
  have hMeq : M = P := sub_eq_zero.mp hN
  let w : EuclideanSpace ℂ I := WithLp.toLp 2 fun x => M x k / ((Real.sqrt r : ℝ) : ℂ)
  have hpd : P = pureDensity w := by
    ext a b
    have hsq : ((Real.sqrt r : ℝ) : ℂ) * ((Real.sqrt r : ℝ) : ℂ) = (r : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hrpos.le]
    have hmb : (starRingEnd ℂ) (M b k) = M k b := by
      conv_rhs => rw [← hh]
      rfl
    have hsr : ((Real.sqrt r : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hrpos).ne'
    have hent : (M * E * M) a b = M a k * M k b := by
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      simp only [E, Matrix.mul_apply, Matrix.single_apply]
      rw [Finset.sum_eq_single k]
      · simp
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    simp only [hP, pureDensity, w, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hent]
    rw [map_div₀, Complex.conj_ofReal, hmb]
    field_simp
    rw [sq, hsq]; ring
  refine ⟨w, ?_, by rw [hMeq, hpd]⟩
  have htw : (pureDensity w).trace = 1 := by rw [← hpd, htrP]
  have h2 : ∑ x, ‖w x‖ ^ 2 = 1 := by
    have : (pureDensity w).trace = ((∑ x, ‖w x‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.trace]; push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Matrix.diag, pureDensity, Matrix.of_apply]
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [htw] at this
    exact_mod_cast this.symm
  rw [EuclideanSpace.norm_eq, h2, Real.sqrt_one]

theorem g79b_inb_single {d : ℕ} {blk : Fin d → ℕ} {i j : Fin d} (h : blk i = blk j) (c : ℂ) :
    InBlocks blk (Matrix.single i j c) := by
  intro a b hab
  rw [Matrix.single_apply]
  split_ifs with h1
  · obtain ⟨rfl, rfl⟩ := h1; exact absurd h hab
  · rfl

theorem g79b_inb_mul {d : ℕ} {blk : Fin d → ℕ} {X Y : Matrix (Fin d) (Fin d) ℂ}
    (hX : InBlocks blk X) (hY : InBlocks blk Y) : InBlocks blk (X * Y) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : blk a = blk k
  · rw [hY k b (by rw [← hk]; exact hab), mul_zero]
  · rw [hX a k hk, zero_mul]

theorem g79b_inb_conj {d : ℕ} {blk : Fin d → ℕ} {X : Matrix (Fin d) (Fin d) ℂ}
    (hX : InBlocks blk X) : InBlocks blk Xᴴ := by
  intro a b hab
  rw [Matrix.conjTranspose_apply, hX b a (Ne.symm hab), star_zero]

theorem g79b_f_mul {A B : IntrinsicSystem} (F : Hom A B) {i j k l : Fin A.dim}
    (h1 : A.block i = A.block j) (h2 : A.block k = A.block l) :
    F.map (Matrix.single i j 1) * F.map (Matrix.single k l 1) =
      if j = k then F.map (Matrix.single i l 1) else 0 := by
  rw [← F.mul _ _ (g79b_inb_single h1 1) (g79b_inb_single h2 1)]
  split_ifs with hjk
  · subst hjk; rw [Matrix.single_mul_single_same, one_mul]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ hjk, map_zero]

theorem g79b_f_herm {A B : IntrinsicSystem} (F : Hom A B) {i j : Fin A.dim}
    (h : A.block i = A.block j) :
    (F.map (Matrix.single i j 1))ᴴ = F.map (Matrix.single j i 1) := by
  rw [← F.star _ (g79b_inb_single h 1), Matrix.conjTranspose_single, star_one]

theorem g79b_expand {A B : IntrinsicSystem} (F : Hom A B) (U : Matrix (Fin A.dim) (Fin A.dim) ℂ) :
    F.map U = ∑ i, ∑ j, U i j • F.map (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single U]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

def g79b_t {A B : IntrinsicSystem} (F : Hom A B) (i : Fin A.dim) : ℂ :=
  (F.map (Matrix.single i i 1)).trace

theorem g79b_t01 {A B : IntrinsicSystem} (F : Hom A B)
    (hsurj : ∀ T, InBlocks B.block T → ∃ U, InBlocks A.block U ∧ F.map U = T) (i : Fin A.dim) :
    (g79b_t F i = 0 ∧ F.map (Matrix.single i i 1) = 0) ∨ g79b_t F i = 1 := by
  set f := F.map (Matrix.single i i 1) with hfdef
  have hidem : f * f = f := by rw [hfdef, g79b_f_mul F rfl rfl, if_pos rfl]
  have hherm : fᴴ = f := g79b_f_herm F rfl
  set t := g79b_t F i with htdef
  have htf : t = f.trace := rfl
  have key : ∀ a : Fin B.dim, f a a * (1 - t) = 0 := by
    intro a
    obtain ⟨U, hU, hFU⟩ := hsurj (Matrix.single a a 1) (g79b_inb_single rfl 1)
    have hc : f * Matrix.single a a 1 * f = U i i • f := by
      rw [← hFU, hfdef, ← F.mul _ _ (g79b_inb_single rfl 1) hU,
        ← F.mul _ _ (g79b_inb_mul (g79b_inb_single rfl 1) hU) (g79b_inb_single rfl 1),
        Matrix.single_mul_mul_single, one_mul, mul_one, ← map_smul, Matrix.smul_single,
        smul_eq_mul, mul_one]
    set c := U i i
    have htr : f a a = c * t := by
      have e1 : (f * Matrix.single a a 1 * f).trace = f a a := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hidem, Matrix.trace_mul_single]
        simp
      rw [← e1, hc, Matrix.trace_smul, smul_eq_mul, htf]
    have hsq : (c * c) • f = (f a a * c) • f := by
      have e2 : (f * Matrix.single a a 1 * f) * (f * Matrix.single a a 1 * f) =
          f a a • (f * Matrix.single a a 1 * f) := by
        calc (f * Matrix.single a a 1 * f) * (f * Matrix.single a a 1 * f)
            = f * (Matrix.single a a 1 * (f * f) * Matrix.single a a 1) * f := by
              simp only [Matrix.mul_assoc]
          _ = f a a • (f * Matrix.single a a 1 * f) := by
              rw [hidem, Matrix.single_mul_mul_single, one_mul, mul_one]
              have hs : Matrix.single a a (f a a) = f a a • Matrix.single a a (1 : ℂ) := by
                rw [Matrix.smul_single, smul_eq_mul, mul_one]
              rw [hs, Matrix.mul_smul, Matrix.smul_mul]
      rw [hc, Matrix.smul_mul, Matrix.mul_smul, hidem, smul_smul, smul_smul] at e2
      exact e2
    by_cases hf0 : f = 0
    · have : f a a = 0 := by rw [hf0]; rfl
      rw [this, zero_mul]
    · have hcc : c * c = f a a * c := smul_left_injective ℂ hf0 hsq
      rw [htr] at hcc ⊢
      have : c * c * (1 - t) = 0 := by linear_combination hcc
      have hc0 : c * (1 - t) = 0 := by
        rcases mul_eq_zero.mp (show c * (c * (1 - t)) = 0 by linear_combination this) with h | h
        · rw [h, zero_mul]
        · exact h
      linear_combination t * hc0
  have hsum : t * (1 - t) = 0 := by
    rw [htf, Matrix.trace, Finset.sum_mul]
    exact Finset.sum_eq_zero fun a _ => key a
  rcases mul_eq_zero.mp hsum with h | h
  · left
    refine ⟨h, g79b_zero_of_herm_idem_trace_zero hherm hidem (htf ▸ h)⟩
  · right; linear_combination -h

theorem g79b_t_block {A B : IntrinsicSystem} (F : Hom A B) {i j : Fin A.dim}
    (h : A.block i = A.block j) : g79b_t F i = g79b_t F j := by
  unfold g79b_t
  have e1 : F.map (Matrix.single i j 1) * F.map (Matrix.single j i 1) = F.map (Matrix.single i i 1) := by
    rw [g79b_f_mul F h h.symm, if_pos rfl]
  have e2 : F.map (Matrix.single j i 1) * F.map (Matrix.single i j 1) = F.map (Matrix.single j j 1) := by
    rw [g79b_f_mul F h.symm h, if_pos rfl]
  rw [← e1, ← e2, Matrix.trace_mul_comm]

theorem g79b_f_zero {A B : IntrinsicSystem} (F : Hom A B)
    (hsurj : ∀ T, InBlocks B.block T → ∃ U, InBlocks A.block U ∧ F.map U = T) {i j : Fin A.dim}
    (h : A.block i = A.block j) (ht : g79b_t F i = 0) : F.map (Matrix.single i j 1) = 0 := by
  have hii : F.map (Matrix.single i i 1) = 0 := by
    rcases g79b_t01 F hsurj i with h1 | h1
    · exact h1.2
    · rw [ht] at h1; exact absurd h1 zero_ne_one
  have e : F.map (Matrix.single i i 1) * F.map (Matrix.single i j 1) = F.map (Matrix.single i j 1) := by
    rw [g79b_f_mul F rfl h, if_pos rfl]
  rw [← e, hii, Matrix.zero_mul]

theorem g79b_trace_f {A B : IntrinsicSystem} (F : Hom A B) {i j : Fin A.dim}
    (h : A.block i = A.block j) :
    (F.map (Matrix.single i j 1)).trace = if i = j then g79b_t F i else 0 := by
  split_ifs with hij
  · subst hij; rfl
  · have e : F.map (Matrix.single i j 1) * F.map (Matrix.single j j 1) = F.map (Matrix.single i j 1) := by
      rw [g79b_f_mul F h rfl, if_pos rfl]
    rw [← e, Matrix.trace_mul_comm, g79b_f_mul F rfl h, if_neg (Ne.symm hij), Matrix.trace_zero]

theorem g79b_t_cases {A B : IntrinsicSystem} (F : Hom A B)
    (hsurj : ∀ T, InBlocks B.block T → ∃ U, InBlocks A.block U ∧ F.map U = T) (i : Fin A.dim) :
    g79b_t F i = 0 ∨ g79b_t F i = 1 := by
  rcases g79b_t01 F hsurj i with h | h
  · exact Or.inl h.1
  · exact Or.inr h

def g79b_D {A B : IntrinsicSystem} (F : Hom A B) : Matrix (Fin A.dim) (Fin A.dim) ℂ :=
  Matrix.diagonal (g79b_t F)

theorem g79b_D_comm {A B : IntrinsicSystem} (F : Hom A B) {U : Matrix (Fin A.dim) (Fin A.dim) ℂ}
    (hU : InBlocks A.block U) : g79b_D F * U = U * g79b_D F := by
  ext i j
  rw [g79b_D, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : A.block i = A.block j
  · rw [g79b_t_block F h, mul_comm]
  · rw [hU i j h, mul_zero, zero_mul]

theorem g79b_D_idem {A B : IntrinsicSystem} (F : Hom A B)
    (hsurj : ∀ T, InBlocks B.block T → ∃ U, InBlocks A.block U ∧ F.map U = T) :
    g79b_D F * g79b_D F = g79b_D F := by
  rw [g79b_D, Matrix.diagonal_mul_diagonal]
  congr 1; funext i
  rcases g79b_t_cases F hsurj i with h | h <;> rw [h] <;> simp

theorem g79b_D_herm {A B : IntrinsicSystem} (F : Hom A B)
    (hsurj : ∀ T, InBlocks B.block T → ∃ U, InBlocks A.block U ∧ F.map U = T) :
    (g79b_D F)ᴴ = g79b_D F := by
  rw [g79b_D, Matrix.diagonal_conjTranspose]
  congr 1; funext i
  rcases g79b_t_cases F hsurj i with h | h <;> simp [h]

theorem g79b_D_inb {A B : IntrinsicSystem} (F : Hom A B) {U : Matrix (Fin A.dim) (Fin A.dim) ℂ}
    (hU : InBlocks A.block U) : InBlocks A.block (g79b_D F * U) := by
  intro a b hab
  rw [g79b_D, Matrix.diagonal_mul, hU a b hab, mul_zero]

theorem g79b_restr_F {A B : IntrinsicSystem} (F : Hom A B)
    {U : Matrix (Fin A.dim) (Fin A.dim) ℂ} (hU : InBlocks A.block U) :
    intrinsicRestriction A F.map (F.map U) = g79b_D F * U := by
  ext i j
  rw [g79b_D, Matrix.diagonal_mul]
  unfold intrinsicRestriction
  split_ifs with hij
  · rw [g79b_expand F U, Finset.sum_mul, Matrix.trace_sum]
    have hterm : ∀ k l, (((U k l) • F.map (Matrix.single k l 1)) * F.map (Matrix.single j i 1)).trace
        = if k = i ∧ l = j then g79b_t F i * U i j else 0 := by
      intro k l
      by_cases hkl : A.block k = A.block l
      · rw [Matrix.smul_mul, Matrix.trace_smul, g79b_f_mul F hkl hij.symm]
        split_ifs with h1 h2 h2
        · obtain ⟨rfl, rfl⟩ := h2
          rw [g79b_trace_f F rfl, if_pos rfl, smul_eq_mul, mul_comm]
        · subst h1
          rw [g79b_trace_f F (hkl.trans hij.symm), if_neg (fun h => h2 ⟨h, rfl⟩), smul_zero]
        · exact absurd h2.2 h1
        · rw [Matrix.trace_zero, smul_zero]
      · rw [hU k l hkl, zero_smul, Matrix.zero_mul, Matrix.trace_zero]
        split_ifs with h2
        · obtain ⟨rfl, rfl⟩ := h2; exact absurd hij hkl
        · rfl
    simp only [Matrix.trace_sum, Finset.sum_mul] at *
    simp_rw [hterm]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro l _ hl; simp [hl]
      · simp
    · intro k _ hk; simp [hk]
    · simp
  · rw [hU i j hij, mul_zero]

theorem g79b_restr_add {A B : IntrinsicSystem} (G : Matrix (Fin A.dim) (Fin A.dim) ℂ →ₗ[ℂ] Matrix (Fin B.dim) (Fin B.dim) ℂ)
    (X Y : Matrix (Fin B.dim) (Fin B.dim) ℂ) :
    intrinsicRestriction A G (X + Y) = intrinsicRestriction A G X + intrinsicRestriction A G Y := by
  ext i j
  rw [Matrix.add_apply]
  simp only [intrinsicRestriction]
  split_ifs <;> simp [Matrix.add_mul, Matrix.trace_add]

theorem g79b_restr_smul {A B : IntrinsicSystem} (G : Matrix (Fin A.dim) (Fin A.dim) ℂ →ₗ[ℂ] Matrix (Fin B.dim) (Fin B.dim) ℂ)
    (c : ℂ) (X : Matrix (Fin B.dim) (Fin B.dim) ℂ) :
    intrinsicRestriction A G (c • X) = c • intrinsicRestriction A G X := by
  ext i j
  rw [Matrix.smul_apply]
  simp only [intrinsicRestriction]
  split_ifs <;> simp [Matrix.smul_mul, Matrix.trace_smul]

theorem g79b_restr_zero {A B : IntrinsicSystem} (G : Matrix (Fin A.dim) (Fin A.dim) ℂ →ₗ[ℂ] Matrix (Fin B.dim) (Fin B.dim) ℂ) :
    intrinsicRestriction A G 0 = 0 := by
  ext i j; unfold intrinsicRestriction
  split_ifs <;> simp

theorem g79b_restr_sum {A B : IntrinsicSystem} (G : Matrix (Fin A.dim) (Fin A.dim) ℂ →ₗ[ℂ] Matrix (Fin B.dim) (Fin B.dim) ℂ)
    {m : ℕ} (c : Fin m → ℂ) (X : Fin m → Matrix (Fin B.dim) (Fin B.dim) ℂ) :
    intrinsicRestriction A G (∑ i, c i • X i) = ∑ i, c i • intrinsicRestriction A G (X i) := by
  induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
  | empty => simp [g79b_restr_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, g79b_restr_add, g79b_restr_smul, ih]

theorem g79b_F_D {A B : IntrinsicSystem} (F : Hom A B)
    (hsurj : ∀ T, InBlocks B.block T → ∃ U, InBlocks A.block U ∧ F.map U = T)
    {U : Matrix (Fin A.dim) (Fin A.dim) ℂ} (hU : InBlocks A.block U) :
    F.map (g79b_D F * U) = F.map U := by
  rw [g79b_expand F U, g79b_expand F (g79b_D F * U)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [g79b_D, Matrix.diagonal_mul]
  by_cases h : A.block i = A.block j
  · rcases g79b_t_cases F hsurj i with ht | ht
    · rw [g79b_f_zero F hsurj h ht, smul_zero, smul_zero]
    · rw [ht, one_mul]
  · rw [hU i j h, mul_zero]

theorem g79b_trace_F {A B : IntrinsicSystem} (F : Hom A B)
    {U : Matrix (Fin A.dim) (Fin A.dim) ℂ} (hU : InBlocks A.block U) :
    (F.map U).trace = (g79b_D F * U).trace := by
  rw [g79b_expand F U, Matrix.trace_sum]
  simp only [Matrix.trace_sum, Matrix.trace_smul]
  rw [Matrix.trace, g79b_D]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [g79b_trace_f F rfl, if_pos rfl, smul_eq_mul, Matrix.diag, Matrix.diagonal_mul, mul_comm]
  · intro j _ hj
    by_cases h : A.block i = A.block j
    · rw [g79b_trace_f F h, if_neg (Ne.symm hj), smul_zero]
    · rw [hU i j h, zero_smul]
  · simp

theorem g79b_pure_sandwich {I : Type} [Fintype I] {p : Matrix I I ℂ} (hp : IsPure p)
    (X : Matrix I I ℂ) : p * X * p = (p * X).trace • p := by
  obtain ⟨v, -, rfl⟩ := hp
  ext a b
  simp only [pureDensity, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.trace, Matrix.diag]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem g79b_Dp {A B : IntrinsicSystem} (F : Hom A B) {p : Matrix (Fin A.dim) (Fin A.dim) ℂ}
    (hp : A.IsPureState p) : g79b_D F * p = (p * g79b_D F).trace • p := by
  have hpp := (g79b_pure_props hp.1).2.1
  calc g79b_D F * p = g79b_D F * (p * p) := by rw [hpp]
    _ = (g79b_D F * p) * p := by rw [Matrix.mul_assoc]
    _ = p * g79b_D F * p := by rw [g79b_D_comm F hp.2]
    _ = _ := g79b_pure_sandwich hp.1 _

theorem g79b_Fp {A B : IntrinsicSystem} (F : Hom A B)
    (hsurj : ∀ T, InBlocks B.block T → ∃ U, InBlocks A.block U ∧ F.map U = T)
    {p : Matrix (Fin A.dim) (Fin A.dim) ℂ}
    (hp : A.IsPureState p) (hF : F.map p ≠ 0) : (p * g79b_D F).trace = 1 := by
  have e := g79b_F_D F hsurj hp.2
  rw [g79b_Dp F hp, map_smul] at e
  have : ((p * g79b_D F).trace - 1) • F.map p = 0 := by rw [sub_smul, e, one_smul, sub_self]
  rcases smul_eq_zero.mp this with h | h
  · linear_combination h
  · exact absurd h hF

theorem g79b_part1 {A B : IntrinsicSystem} (F : Hom A B)
    (hsurj : ∀ T, InBlocks B.block T → ∃ U, InBlocks A.block U ∧ F.map U = T)
    {p : Matrix (Fin A.dim) (Fin A.dim) ℂ} (hp : A.IsPureState p) :
    B.IsPureState (F.map p) ∨ F.map p = 0 := by
  by_cases hF : F.map p = 0
  · exact Or.inr hF
  left
  obtain ⟨hh, hi, ht⟩ := g79b_pure_props hp.1
  refine ⟨g79b_pure_of_props ?_ ?_ ?_, F.blocks _ hp.2⟩
  · rw [← F.star _ hp.2, hh]
  · rw [← F.mul _ _ hp.2 hp.2, hi]
  · rw [g79b_trace_F F hp.2, g79b_Dp F hp, Matrix.trace_smul, ht, smul_eq_mul, mul_one,
      g79b_Fp F hsurj hp hF]

/-- Lemma A.6, PDF pp.66-67: all five assertions for a surjective star homomorphism,
including both directions of the diagonalization correspondence. -/
theorem solution {A B : IntrinsicSystem} (F : Hom A B)
    (hsurj : ∀ T, InBlocks B.block T → ∃ U, InBlocks A.block U ∧ F.map U = T) :
    (∀ p, A.IsPureState p → B.IsPureState (F.map p) ∨ F.map p = 0) ∧
    (∀ T, InBlocks A.block T → T.PosSemidef → T.trace.re ≥ (F.map T).trace.re) ∧
    (∀ p q, A.IsPureState p → B.IsPureState q →
      (intrinsicRestriction A F.map (F.map p) = p ∨ F.map p = 0) ∧
      F.map (intrinsicRestriction A F.map (F.map p)) = F.map p ∧ F.map (intrinsicRestriction A F.map q) = q) ∧
    (∀ (rho : Matrix (Fin B.dim) (Fin B.dim) ℂ), B.IsState rho →
      ∀ (m : ℕ) (p : Fin m → ℝ) (P : Fin m → Matrix (Fin A.dim) (Fin A.dim) ℂ),
      Diagonalization A (intrinsicRestriction A F.map rho) p P →
      Diagonalization B rho p (fun i => F.map (P i))) ∧
    (∀ (rho : Matrix (Fin B.dim) (Fin B.dim) ℂ), B.IsState rho →
      ∀ (m : ℕ) (p : Fin m → ℝ) (P : Fin m → Matrix (Fin B.dim) (Fin B.dim) ℂ),
      Diagonalization B rho p P →
      Diagonalization A (intrinsicRestriction A F.map rho) p (fun i => intrinsicRestriction A F.map (P i))) := by
  refine ⟨fun p hp => g79b_part1 F hsurj hp, ?_, ?_, ?_, ?_⟩
  · -- trace nonincreasing
    intro T hT hpsd
    rw [g79b_trace_F F hT, g79b_D, Matrix.trace, Matrix.trace, ge_iff_le, Complex.re_sum, Complex.re_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Matrix.diag, Matrix.diagonal_mul]
    have h0 : 0 ≤ (T i i).re := by
      have := hpsd.diag_nonneg (i := i)
      exact (Complex.nonneg_iff.mp this).1
    rcases g79b_t_cases F hsurj i with ht | ht <;> rw [ht] <;> simp [h0]
  · intro p q hp hq
    refine ⟨?_, ?_, ?_⟩
    · by_cases hF : F.map p = 0
      · exact Or.inr hF
      · left
        rw [g79b_restr_F F hp.2, g79b_Dp F hp, g79b_Fp F hsurj hp hF, one_smul]
    · rw [g79b_restr_F F hp.2, g79b_F_D F hsurj hp.2]
    · obtain ⟨U, hU, rfl⟩ := hsurj q hq.2
      rw [g79b_restr_F F hU, g79b_F_D F hsurj hU]
  · intro rho hrho m p P hD
    obtain ⟨U, hU, rfl⟩ := hsurj rho hrho.2
    rw [g79b_restr_F F hU] at hD
    obtain ⟨hpos, hpure, horth, hsum⟩ := hD
    refine ⟨hpos, fun i => ?_, fun i j hij => ?_, ?_⟩
    · rcases g79b_part1 F hsurj (hpure i) with h | h
      · exact h
      · exfalso
        have hDP : g79b_D F * P i = 0 := by
          rw [← g79b_restr_F F (hpure i).2, h, g79b_restr_zero]
        have hidem := (g79b_pure_props (hpure i).1).2.1
        have e1 : P i * (g79b_D F * U) = (p i : ℂ) • P i := by
          rw [hsum, Matrix.mul_sum]
          rw [Finset.sum_eq_single i]
          · rw [Matrix.mul_smul, hidem]
          · intro j _ hj; rw [Matrix.mul_smul, horth i j (Ne.symm hj), smul_zero]
          · simp
        have e2 : P i * (g79b_D F * U) = 0 := by
          rw [← Matrix.mul_assoc, ← g79b_D_comm F (hpure i).2, hDP, Matrix.zero_mul]
        rw [e2] at e1
        have hp0 : (p i : ℂ) ≠ 0 := by exact_mod_cast (hpos i).ne'
        have : P i = 0 := by
          rcases smul_eq_zero.mp e1.symm with h' | h'
          · exact absurd h' hp0
          · exact h'
        have htr := (g79b_pure_props (hpure i).1).2.2
        rw [this, Matrix.trace_zero] at htr
        exact zero_ne_one htr
    · show F.map (P i) * F.map (P j) = 0
      rw [← F.mul _ _ (hpure i).2 (hpure j).2, horth i j hij, map_zero]
    · rw [← g79b_F_D F hsurj hU, hsum, map_sum]
      simp only [map_smul]
  · intro rho hrho m p P hD
    obtain ⟨hpos, hpure, horth, hsum⟩ := hD
    have hlift : ∀ i, ∃ U, InBlocks A.block U ∧ F.map U = P i := fun i => hsurj (P i) (hpure i).2
    choose U hU hFU using hlift
    have hr : ∀ i, intrinsicRestriction A F.map (P i) = g79b_D F * U i := by
      intro i; rw [← hFU i, g79b_restr_F F (hU i)]
    have hmul : ∀ i j, (g79b_D F * U i) * (g79b_D F * U j) = g79b_D F * (U i * U j) := by
      intro i j
      calc (g79b_D F * U i) * (g79b_D F * U j) = g79b_D F * (U i * g79b_D F) * U j := by
            simp only [Matrix.mul_assoc]
        _ = g79b_D F * (g79b_D F * U i) * U j := by rw [g79b_D_comm F (hU i)]
        _ = _ := by rw [← Matrix.mul_assoc, g79b_D_idem F hsurj, Matrix.mul_assoc]
    refine ⟨hpos, fun i => ?_, fun i j hij => ?_, ?_⟩
    · obtain ⟨hh, hi, ht⟩ := g79b_pure_props (hpure i).1
      refine ⟨g79b_pure_of_props ?_ ?_ ?_, ?_⟩
      · beta_reduce; rw [hr i, Matrix.conjTranspose_mul, g79b_D_herm F hsurj,
          ← g79b_D_comm F (g79b_inb_conj (hU i)), ← g79b_restr_F F (g79b_inb_conj (hU i)),
          F.star _ (hU i), hFU i, hh, hr i]
      · beta_reduce; rw [hr i, hmul, ← g79b_restr_F F (g79b_inb_mul (hU i) (hU i)),
          F.mul _ _ (hU i) (hU i), hFU i, hi, hr i]
      · beta_reduce; rw [hr i, ← g79b_trace_F F (hU i), hFU i, ht]
      · beta_reduce; rw [hr i]; exact g79b_D_inb F (hU i)
    · show intrinsicRestriction A F.map (P i) * intrinsicRestriction A F.map (P j) = 0
      rw [hr i, hr j, hmul, ← g79b_restr_F F (g79b_inb_mul (hU i) (hU j)),
        F.mul _ _ (hU i) (hU j), hFU i, hFU j, horth i j hij, g79b_restr_zero]
    · rw [hsum, g79b_restr_sum]


end
