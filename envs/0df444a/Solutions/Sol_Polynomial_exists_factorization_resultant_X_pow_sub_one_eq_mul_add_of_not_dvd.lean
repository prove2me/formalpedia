-- Prove2me | solution 1 for Polynomial.exists_factorization_resultant_X_pow_sub_one_eq_mul_add_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9dc59dcc-1f6a-5d48-ac70-70b23ef9c86e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_factorization_resultant_X_pow_sub_one_eq_mul_add_of_not_dvd

set_option autoImplicit false

open Polynomial Matrix

namespace P2mLTEu

section Val

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

def v (z : ℤ) : ℕ := z.natAbs.factorization ℓ

theorem v_eq (z : ℤ) : v ℓ z = padicValNat ℓ z.natAbs :=
  Nat.factorization_def _ hℓ.out

theorem v_mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : v ℓ (a * b) = v ℓ a + v ℓ b := by
  rw [v_eq, v_eq, v_eq, Int.natAbs_mul,
    padicValNat.mul (Int.natAbs_ne_zero.mpr ha) (Int.natAbs_ne_zero.mpr hb)]

omit hℓ in
theorem v_neg (a : ℤ) : v ℓ (-a) = v ℓ a := by rw [v, v, Int.natAbs_neg]

omit hℓ in
theorem v_units_mul (u : ℤˣ) (a : ℤ) : v ℓ ((u : ℤ) * a) = v ℓ a := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h, v_neg]

omit hℓ in
theorem v_neg_one_pow_mul (n : ℕ) (a : ℤ) : v ℓ ((-1) ^ n * a) = v ℓ a := by
  rcases neg_one_pow_eq_or ℤ n with h | h <;> simp [h, v_neg]

theorem v_pow_self (n : ℕ) : v ℓ ((ℓ : ℤ) ^ n) = n := by
  rw [v_eq, Int.natAbs_pow, Int.natAbs_natCast, padicValNat.prime_pow]

theorem v_eq_zero_of_not_dvd {a : ℤ} (h : ¬ (ℓ : ℤ) ∣ a) : v ℓ a = 0 := by
  rw [v_eq]
  apply padicValNat.eq_zero_of_not_dvd
  rwa [← Int.ofNat_dvd_left]

end Val

section MulMatrix

variable (P : ℤ[X]) (hP : P.Monic)

noncomputable def B : Matrix (Fin P.natDegree) (Fin P.natDegree) ℤ :=
  Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hP).basis (AdjoinRoot.root P)

theorem charpoly_B : (B P hP).charpoly = P := by
  set b := (AdjoinRoot.powerBasis' hP).basis
  have hkill : Polynomial.aeval (AdjoinRoot.root P) (B P hP).charpoly = 0 := by
    apply Algebra.leftMulMatrix_injective b
    rw [← Polynomial.aeval_algHom_apply, map_zero]
    exact Matrix.aeval_self_charpoly _
  have hdvd : P ∣ (B P hP).charpoly := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at hkill
    exact hkill
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hP (Matrix.charpoly_monic _) hdvd ?_
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem det_B : (B P hP).det = (-1) ^ P.natDegree * P.coeff 0 := by
  rw [Matrix.det_eq_sign_charpoly_coeff, charpoly_B, Fintype.card_fin]

variable {r : ℕ}

theorem det_aeval_prod_X_sub_C {L : Type*} [Field L] (M : Matrix (Fin r) (Fin r) L)
    (s : Multiset L) :
    (aeval M (s.map (fun γ => X - C γ)).prod).det =
      (s.map fun γ => (-1 : L) ^ r * M.charpoly.eval γ).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Matrix.det_mul, ih, Multiset.map_cons,
      Multiset.prod_cons]
    congr 1
    have h1 : aeval M (X - C a) = -(Matrix.scalar (Fin r) a - M) := by
      rw [map_sub, aeval_X, aeval_C, neg_sub]; rfl
    rw [h1, Matrix.det_neg, Fintype.card_fin, Matrix.eval_charpoly]

theorem det_aeval_eq_of_isAlgClosed {L : Type*} [Field L] [IsAlgClosed L]
    (M : Matrix (Fin r) (Fin r) L) (G : L[X]) (hG : G.Monic) :
    (aeval M G).det = (-1) ^ (r * G.natDegree) * resultant G M.charpoly := by
  have hsplit : G.Splits := IsAlgClosed.splits G
  have hχdeg : M.charpoly.natDegree = r := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hres : resultant G M.charpoly = (G.roots.map M.charpoly.eval).prod := by
    have := resultant_eq_prod_eval G M.charpoly r (le_of_eq hχdeg) hsplit
    rw [hG.leadingCoeff, one_pow, one_mul] at this
    rw [← this, hχdeg]
  conv_lhs => rw [hsplit.eq_prod_roots_of_monic hG]
  rw [det_aeval_prod_X_sub_C, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    hres, hsplit.natDegree_eq_card_roots, pow_mul]

theorem det_aeval_eq (M : Matrix (Fin r) (Fin r) ℤ) (G : ℤ[X]) (hG : G.Monic) :
    (aeval M G).det = (-1) ^ (r * G.natDegree) * resultant G M.charpoly := by
  set ι : ℤ →+* ℂ := Int.castRingHom ℂ with hι
  have hinj : Function.Injective ι := Int.cast_injective
  apply hinj
  have hL : ι (aeval M G).det = (aeval (M.map ι) (G.map ι)).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    have hcomp : (algebraMap ℂ (Matrix (Fin r) (Fin r) ℂ)).comp ι =
        (ι.mapMatrix).comp (algebraMap ℤ (Matrix (Fin r) (Fin r) ℤ)) := by
      ext c i j
      simp
    have := Polynomial.map_aeval_eq_aeval_map hcomp G M
    rw [RingHom.mapMatrix_apply] at this
    exact this
  rw [hL, det_aeval_eq_of_isAlgClosed (M.map ι) (G.map ι) (hG.map ι), map_mul, map_pow, map_neg,
    map_one, hG.natDegree_map, Matrix.charpoly_map]
  congr 1
  rw [← resultant_map_map G M.charpoly G.natDegree M.charpoly.natDegree ι]
  rw [(Matrix.charpoly_monic M).natDegree_map]

theorem monic_X_pow_sub_one {n : ℕ} (hn : 0 < n) : (X ^ n - 1 : ℤ[X]).Monic := by
  simpa using Polynomial.monic_X_pow_sub_C (1 : ℤ) hn.ne'

theorem det_B_pow_sub_one {n : ℕ} (hn : 0 < n) :
    ((B P hP) ^ n - 1).det =
      (-1) ^ (P.natDegree * (X ^ n - 1 : ℤ[X]).natDegree) * (X ^ n - 1 : ℤ[X]).resultant P := by
  have h := det_aeval_eq (B P hP) (X ^ n - 1) (monic_X_pow_sub_one hn)
  rw [charpoly_B] at h
  rw [← h, map_sub, map_pow, aeval_X, map_one]

theorem v_det_B_pow_sub_one (ℓ : ℕ) [Fact ℓ.Prime] {n : ℕ} (hn : 0 < n) :
    v ℓ ((B P hP) ^ n - 1).det = v ℓ ((X ^ n - 1 : ℤ[X]).resultant P) := by
  rw [det_B_pow_sub_one P hP hn, v_neg_one_pow_mul]

theorem det_B_pow_sub_one_ne_zero {n : ℕ} (hn : 0 < n)
    (hres : (X ^ n - 1 : ℤ[X]).resultant P ≠ 0) : ((B P hP) ^ n - 1).det ≠ 0 := by
  rw [det_B_pow_sub_one P hP hn]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hres

end MulMatrix

section Cong

variable {d : ℕ}

def CongOne (q : ℤ) (M : Matrix (Fin d) (Fin d) ℤ) : Prop :=
  ∃ N : Matrix (Fin d) (Fin d) ℤ, M = 1 + q • N

theorem congOne_one (q : ℤ) : CongOne q (1 : Matrix (Fin d) (Fin d) ℤ) := ⟨0, by simp⟩

theorem CongOne.mul {q : ℤ} {M M' : Matrix (Fin d) (Fin d) ℤ} (h : CongOne q M)
    (h' : CongOne q M') : CongOne q (M * M') := by
  obtain ⟨N, rfl⟩ := h
  obtain ⟨N', rfl⟩ := h'
  refine ⟨N + N' + q • (N * N'), ?_⟩
  rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_add, smul_add, ← mul_smul]
  abel

theorem CongOne.pow {q : ℤ} {M : Matrix (Fin d) (Fin d) ℤ} (h : CongOne q M) (n : ℕ) :
    CongOne q (M ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact congOne_one q
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem CongOne.geom_sum {q : ℤ} {M : Matrix (Fin d) (Fin d) ℤ} (h : CongOne q M) (n : ℕ) :
    ∃ N' : Matrix (Fin d) (Fin d) ℤ,
      ∑ i ∈ Finset.range n, M ^ i = (n : ℤ) • (1 : Matrix (Fin d) (Fin d) ℤ) + q • N' := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨N', hN'⟩ := ih
    obtain ⟨N, hN⟩ := h.pow n
    refine ⟨N' + N, ?_⟩
    rw [Finset.sum_range_succ, hN', hN, Nat.cast_succ, add_smul, one_smul, smul_add]
    abel

theorem CongOne.of_dvd {q q' : ℤ} (hq : q' ∣ q) {M : Matrix (Fin d) (Fin d) ℤ} (h : CongOne q M) :
    CongOne q' M := by
  obtain ⟨t, rfl⟩ := hq
  obtain ⟨N, rfl⟩ := h
  exact ⟨t • N, by rw [smul_smul]⟩

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem not_dvd_det_one_add (N : Matrix (Fin d) (Fin d) ℤ) :
    ¬ (ℓ : ℤ) ∣ (1 + (ℓ : ℤ) • N).det := by
  intro hdvd
  have h0 : (((1 + (ℓ : ℤ) • N).det : ℤ) : ZMod ℓ) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mpr hdvd
  have h1 : (((1 + (ℓ : ℤ) • N).det : ℤ) : ZMod ℓ) = 1 := by
    rw [show (((1 + (ℓ : ℤ) • N).det : ℤ) : ZMod ℓ) = (Int.castRingHom (ZMod ℓ)) (1 + (ℓ : ℤ) • N).det
      from rfl, RingHom.map_det, map_add, map_one, map_zsmul]
    have : ((ℓ : ℤ) • (Int.castRingHom (ZMod ℓ)).mapMatrix N) = 0 := by
      rw [← Int.cast_smul_eq_zsmul (ZMod ℓ)]
      simp
    rw [this, add_zero, Matrix.det_one]
  rw [h0] at h1
  exact zero_ne_one h1

theorem lte_step {M : Matrix (Fin d) (Fin d) ℤ} (h : CongOne ((ℓ : ℤ) ^ 2) M) :
    CongOne ((ℓ : ℤ) ^ 2) (M ^ ℓ) ∧
      ((M ^ ℓ - 1).det ≠ 0 → v ℓ (M ^ ℓ - 1).det = v ℓ (M - 1).det + d) := by
  obtain ⟨N', hS⟩ := h.geom_sum ℓ
  obtain ⟨N, hN⟩ := h
  set S := ∑ i ∈ Finset.range ℓ, M ^ i with hSdef

  have hS' : S = (ℓ : ℤ) • (1 + (ℓ : ℤ) • N') := by
    rw [hS, smul_add, smul_smul, ← pow_two, natCast_zsmul]

  have hgeom : S * (M - 1) = M ^ ℓ - 1 := geom_sum_mul M ℓ
  have hM1 : M - 1 = ((ℓ : ℤ) ^ 2) • N := by rw [hN]; abel
  refine ⟨?_, ?_⟩
  ·
    refine ⟨S * N, ?_⟩
    rw [← Matrix.mul_smul, ← hM1, hgeom]
    abel
  · intro hne
    rw [← hgeom] at hne ⊢
    rw [Matrix.det_mul] at hne ⊢
    have hSne : S.det ≠ 0 := left_ne_zero_of_mul hne
    have hMne : (M - 1).det ≠ 0 := right_ne_zero_of_mul hne
    rw [v_mul ℓ hSne hMne, add_comm]
    congr 1
    rw [hS', Matrix.det_smul, Fintype.card_fin]
    have hu : (1 + (ℓ : ℤ) • N').det ≠ 0 := fun h0 =>
      not_dvd_det_one_add ℓ N' (h0 ▸ dvd_zero _)
    rw [v_mul ℓ (pow_ne_zero _ (by exact_mod_cast hℓ.out.ne_zero)) hu, v_pow_self,
      v_eq_zero_of_not_dvd ℓ (not_dvd_det_one_add ℓ N'), add_zero]

theorem lte {M : Matrix (Fin d) (Fin d) ℤ} (h : CongOne ((ℓ : ℤ) ^ 2) M)
    (hne : ∀ j : ℕ, (M ^ ℓ ^ j - 1).det ≠ 0) (k : ℕ) :
    v ℓ (M ^ ℓ ^ k - 1).det = d * k + v ℓ (M - 1).det := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : CongOne ((ℓ : ℤ) ^ 2) (M ^ ℓ ^ k) := h.pow _
    have hstep := (lte_step ℓ hk).2
    rw [← pow_mul, ← pow_succ] at hstep
    rw [hstep (hne (k + 1)), ih]
    ring

end Cong

section Order

variable {d : ℕ} (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem isUnit_cast_of_not_dvd {z : ℤ} (hz : ¬ (ℓ : ℤ) ∣ z) : IsUnit (z : ZMod (ℓ ^ 2)) := by
  have hn : ¬ ℓ ∣ z.natAbs := by rwa [← Int.ofNat_dvd_left]
  have hu : IsUnit ((z.natAbs : ℕ) : ZMod (ℓ ^ 2)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hℓ.out (by norm_num)).mpr hn
  rcases Int.natAbs_eq z with h | h
  · rw [h, Int.cast_natCast]; exact hu
  · rw [h, Int.cast_neg, Int.cast_natCast]; exact hu.neg

theorem exists_pow_congOne (M : Matrix (Fin d) (Fin d) ℤ) (hM : ¬ (ℓ : ℤ) ∣ M.det) :
    ∃ a : ℕ, 0 < a ∧ CongOne ((ℓ : ℤ) ^ 2) (M ^ a) := by
  haveI : NeZero (ℓ ^ 2) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  set f : ℤ →+* ZMod (ℓ ^ 2) := Int.castRingHom _ with hf
  set Mb : Matrix (Fin d) (Fin d) (ZMod (ℓ ^ 2)) := f.mapMatrix M with hMb
  have hdet : IsUnit Mb.det := by
    rw [hMb, ← RingHom.map_det]
    exact isUnit_cast_of_not_dvd ℓ hM
  have hunit : IsUnit Mb := (Matrix.isUnit_iff_isUnit_det Mb).mpr hdet
  set u : (Matrix (Fin d) (Fin d) (ZMod (ℓ ^ 2)))ˣ := hunit.unit with hu
  refine ⟨orderOf u, orderOf_pos u, ?_⟩
  have hpow : Mb ^ orderOf u = 1 := by
    have h1 : (u : Matrix (Fin d) (Fin d) (ZMod (ℓ ^ 2))) = Mb := hunit.unit_spec
    rw [← h1, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hmap : f.mapMatrix (M ^ orderOf u - 1) = 0 := by
    rw [map_sub, map_pow, map_one, ← hMb, hpow, sub_self]

  have hdvd : ∀ i j, ((ℓ : ℤ) ^ 2) ∣ (M ^ orderOf u - 1) i j := by
    intro i j
    have hij : (((M ^ orderOf u - 1) i j : ℤ) : ZMod (ℓ ^ 2)) = 0 := by
      have := congrFun (congrFun hmap i) j
      simpa [hf] using this
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (ℓ ^ 2)).mp hij
    exact_mod_cast this
  refine ⟨Matrix.of fun i j => (M ^ orderOf u - 1) i j / (ℓ : ℤ) ^ 2, ?_⟩
  ext i j
  have h := Int.ediv_mul_cancel (hdvd i j)
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_comm, h,
    Matrix.sub_apply, add_sub_cancel]

end Order

section PrimeTo

variable {d : ℕ} (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem not_dvd_det_natCast_smul_one_add {j : ℕ} (hj : ¬ ℓ ∣ j) (N : Matrix (Fin d) (Fin d) ℤ) :
    ¬ (ℓ : ℤ) ∣ ((j : ℤ) • (1 : Matrix (Fin d) (Fin d) ℤ) + (ℓ : ℤ) • N).det := by
  intro hdvd
  set A : Matrix (Fin d) (Fin d) ℤ := (j : ℤ) • (1 : Matrix (Fin d) (Fin d) ℤ) + (ℓ : ℤ) • N
    with hA
  have h0 : ((A.det : ℤ) : ZMod ℓ) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mpr hdvd
  have h1 : ((A.det : ℤ) : ZMod ℓ) = (j : ZMod ℓ) ^ d := by
    rw [show ((A.det : ℤ) : ZMod ℓ) = (Int.castRingHom (ZMod ℓ)) A.det from rfl, RingHom.map_det,
      hA, map_add, map_zsmul, map_zsmul, map_one]
    have hℓ0 : ((ℓ : ℤ) • (Int.castRingHom (ZMod ℓ)).mapMatrix N) = 0 := by
      rw [← Int.cast_smul_eq_zsmul (ZMod ℓ)]
      simp
    have hj1 : ((j : ℤ) • (1 : Matrix (Fin d) (Fin d) (ZMod ℓ))) =
        (j : ZMod ℓ) • (1 : Matrix (Fin d) (Fin d) (ZMod ℓ)) := by
      rw [← Int.cast_smul_eq_zsmul (ZMod ℓ), Int.cast_natCast]
    rw [hℓ0, add_zero, hj1, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  rw [h0] at h1
  have hj0 : (j : ZMod ℓ) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  exact pow_ne_zero d hj0 h1.symm

theorem v_det_pow_sub_one_of_not_dvd {M : Matrix (Fin d) (Fin d) ℤ} (h : CongOne (ℓ : ℤ) M)
    {j : ℕ} (hj : ¬ ℓ ∣ j) (hne : (M ^ j - 1).det ≠ 0) :
    v ℓ (M ^ j - 1).det = v ℓ (M - 1).det := by
  obtain ⟨N', hS⟩ := h.geom_sum j
  set S := ∑ i ∈ Finset.range j, M ^ i with hSdef
  have hgeom : S * (M - 1) = M ^ j - 1 := geom_sum_mul M j
  rw [← hgeom, Matrix.det_mul] at hne ⊢
  have hSne : S.det ≠ 0 := left_ne_zero_of_mul hne
  have hMne : (M - 1).det ≠ 0 := right_ne_zero_of_mul hne
  rw [v_mul ℓ hSne hMne, hS, v_eq_zero_of_not_dvd ℓ (not_dvd_det_natCast_smul_one_add ℓ hj N'),
    zero_add]

end PrimeTo

section Main

variable (P : ℤ[X]) (hP : P.Monic) (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

include hP in
theorem mainU (hℓP : ¬ ((ℓ : ℤ) ∣ P.coeff 0))
    (hres : ∀ n : ℕ, 0 < n → (X ^ n - 1 : ℤ[X]).resultant P ≠ 0) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∃ c : ℕ, ∀ j : ℕ, 0 < j → ¬ ℓ ∣ j → ∀ k : ℕ,
        ((X ^ (m₀ * j * ℓ ^ k) - 1 : ℤ[X]).resultant P).natAbs.factorization ℓ =
          P.natDegree * k + c := by

  have hdetB : ¬ (ℓ : ℤ) ∣ (B P hP).det := by
    rw [det_B]
    intro h
    apply hℓP
    have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ.out
    rcases hprime.dvd_or_dvd h with h1 | h1
    · exact absurd (hprime.dvd_of_dvd_pow h1) (by
        rw [Int.dvd_neg]
        exact_mod_cast hℓ.out.one_lt.ne' ∘ Nat.dvd_one.mp)
    · exact h1
  obtain ⟨a, ha, hcong⟩ := exists_pow_congOne ℓ (B P hP) hdetB
  refine ⟨a, ha, v ℓ ((B P hP) ^ a - 1).det, fun j hj hjℓ k => ?_⟩
  set M := (B P hP) ^ (a * j) with hMdef
  have hM : CongOne ((ℓ : ℤ) ^ 2) M := by rw [hMdef, pow_mul]; exact hcong.pow j
  have haj : 0 < a * j := Nat.mul_pos ha hj
  have hne : ∀ i : ℕ, (M ^ ℓ ^ i - 1).det ≠ 0 := by
    intro i
    rw [hMdef, ← pow_mul]
    exact det_B_pow_sub_one_ne_zero P hP (Nat.mul_pos haj (pow_pos hℓ.out.pos i))
      (hres _ (Nat.mul_pos haj (pow_pos hℓ.out.pos i)))

  have hcong1 : CongOne (ℓ : ℤ) ((B P hP) ^ a) :=
    hcong.of_dvd (dvd_pow_self (ℓ : ℤ) two_ne_zero)
  have hMj : v ℓ (M - 1).det = v ℓ ((B P hP) ^ a - 1).det := by
    rw [hMdef, pow_mul]
    refine v_det_pow_sub_one_of_not_dvd ℓ hcong1 hjℓ ?_
    rw [← pow_mul]
    exact det_B_pow_sub_one_ne_zero P hP haj (hres _ haj)
  have hpos : 0 < a * j * ℓ ^ k := Nat.mul_pos haj (pow_pos hℓ.out.pos k)
  have h := lte ℓ hM hne k
  have hlhs : v ℓ (M ^ ℓ ^ k - 1).det =
      ((X ^ (a * j * ℓ ^ k) - 1 : ℤ[X]).resultant P).natAbs.factorization ℓ := by
    rw [hMdef, ← pow_mul]
    exact v_det_B_pow_sub_one P hP ℓ hpos
  rw [← hlhs, h, hMj]

end Main

end P2mLTEu

theorem solution
    (P : Polynomial ℤ) (hP : P.Monic) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ¬ ((ℓ : ℤ) ∣ P.coeff 0))
    (hres : ∀ n : ℕ, 0 < n → (Polynomial.X ^ n - 1 : Polynomial ℤ).resultant P ≠ 0) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∃ c : ℕ, ∀ j : ℕ, 0 < j → ¬ ℓ ∣ j → ∀ k : ℕ,
        ((Polynomial.X ^ (m₀ * j * ℓ ^ k) - 1 : Polynomial ℤ).resultant P).natAbs.factorization ℓ =
          P.natDegree * k + c :=
  P2mLTEu.mainU P hP ℓ hℓ hres

end S_Polynomial_exists_factorization_resultant_X_pow_sub_one_eq_mul_add_of_not_dvd
end P2MW
export P2MW.S_Polynomial_exists_factorization_resultant_X_pow_sub_one_eq_mul_add_of_not_dvd (solution)
