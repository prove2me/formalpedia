-- Prove2me | solution 1 for OracleStateHSP.fracOracle_unitary_prepares
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:27:11.629444+00:00
-- url     : https://prove2.me/submissions/d9b8c05c-72b9-4401-9088-85623ce2b6bf

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OracleStateHSP_flagZero
import Definitions.Def_OracleStateHSP_phiEps
import Definitions.Def_OracleStateHSP_fracU

open OracleStateHSP QAlgorithms

namespace AuxFracPrep

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

lemma sign_zmod2_add (a b : ZMod 2) :
    (if a = 0 then (1 : ℂ) else -1) * (if b = 0 then (1 : ℂ) else -1) =
      (if a + b = 0 then (1 : ℂ) else -1) := by
  have h10 : ((1 : ZMod 2) ≠ 0) := by decide
  by_cases ha : a = 0
  · subst ha; by_cases hb : b = 0 <;> simp [hb]
  · rw [zmod2_eq_one_of_ne_zero ha]
    by_cases hb : b = 0
    · subst hb; simp [h10]
    · rw [zmod2_eq_one_of_ne_zero hb, zmod2_add_self]; simp [h10]

lemma sign_zmod2_add_one (a : ZMod 2) :
    (if a + 1 = 0 then (1 : ℂ) else -1) = -(if a = 0 then (1 : ℂ) else -1) := by
  have h10 : ((1 : ZMod 2) ≠ 0) := by decide
  by_cases ha : a = 0
  · subst ha; simp [h10]
  · rw [zmod2_eq_one_of_ne_zero ha, zmod2_add_self]; simp [h10]

lemma vm_add_self {m : ℕ} (v : V m) : v + v = 0 := by
  ext i; exact zmod2_add_self (v i)

lemma kr_add_self {r : ℕ} (k : K r) : k + k = 0 := by
  ext i; exact zmod2_add_self (k i)

lemma g_add_self {r m : ℕ} (g : K r × V m) : g + g = 0 :=
  Prod.ext (kr_add_self g.1) (vm_add_self g.2)

lemma vm_neg_eq_self {m : ℕ} (v : V m) : -v = v := by
  rw [neg_eq_iff_add_eq_zero]; exact vm_add_self v

lemma paddedOracle_mul_self (r m : ℕ) (f : V m → V m) :
    paddedOracle r f * paddedOracle r f = 1 := by
  have hneg : -(fun g : K r × V m => f g.2) = (fun g : K r × V m => f g.2) := by
    funext g; exact vm_neg_eq_self (f g.2)
  simpa [paddedOracle, hneg] using xorOracle_mul_neg (fun g : K r × V m => f g.2)

lemma paddedOracle_star (r m : ℕ) (f : V m → V m) :
    star (paddedOracle r f) = paddedOracle r f := by
  ext ⟨p1, p2⟩ ⟨q1, q2⟩
  simp only [Matrix.star_apply, paddedOracle, xorOracle, Matrix.of_apply]
  have hiff : (q1 = p1 ∧ q2 = p2 + f p1.2) ↔ (p1 = q1 ∧ p2 = q2 + f q1.2) := by
    constructor <;> rintro ⟨rfl, h2⟩ <;> refine ⟨rfl, ?_⟩ <;>
      rw [h2, add_assoc, vm_add_self, add_zero]
  by_cases h : p1 = q1 ∧ p2 = q2 + f q1.2
  · rw [if_pos (hiff.mpr h), if_pos h, star_one]
  · rw [if_neg (mt hiff.mp h), if_neg h, star_zero]

def J2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

lemma J2_mul_self : J2 * J2 = -1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [J2, Matrix.mul_apply, Fin.sum_univ_two]

lemma fracOracle_decomp (ε : ℝ) (r m : ℕ) (f : V m → V m) :
    fracOracle ε r f =
      (Real.sqrt (1 - ε) : ℂ) • (1 : Matrix (FlagQ r m) (FlagQ r m) ℂ) +
        (Real.sqrt ε : ℂ) • Matrix.kronecker J2 (paddedOracle r f) := by
  ext ⟨a, x⟩ ⟨b, y⟩
  fin_cases a <;> fin_cases b <;>
    simp [fracOracle, J2, Matrix.one_apply, Prod.ext_iff, Matrix.kroneckerMap_apply]

lemma fracOracle_mem_unitary (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (r m : ℕ) (f : V m → V m) :
    fracOracle ε r f ∈ Matrix.unitaryGroup (FlagQ r m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  set M : Matrix (FlagQ r m) (FlagQ r m) ℂ := Matrix.kronecker J2 (paddedOracle r f)
  have hM_star : star M = -M := by
    ext ⟨a, x⟩ ⟨b, y⟩
    have hp := congr_fun (congr_fun (paddedOracle_star r m f) x) y
    simp only [Matrix.star_apply] at hp
    fin_cases a <;> fin_cases b <;> simp [M, J2, Matrix.star_apply, Matrix.kroneckerMap_apply, hp]
  have hM_sq : M * M = -1 := by
    change Matrix.kroneckerMap (· * ·) J2 (paddedOracle r f) *
        Matrix.kroneckerMap (· * ·) J2 (paddedOracle r f) = -1
    rw [← Matrix.mul_kronecker_mul, J2_mul_self, paddedOracle_mul_self]
    ext ⟨a, x⟩ ⟨b, y⟩
    fin_cases a <;> fin_cases b <;>
      (simp [Matrix.one_apply, Prod.ext_iff, Matrix.kroneckerMap_apply]; try split_ifs <;> simp)
  set c0 : ℂ := (Real.sqrt (1 - ε) : ℂ)
  set c1 : ℂ := (Real.sqrt ε : ℂ)
  have hc0_star : star c0 = c0 := Complex.conj_ofReal _
  have hc1_star : star c1 = c1 := Complex.conj_ofReal _
  have hsq : c0 * c0 + c1 * c1 = 1 := by
    dsimp only [c0, c1]
    norm_cast
    rw [← sq, ← sq, Real.sq_sqrt (by linarith), Real.sq_sqrt hε0.le]
    ring
  rw [fracOracle_decomp, star_add, star_smul, star_smul, star_one, hc0_star, hc1_star, hM_star]
  calc (c0 • (1 : Matrix (FlagQ r m) (FlagQ r m) ℂ) + c1 • M) * (c0 • 1 + c1 • (-M))
      = (c0 * c0) • 1 + (c0 * c1) • (-M) + (c1 * c0) • M + (c1 * c1) • (M * (-M)) := by
          simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one]
          abel
    _ = (c0 * c0 + c1 * c1) • 1 := by
          rw [mul_neg, hM_sq, neg_neg, smul_neg, mul_comm c1 c0, add_smul]
          abel
    _ = 1 := by rw [hsq, one_smul]

noncomputable def hadamardG (r m : ℕ) : Matrix (K r × V m) (K r × V m) ℂ :=
  Matrix.of fun x y =>
    ((Real.sqrt (2 ^ (r + m)))⁻¹ : ℂ) * (if dotG x y = 0 then 1 else -1)

lemma dotG_comm {r m : ℕ} (x y : K r × V m) : dotG x y = dotG y x := by
  simp only [dotG, mul_comm]

lemma dotG_zero_left {r m : ℕ} (y : K r × V m) : dotG (0 : K r × V m) y = 0 := by
  simp [dotG]

lemma dotG_add_left {r m : ℕ} (x y z : K r × V m) : dotG (x + y) z = dotG x z + dotG y z := by
  simp only [dotG, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  abel

lemma dotG_add_right {r m : ℕ} (x y z : K r × V m) : dotG x (y + z) = dotG x y + dotG x z := by
  rw [dotG_comm, dotG_add_left, dotG_comm y x, dotG_comm z x]

lemma sum_sign_dotG {r m : ℕ} (d : K r × V m) :
    (∑ z : K r × V m, (if dotG d z = 0 then (1 : ℂ) else -1)) =
      if d = 0 then (2 ^ (r + m) : ℂ) else 0 := by
  by_cases hd : d = 0
  · subst hd
    simp only [if_true, dotG_zero_left]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin, ← pow_add]
    simp
  · rw [if_neg hd]
    have hne : d.1 ≠ 0 ∨ d.2 ≠ 0 := by
      by_cases h1 : d.1 = 0
      · right; intro h2; exact hd (Prod.ext h1 h2)
      · exact Or.inl h1
    have hex : ∃ e : K r × V m, dotG d e = 1 := by
      rcases hne with h1 | h2
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp h1
        refine ⟨(Pi.single i 1, 0), ?_⟩
        simp [dotG, Pi.single_apply, zmod2_eq_one_of_ne_zero hi]
      · obtain ⟨j, hj⟩ := Function.ne_iff.mp h2
        refine ⟨(0, Pi.single j 1), ?_⟩
        simp [dotG, Pi.single_apply, zmod2_eq_one_of_ne_zero hj]
    obtain ⟨e, he⟩ := hex
    set S : ℂ := ∑ z : K r × V m, (if dotG d z = 0 then (1 : ℂ) else -1)
    have hshift : S = -S := by
      calc S = ∑ z : K r × V m, (if dotG d (z + e) = 0 then (1 : ℂ) else -1) := by
              symm
              exact Equiv.sum_comp (Equiv.addRight e) (fun z => if dotG d z = 0 then (1 : ℂ) else -1)
        _ = ∑ z : K r × V m, -(if dotG d z = 0 then (1 : ℂ) else -1) := by
              refine Finset.sum_congr rfl fun z _ => ?_
              rw [dotG_add_right, he, sign_zmod2_add_one]
        _ = -S := by simp [S, Finset.sum_neg_distrib]
    linear_combination (1 / 2 : ℂ) * hshift

lemma hadamardG_star (r m : ℕ) : star (hadamardG r m) = hadamardG r m := by
  ext x y
  simp only [Matrix.star_apply, hadamardG, Matrix.of_apply, dotG_comm y x]
  split_ifs <;> simp [Complex.conj_ofReal]

lemma hadamardG_mul_self (r m : ℕ) : hadamardG r m * hadamardG r m = 1 := by
  ext x y
  simp only [hadamardG, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  have hterm : ∀ z : K r × V m,
      (((Real.sqrt (2 ^ (r + m)))⁻¹ : ℂ) * (if dotG x z = 0 then 1 else -1)) *
        (((Real.sqrt (2 ^ (r + m)))⁻¹ : ℂ) * (if dotG z y = 0 then 1 else -1)) =
      (((Real.sqrt (2 ^ (r + m)))⁻¹ : ℂ) ^ 2) * (if dotG (x + y) z = 0 then 1 else -1) := by
    intro z
    rw [dotG_comm z y, mul_mul_mul_comm, sign_zmod2_add, ← dotG_add_left, sq]
  simp_rw [hterm, ← Finset.mul_sum, sum_sign_dotG]
  have hxy : x + y = 0 ↔ x = y := by
    constructor
    · intro h
      calc x = x + 0 := (add_zero x).symm
        _ = x + (y + y) := by rw [g_add_self]
        _ = (x + y) + y := (add_assoc x y y).symm
        _ = y := by rw [h, zero_add]
    · rintro rfl; exact g_add_self x
  by_cases h : x = y
  · rw [if_pos (hxy.mpr h), if_pos h]
    have hsq : ((Real.sqrt (2 ^ (r + m)) : ℂ)) ^ 2 = (2 : ℂ) ^ (r + m) := by
      have hr : (Real.sqrt ((2 : ℝ) ^ (r + m))) ^ 2 = (2 : ℝ) ^ (r + m) :=
        Real.sq_sqrt (by positivity)
      exact_mod_cast hr
    have h2ne : (2 : ℂ) ^ (r + m) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [inv_pow, hsq, inv_mul_cancel₀ h2ne]
  · rw [if_neg (mt hxy.mp h), if_neg h, mul_zero]

lemma hadamardW_eq_kronecker (r m : ℕ) :
    hadamardW r m =
      Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ)
        (Matrix.kronecker (hadamardG r m) (1 : Matrix (V m) (V m) ℂ)) := by
  ext ⟨a, ⟨x, u⟩⟩ ⟨b, ⟨y, v⟩⟩
  by_cases hab : a = b
  · subst hab
    by_cases huv : u = v
    · subst huv
      simp [hadamardW, hadamardG, Matrix.kroneckerMap_apply]
    · simp [hadamardW, Matrix.kroneckerMap_apply, huv]
  · simp [hadamardW, Matrix.kroneckerMap_apply, Matrix.one_apply, hab]

lemma hadamardW_mem_unitary (r m : ℕ) :
    hadamardW r m ∈ Matrix.unitaryGroup (FlagQ r m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hsq : hadamardW r m * hadamardW r m = 1 := by
    rw [hadamardW_eq_kronecker]
    unfold Matrix.kronecker
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      one_mul, hadamardG_mul_self, one_mul]
    ext ⟨a, ⟨x, u⟩⟩ ⟨b, ⟨y, v⟩⟩
    by_cases hab : a = b
    · subst hab
      by_cases hxy : x = y
      · subst hxy
        by_cases huv : u = v
        · subst huv; simp [Matrix.kroneckerMap_apply]
        · simp [Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff, huv]
      · simp [Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff, hxy]
    · simp [Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff, hab]
  have hstar : star (hadamardW r m) = hadamardW r m := by
    ext ⟨a, ⟨x, u⟩⟩ ⟨b, ⟨y, v⟩⟩
    simp only [Matrix.star_apply, hadamardW, Matrix.of_apply, dotG_comm y x]
    by_cases h : a = b ∧ u = v
    · rw [if_pos ⟨h.1.symm, h.2.symm⟩, if_pos h]
      split_ifs <;> simp [Complex.conj_ofReal]
    · have h' : ¬ (b = a ∧ v = u) := fun ⟨h1, h2⟩ => h ⟨h1.symm, h2.symm⟩
      rw [if_neg h', if_neg h, star_zero]
  rw [hstar, hsq]

lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A * B) v = act A (act B v) := by
  ext i
  simp [act, Matrix.mulVec_mulVec]

lemma hadamardW_ket_zero (r m : ℕ) :
    act (hadamardW r m) (ket (flagZero r m)) =
      (WithLp.toLp 2 fun p => if p.1 = 0 then uG r m p.2 else 0 : EuclideanSpace ℂ (FlagQ r m)) := by
  ext ⟨a, ⟨x, u⟩⟩
  have hk : ∀ q : FlagQ r m, ket (flagZero r m) q = if q = flagZero r m then 1 else 0 := by
    intro q
    simp [ket, PiLp.single_apply]
  simp only [act, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp]
  simp_rw [hk, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  fin_cases a
  · by_cases hu : u = 0
    · subst hu
      simp [flagZero, hadamardW, uG, dotG]
    · simp [flagZero, hadamardW, uG, hu]
  · simp [flagZero, hadamardW]

lemma fracU_ket_zero (ε : ℝ) (r m : ℕ) (f : V m → V m) :
    act (fracU ε r f) (ket (flagZero r m)) = phiEps ε r f := by
  rw [fracU, act_mul, hadamardW_ket_zero]
  ext ⟨a, ⟨x, u⟩⟩
  simp only [act, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have hz : (∑ q : (K r × V m) × V m,
      fracOracle ε r f (a, (x, u)) (1, q) * (if (1 : Fin 2) = 0 then uG r m q else 0)) = 0 := by
    refine Finset.sum_eq_zero fun q _ => ?_
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    rw [if_neg h10, mul_zero]
  rw [hz, add_zero]
  simp only [if_true]
  fin_cases a
  · have hsum : (∑ q : (K r × V m) × V m,
        fracOracle ε r f (0, (x, u)) (0, q) * uG r m q) =
        (Real.sqrt (1 - ε) : ℂ) * uG r m (x, u) := by
      have hterm : ∀ q : (K r × V m) × V m,
          fracOracle ε r f (0, (x, u)) (0, q) * uG r m q =
          if q = (x, u) then (Real.sqrt (1 - ε) : ℂ) * uG r m (x, u) else 0 := by
        intro q
        by_cases hq : q = (x, u)
        · subst hq; simp [fracOracle]
        · have hqx : (x, u) ≠ q := Ne.symm hq
          simp [fracOracle, hq, hqx]
      simp_rw [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simpa [phiEps] using hsum
  · have hsum : (∑ q : (K r × V m) × V m,
        fracOracle ε r f (1, (x, u)) (0, q) * uG r m q) =
        (Real.sqrt ε : ℂ) * phiF r f (x, u) := by
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      rw [Fintype.sum_prod_type]
      have hinner : ∀ y : K r × V m,
          (∑ b : V m, fracOracle ε r f (1, (x, u)) (0, (y, b)) * uG r m (y, b)) =
          if y = x then (Real.sqrt ε : ℂ) * phiF r f (x, u) else 0 := by
        intro y
        by_cases hy : y = x
        · subst hy
          rw [if_pos rfl, Finset.sum_eq_single (0 : V m)]
          · simp [fracOracle, h10, paddedOracle, xorOracle, uG, phiF]
          · intro b _ hb0
            simp [uG, hb0]
          · simp
        · rw [if_neg hy]
          have hxy : x ≠ y := Ne.symm hy
          refine Finset.sum_eq_zero fun b _ => ?_
          simp [fracOracle, h10, paddedOracle, xorOracle, hxy, hy]
      simp_rw [hinner, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simpa [phiEps, h10] using hsum

lemma fracOracle_im (ε : ℝ) (r m : ℕ) (f : V m → V m) (p q : FlagQ r m) :
    (fracOracle ε r f p q).im = 0 := by
  simp only [fracOracle, Matrix.of_apply, paddedOracle, xorOracle]
  split_ifs <;> simp

lemma hadamardW_im (r m : ℕ) (p q : FlagQ r m) :
    (hadamardW r m p q).im = 0 := by
  simp only [hadamardW, Matrix.of_apply]
  split_ifs <;> simp

lemma fracU_im (ε : ℝ) (r m : ℕ) (f : V m → V m) (p q : FlagQ r m) :
    (fracU ε r f p q).im = 0 := by
  simp only [fracU, Matrix.mul_apply, Complex.im_sum]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [Complex.mul_im, fracOracle_im, hadamardW_im, mul_zero, zero_mul, add_zero]

end AuxFracPrep

theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (r m : ℕ)
    (f : V m → V m) :
    fracOracle ε r f ∈ Matrix.unitaryGroup (FlagQ r m) ℂ ∧
    fracU ε r f ∈ Matrix.unitaryGroup (FlagQ r m) ℂ ∧
    act (hadamardW r m) (ket (flagZero r m)) =
      (WithLp.toLp 2 fun p => if p.1 = 0 then uG r m p.2 else 0 : EuclideanSpace ℂ (FlagQ r m)) ∧
    act (fracU ε r f) (ket (flagZero r m)) = phiEps ε r f ∧
    ∀ p q, (fracU ε r f p q).im = 0 := by
  have hO := AuxFracPrep.fracOracle_mem_unitary ε hε0 hε1 r m f
  have hW := AuxFracPrep.hadamardW_mem_unitary r m
  exact ⟨hO, Submonoid.mul_mem _ hO hW, AuxFracPrep.hadamardW_ket_zero r m,
    AuxFracPrep.fracU_ket_zero ε r m f, AuxFracPrep.fracU_im ε r m f⟩
