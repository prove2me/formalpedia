-- Prove2me | solution 1 for ZlibCrc32.Crcz.holds32_crcBytes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T13:26:01.942014+00:00
-- url     : https://prove2.me/submissions/0469209a-6185-4cfe-bcd3-89bd6875be98

import Definitions.Def_ZlibCrc32_CrczModel
import Definitions.Def_KadatchJenkinsCrc
import Mathlib
import Theorems.Thm_ZlibCrc32_crc_tables_eq
import Theorems.Thm_KadatchJenkins_crc_eq_crc0_add

section
/-! # A bit-level model of zlib's braided `crc32_z` (N = 5, W = 8)

Pure functions on bit vectors that the machine-level proof shows the code computes, and whose
polynomial meaning `Solutions.ZlibCrc32Goal.Math` establishes. -/

namespace ZlibCrc32.Crcz

open Polynomial KadatchJenkins













end ZlibCrc32.Crcz
end

section
/-! # The polynomial layer of the zlib CRC-32 proof -/

namespace ZlibCrc32.Crcz.PartM

open Polynomial KadatchJenkins

/-! ## Basics on `regPoly` and `crc32P` -/

theorem coeff_regPoly {D : ℕ} (r : BitVec D) (n : ℕ) :
    (regPoly r).coeff n = if n < D ∧ r.getLsbD (D - 1 - n) = true then 1 else 0 := by
  unfold regPoly
  rw [finsetSum_coeff]
  simp only [apply_ite (fun p : (ZMod 2)[X] => p.coeff n), coeff_X_pow, coeff_zero]
  split_ifs with h
  · obtain ⟨hn, hb⟩ := h
    rw [Finset.sum_eq_single (⟨D - 1 - n, by omega⟩ : Fin D)]
    · simp only [hb, if_true]; rw [if_pos]; omega
    · intro i _ hi
      split_ifs with h1 h2
      · exfalso; apply hi; ext; simp only; omega
      · rfl
      · rfl
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    split_ifs with h1 h2
    · exfalso; apply h; refine ⟨by omega, ?_⟩; rw [show D - 1 - n = (i : ℕ) by omega]; exact h1
    · rfl
    · rfl

theorem degree_regPoly_lt {D : ℕ} (r : BitVec D) : (regPoly r).degree < D := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_regPoly, if_neg]
  omega

theorem regPoly_xor {D : ℕ} (a b : BitVec D) : regPoly (a ^^^ b) = regPoly a + regPoly b := by
  ext n
  simp only [coeff_add, coeff_regPoly, BitVec.getLsbD_xor]
  by_cases hn : n < D
  · cases a.getLsbD (D - 1 - n) <;> cases b.getLsbD (D - 1 - n) <;> simp [hn] <;> decide
  · simp [hn]

theorem two_eq_zero : (2 : (ZMod 2)[X]) = 0 := by
  rw [← map_ofNat C 2, show (OfNat.ofNat 2 : ZMod 2) = 0 from rfl, map_zero]

theorem neg_eq' (a : (ZMod 2)[X]) : -a = a := by
  linear_combination (-a) * two_eq_zero

theorem crc32P_natDegree : crc32P.natDegree = 32 := by
  unfold crc32P; compute_degree!

theorem crc32P_monic : crc32P.Monic := by
  unfold crc32P; monicity!

theorem crc32P_ne_zero : crc32P ≠ 0 := crc32P_monic.ne_zero

theorem crc32P_degree : crc32P.degree = 32 := by
  rw [Polynomial.degree_eq_natDegree crc32P_ne_zero, crc32P_natDegree]; rfl

theorem crc32P_natDegree_pos : 0 < crc32P.natDegree := by rw [crc32P_natDegree]; omega

theorem regPoly_mod {D : ℕ} (r : BitVec D) (hD : D ≤ 32) : regPoly r % crc32P = regPoly r := by
  rw [Polynomial.mod_eq_self_iff crc32P_ne_zero, crc32P_degree]
  exact lt_of_lt_of_le (degree_regPoly_lt r) (by exact_mod_cast hD)

theorem mul_P_mod (y : (ZMod 2)[X]) : y * crc32P % crc32P = 0 :=
  EuclideanDomain.mod_eq_zero.2 (dvd_mul_left _ _)

theorem add_mul_P_mod (x y : (ZMod 2)[X]) : (x + y * crc32P) % crc32P = x % crc32P := by
  rw [Polynomial.add_mod, mul_P_mod, add_zero]

theorem mod_mul_mod (a c : (ZMod 2)[X]) : a % crc32P * c % crc32P = a * c % crc32P := by
  conv_rhs => rw [← EuclideanDomain.mod_add_div a crc32P]
  rw [add_mul, show crc32P * (a / crc32P) * c = (a / crc32P * c) * crc32P by ring,
    add_mul_P_mod]

theorem add_mod' (a b : (ZMod 2)[X]) : (a + b) % crc32P = a % crc32P + b % crc32P :=
  Polynomial.add_mod a b crc32P

theorem stdU_degree : (stdU 32).degree < (crc32P.natDegree : WithBot ℕ) := by
  rw [crc32P_natDegree, Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  simp only [stdU, finsetSum_coeff, coeff_X_pow]
  apply Finset.sum_eq_zero
  intro k hk
  simp at hk
  rw [if_neg]; omega

theorem coeff_stdU (n : ℕ) : (stdU 32).coeff n = if n < 32 then 1 else 0 := by
  simp only [stdU, finsetSum_coeff, coeff_X_pow]
  rw [Finset.sum_ite_eq]; simp

theorem regPoly_not (x : BitVec 32) : regPoly (~~~x) = regPoly x + stdU 32 := by
  ext n
  simp only [coeff_add, coeff_regPoly, coeff_stdU, BitVec.getLsbD_not]
  by_cases hn : n < 32
  · have : 32 - 1 - n < 32 := by omega
    cases h : x.getLsbD (32 - 1 - n) <;> simp [hn, this, h] <;> decide
  · simp [hn]

theorem holds32_iff (x : BitVec 32) (p : (ZMod 2)[X]) :
    Holds32 (x.setWidth 64) p ↔ regPoly x = p := by
  have h1 : (x.setWidth 64).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_setWidth]; have := x.isLt; omega
  have h2 : (x.setWidth 64).setWidth 32 = x := by
    ext i hi; simp [hi]
  simp only [Holds32, h1, h2, true_and]

/-! ## Messages -/

theorem poly_nil : Message.poly [] = 0 := by simp [Message.poly]

theorem poly_cons (a : ZMod 2) (M : Message) :
    Message.poly (a :: M) = C a * X ^ M.length + M.poly := by
  unfold Message.poly
  refine (Fin.sum_univ_succ (n := M.length) _).trans ?_
  simp only [List.length_cons, List.get_eq_getElem, Fin.val_zero, Fin.val_succ,
    List.getElem_cons_zero, List.getElem_cons_succ]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  omega

theorem poly_append (M₁ M₂ : Message) :
    (M₁ ++ M₂).poly = M₁.poly * X ^ M₂.length + M₂.poly := by
  induction M₁ with
  | nil => simp [poly_nil]
  | cons a M ih =>
    rw [List.cons_append, poly_cons, poly_cons, ih, List.length_append]; ring

theorem ofBytes_append (a b : List (BitVec 8)) :
    Message.ofBytes (a ++ b) = Message.ofBytes a ++ Message.ofBytes b := by
  simp [Message.ofBytes, List.flatMap_append]

theorem ofBytes_cons (a : BitVec 8) (b : List (BitVec 8)) :
    Message.ofBytes (a :: b) = Message.ofBytes [a] ++ Message.ofBytes b := by
  rw [← ofBytes_append]; rfl

theorem length_ofBytes (bs : List (BitVec 8)) : (Message.ofBytes bs).length = 8 * bs.length := by
  induction bs with
  | nil => simp [Message.ofBytes]
  | cons b bs ih =>
    simp only [Message.ofBytes, List.flatMap_cons, List.length_append, List.length_ofFn] at ih ⊢
    rw [ih]; simp; ring

theorem C_ite_mul (p : Prop) [Decidable p] (k : ℕ) :
    C (if p then (1 : ZMod 2) else 0) * X ^ k = if p then X ^ k else 0 := by
  split_ifs <;> simp

theorem poly_ofBytes_single (b : BitVec 8) : (Message.ofBytes [b]).poly = regPoly b := by
  have h : Message.ofBytes [b] = [if b.getLsbD 0 then 1 else 0, if b.getLsbD 1 then 1 else 0,
      if b.getLsbD 2 then 1 else 0, if b.getLsbD 3 then 1 else 0, if b.getLsbD 4 then 1 else 0,
      if b.getLsbD 5 then 1 else 0, if b.getLsbD 6 then 1 else 0, if b.getLsbD 7 then 1 else 0] := by
    simp [Message.ofBytes, List.ofFn_succ]
  rw [h]
  simp only [poly_cons, poly_nil, List.length_cons, List.length_nil, C_ite_mul]
  unfold regPoly
  rw [Fin.sum_univ_eight]
  simp only [add_assoc, add_zero]
  rfl

/-! ## The byte step -/

theorem crc0_def (M : Message) (v : (ZMod 2)[X]) :
    crc0 crc32P M v = (v * X ^ M.length + M.poly * X ^ 32) % crc32P := by
  rw [crc0, crc32P_natDegree]

theorem crc0_append (M₁ M₂ : Message) (v : (ZMod 2)[X]) :
    crc0 crc32P (M₁ ++ M₂) v = crc0 crc32P M₂ (crc0 crc32P M₁ v) := by
  rw [crc0_def, crc0_def, crc0_def, List.length_append, poly_append,
    add_mod' (_ % crc32P * _), mod_mul_mod, ← add_mod']
  exact congrArg (· % crc32P) (by ring)

theorem regPoly_mul_X8 (c : BitVec 32) :
    regPoly c * X ^ 8 = regPoly (c >>> 8) + X ^ 32 * regPoly (c.setWidth 8) := by
  ext n
  simp only [coeff_add, coeff_mul_X_pow', coeff_X_pow_mul', coeff_regPoly,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  by_cases h1 : n < 8
  · simp [show ¬ 8 ≤ n by omega, show ¬ 32 ≤ n by omega,
      BitVec.getLsbD_of_ge c (8 + (32 - 1 - n)) (by omega)]
  by_cases h2 : n < 32
  · have e : 8 + (32 - 1 - n) = 32 - 1 - (n - 8) := by omega
    simp [h2, show 8 ≤ n by omega, show ¬ 32 ≤ n by omega, show n - 8 < 32 by omega, e]
  by_cases h3 : n < 40
  · have e : 8 - 1 - (n - 32) = 32 - 1 - (n - 8) := by omega
    simp [h2, show 8 ≤ n by omega, show 32 ≤ n by omega, show n - 8 < 32 by omega,
      show n - 32 < 8 by omega, e, show 32 - 1 - (n - 8) < 8 by omega]
  · simp [h2, show 8 ≤ n by omega, show 32 ≤ n by omega, show ¬ n - 8 < 32 by omega,
      show ¬ n - 32 < 8 by omega]

theorem regPoly_tstep (c : BitVec 32) (b : BitVec 8) :
    regPoly (tstep c b) = crc0 crc32P (Message.ofBytes [b]) (regPoly c) := by
  have hy : (c ^^^ b.setWidth 32).toNat % 256 = (c.setWidth 8 ^^^ b).toNat := by
    have : (c.setWidth 8 ^^^ b) = (c ^^^ b.setWidth 32).setWidth 8 := by
      ext i hi; simp [show i < 32 by omega]
    rw [this, BitVec.toNat_setWidth]
  unfold tstep T0
  rw [hy, regPoly_xor, (crc_tables_eq.1.2 _ (c.setWidth 8 ^^^ b).isLt), BitVec.ofNat_toNat,
    BitVec.setWidth_eq, crc0_def, crc0_def, poly_ofBytes_single, poly_ofBytes_single,
    regPoly_xor]
  simp only [length_ofBytes, List.length_singleton, mul_one]
  rw [regPoly_mul_X8]
  conv_lhs => rw [← regPoly_mod (c >>> 8) le_rfl, ← add_mod']
  exact congrArg (· % crc32P) (by ring)

theorem regPoly_crcBytes (c : BitVec 32) (bs : List (BitVec 8)) :
    regPoly (crcBytes c bs) = crc0 crc32P (Message.ofBytes bs) (regPoly c) := by
  induction bs generalizing c with
  | nil =>
    simp [crcBytes, crc0_def, Message.ofBytes, poly_nil, regPoly_mod]
  | cons b bs ih =>
    show regPoly (crcBytes (tstep c b) bs) = _
    rw [ih, regPoly_tstep, ofBytes_cons b bs, crc0_append]

theorem crc32Poly_eq (crc : BitVec 32) (bs : List (BitVec 8)) :
    crc32Poly crc bs = crc0 crc32P (Message.ofBytes bs) (regPoly (~~~crc)) + stdU 32 := by
  unfold crc32Poly
  rw [(crc_eq_crc0_add crc32P (stdU 32) crc32P_natDegree_pos stdU_degree (regPoly crc)).1,
    regPoly_not, sub_eq_add_neg, neg_eq']

theorem crcBytes_holds (crc : BitVec 32) (bs : List (BitVec 8)) :
    Holds32 ((~~~ crcBytes (~~~ crc) bs).setWidth 64) (crc32Poly crc bs) := by
  rw [holds32_iff, regPoly_not, regPoly_crcBytes, crc32Poly_eq]

/-! ## `crc_word` -/

/-! ## Words of the buffer -/

/-! ## The braided step -/

/-! ## The braided path -/

end ZlibCrc32.Crcz.PartM

namespace ZlibCrc32.Crcz
end ZlibCrc32.Crcz
end


open ZlibCrc32 ZlibCrc32.Crcz in
theorem solution (crc : BitVec 32) (bs : List (BitVec 8)) :
    Holds32 ((~~~ crcBytes (~~~ crc) bs).setWidth 64) (crc32Poly crc bs) :=

  ZlibCrc32.Crcz.PartM.crcBytes_holds crc bs
