-- Prove2me | solution 1 for ZlibCrc32.Crcz.holds32_braidedResult
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T13:26:03.090564+00:00
-- url     : https://prove2.me/submissions/b95d55b1-0854-49e1-b6f6-9a9b777510b1

import Definitions.Def_ZlibCrc32_CrczModel
import Mathlib
import Theorems.Thm_ZlibCrc32_crc_tables_eq
import Theorems.Thm_KadatchJenkins_crc0_interleaved_fold
import Theorems.Thm_KadatchJenkins_crc0_interleaved
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

theorem regPoly_zero {D : ℕ} : regPoly (0#D) = 0 := by
  unfold regPoly; simp

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

/-! ## `crc_word` -/

theorem wstep_xor (c : BitVec 32) (u : BitVec 64) :
    wstep (c.setWidth 64 ^^^ u) = (tstep c (u.setWidth 8)).setWidth 64 ^^^ (u >>> 8) := by
  have hi : (c.setWidth 64 ^^^ u).toNat % 256 = (c ^^^ (u.setWidth 8).setWidth 32).toNat % 256 := by
    have h1 : ∀ {n} (x : BitVec n), x.toNat % 256 = (x.setWidth 8).toNat := by
      intro n x; rw [BitVec.toNat_setWidth]
    rw [h1, h1]
    congr 1
    ext j hj
    simp [show j < 32 by omega, show j < 64 by omega, hj]
  unfold wstep tstep
  rw [hi]
  ext j hj
  simp

theorem wbytes_take_succ (w : BitVec 64) (k : ℕ) (hk : k < 8) :
    (wbytes w).take (k + 1) = (wbytes w).take k ++ [w.extractLsb' (8 * k) 8] := by
  rw [List.take_add_one]
  congr 1
  simp [wbytes, hk]

theorem wstep_iter (c : BitVec 32) (w : BitVec 64) (k : ℕ) (hk : k ≤ 8) :
    wstep^[k] (c.setWidth 64 ^^^ w) =
      (crcBytes c ((wbytes w).take k)).setWidth 64 ^^^ (w >>> (8 * k)) := by
  induction k with
  | zero => simp [crcBytes]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (by omega), wstep_xor, wbytes_take_succ w k (by omega)]
    have e1 : (w >>> (8 * k)).setWidth 8 = w.extractLsb' (8 * k) 8 := by
      ext j hj; simp [hj, show j < 64 by omega]
    have e2 : w >>> (8 * k) >>> 8 = w >>> (8 * (k + 1)) := by
      rw [← BitVec.shiftRight_add, Nat.mul_succ]
    rw [e1, e2, crcBytes, crcBytes, List.foldl_append]
    rfl

theorem crcWord_eq (c : BitVec 32) (w : BitVec 64) : crcWord c w = crcBytes c (wbytes w) := by
  unfold crcWord
  rw [wstep_iter c w 8 le_rfl]
  have h1 : (wbytes w).take 8 = wbytes w := List.take_of_length_le (by simp [wbytes])
  have h2 : w >>> (8 * 8) = 0#64 := by
    ext j hj; simp
  rw [h1, h2]
  ext j hj
  simp [hj]

/-! ## Words of the buffer -/

theorem extract_wordLE (bs : List (BitVec 8)) (i j : ℕ) (hj : j < 8) :
    (wordLE bs i).extractLsb' (8 * j) 8 = bs.getD (i + j) 0#8 := by
  unfold wordLE
  interval_cases j <;>
  · try simp only [Nat.add_zero, Nat.mul_zero]
    generalize bs.getD (i + 7) 0#8 = b7
    generalize bs.getD (i + 6) 0#8 = b6
    generalize bs.getD (i + 5) 0#8 = b5
    generalize bs.getD (i + 4) 0#8 = b4
    generalize bs.getD (i + 3) 0#8 = b3
    generalize bs.getD (i + 2) 0#8 = b2
    generalize bs.getD (i + 1) 0#8 = b1
    generalize bs.getD i 0#8 = b0
    ext k hk
    simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hk,
      decide_true, Bool.true_and]
    split_ifs <;> first | omega | (congr 1; omega)

theorem wbytes_wordLE (bs : List (BitVec 8)) (i : ℕ) (h : i + 8 ≤ bs.length) :
    wbytes (wordLE bs i) = (bs.drop i).take 8 := by
  apply List.ext_getElem
  · simp [wbytes]; omega
  · intro j h1 h2
    have hj : j < 8 := by simpa [wbytes] using h1
    simp only [wbytes, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    rw [extract_wordLE bs i j hj, List.getD_eq_getElem]

theorem take_drop_chunks {α : Type*} (l : List α) (p L N : ℕ) (g : ℕ → List α)
    (hg : ∀ n < N, g n = (l.drop (p + L * n)).take L) :
    (l.drop p).take (L * N) = (List.range N).flatMap g := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, ← ih (fun n hn => hg n (by omega)), Nat.mul_succ,
      List.take_add]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hg N (by omega), List.drop_drop]

/-! ## The braided step -/

theorem regPoly64_bytes (x : BitVec 64) :
    regPoly x = ∑ k ∈ Finset.range 8, X ^ (8 * (7 - k)) * regPoly (x.extractLsb' (8 * k) 8) := by
  ext n
  rw [finsetSum_coeff]
  simp only [coeff_X_pow_mul', coeff_regPoly, BitVec.getLsbD_extractLsb']
  by_cases hn : n < 64
  · rw [Finset.sum_eq_single (7 - n / 8)]
    · have e1 : 8 * (7 - (7 - n / 8)) ≤ n := by omega
      have e2 : n - 8 * (7 - (7 - n / 8)) < 8 := by omega
      have e3 : 8 - 1 - (n - 8 * (7 - (7 - n / 8))) < 8 := by omega
      have e4 : 8 * (7 - n / 8) + (8 - 1 - (n - 8 * (7 - (7 - n / 8)))) = 64 - 1 - n := by omega
      simp [hn, e1, e2, e3, e4]
    · intro k hk hne
      simp only [Finset.mem_range] at hk
      split_ifs with h1 h2
      · exfalso; obtain ⟨h2, -⟩ := h2; omega
      · rfl
      · rfl
    · intro h; simp at h; omega
  · rw [if_neg (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_range] at hk
    split_ifs with h1 h2
    · exfalso; obtain ⟨h2, -⟩ := h2; omega
    · rfl
    · rfl

theorem regPoly_setWidth64 (v : BitVec 32) : regPoly (v.setWidth 64) = X ^ 32 * regPoly v := by
  ext n
  simp only [coeff_X_pow_mul', coeff_regPoly, BitVec.getLsbD_setWidth]
  by_cases h1 : n < 32
  · simp [show ¬ 32 ≤ n by omega, BitVec.getLsbD_of_ge v (64 - 1 - n) (by omega)]
  by_cases h2 : n < 64
  · have e : 64 - 1 - n = 32 - 1 - (n - 32) := by omega
    simp [h2, e, show 32 ≤ n by omega, show n - 32 < 32 by omega,
      show 32 - 1 - (n - 32) < 64 by omega]
  · simp [h2, show 32 ≤ n by omega, show ¬ n - 32 < 32 by omega]

theorem poly_ofBytes_cons (b : BitVec 8) (bs : List (BitVec 8)) :
    (Message.ofBytes (b :: bs)).poly = regPoly b * X ^ (8 * bs.length) + (Message.ofBytes bs).poly := by
  rw [ofBytes_cons, poly_append, poly_ofBytes_single, length_ofBytes]

theorem poly_ofBytes_wbytes (w : BitVec 64) : (Message.ofBytes (wbytes w)).poly = regPoly w := by
  have h : wbytes w = [w.extractLsb' (8 * 0) 8, w.extractLsb' (8 * 1) 8, w.extractLsb' (8 * 2) 8,
      w.extractLsb' (8 * 3) 8, w.extractLsb' (8 * 4) 8, w.extractLsb' (8 * 5) 8,
      w.extractLsb' (8 * 6) 8, w.extractLsb' (8 * 7) 8] := rfl
  have h0 : (Message.ofBytes []).poly = 0 := poly_nil
  rw [h, regPoly64_bytes]
  simp only [poly_ofBytes_cons, h0, List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero]
  ring

theorem regPoly_TB (k : ℕ) (hk : k < 8) (x : BitVec 64) (s : ℕ) :
    regPoly (TB k ((x >>> s).toNat % 256)) =
      regPoly (x.extractLsb' s 8) * X ^ (8 * (5 * 8 + 3 - k)) % crc32P := by
  have hi : (x >>> s).toNat % 256 = (x.extractLsb' s 8).toNat := by
    have : x.extractLsb' s 8 = (x >>> s).setWidth 8 := by
      ext j hj; simp [hj]
    rw [this, BitVec.toNat_setWidth]
  unfold TB
  rw [hi, (crc_tables_eq.2.1.2 k hk _ (x.extractLsb' s 8).isLt), BitVec.ofNat_toNat,
    BitVec.setWidth_eq, poly_ofBytes_single]

theorem regPoly_braidWord_x (x : BitVec 64) : regPoly (braidWord x) = regPoly x * X ^ 288 % crc32P := by
  have h0 : x.toNat % 256 = (x >>> 0).toNat % 256 := by simp
  unfold braidWord
  rw [h0]
  simp only [regPoly_xor]
  rw [regPoly_TB 0 (by norm_num) x 0, regPoly_TB 1 (by norm_num) x 8,
    regPoly_TB 2 (by norm_num) x 16, regPoly_TB 3 (by norm_num) x 24,
    regPoly_TB 4 (by norm_num) x 32, regPoly_TB 5 (by norm_num) x 40,
    regPoly_TB 6 (by norm_num) x 48, regPoly_TB 7 (by norm_num) x 56]
  rw [regPoly64_bytes x]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← add_mod']
  exact congrArg (· % crc32P) (by ring)

theorem regPoly_braidWord (v : BitVec 32) (w : BitVec 64) :
    regPoly (braidWord (v.setWidth 64 ^^^ w)) =
      crcWordN crc32P 64 5 (Message.ofBytes (wbytes w)).poly (regPoly v) := by
  rw [regPoly_braidWord_x, regPoly_xor, regPoly_setWidth64, poly_ofBytes_wbytes]
  unfold crcWordN
  rw [crc32P_natDegree]
  exact congrArg (· % crc32P) (by ring)

/-! ## The braided path -/

/-- The `n`-th word of block `k` as a message. -/
def mB (bs : List (BitVec 8)) (q : ℕ) (k n : ℕ) : Message :=
  Message.ofBytes (wbytes (wordLE bs (q + 40 * k + 8 * n)))

theorem mB_length (bs : List (BitVec 8)) (q k n : ℕ) : (mB bs q k n).length = 64 := by
  simp [mB, length_ofBytes, wbytes]

theorem regPoly_braids (bs : List (BitVec 8)) (q : ℕ) (c : BitVec 32) (k n : ℕ) :
    regPoly (braids bs q c k n) = stripeCrc crc32P 64 5 (mB bs q) (regPoly c) k n := by
  induction k generalizing n with
  | zero =>
    simp only [braids, stripeCrc]
    split_ifs
    · rfl
    · exact regPoly_zero
  | succ k ih =>
    simp only [braids, stripeCrc]
    rw [regPoly_braidWord, ih]
    rfl

theorem regPoly_crcWord_xor (v b : BitVec 32) (w : BitVec 64) :
    regPoly (crcWord (v ^^^ b) w) =
      crc0 crc32P (Message.ofBytes (wbytes w)) (regPoly v + regPoly b) := by
  rw [crcWord_eq, regPoly_crcBytes, regPoly_xor]

theorem regPoly_foldLast (bs : List (BitVec 8)) (q : ℕ) (c : BitVec 32) (K : ℕ) :
    regPoly (foldLast bs q c K) = crc0 crc32P
      ((List.range (K + 1)).flatMap fun k => (List.range 5).flatMap fun n => mB bs q k n)
      (regPoly c) := by
  have gen : ∀ (l : List ℕ) (a : BitVec 32),
      regPoly (l.foldl (fun v n => crcWord (v ^^^ braids bs q c K n)
        (wordLE bs (q + 40 * K + 8 * n))) a) =
      l.foldl (fun v' n => crc0 crc32P (mB bs q K n)
        (v' + stripeCrc crc32P 64 5 (mB bs q) (regPoly c) K n)) (regPoly a) := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons n l ih =>
      intro a
      simp only [List.foldl_cons]
      rw [ih, regPoly_crcWord_xor, regPoly_braids]
      rfl
  unfold foldLast
  rw [gen, show (0 : BitVec 32) = 0#32 from rfl, regPoly_zero,
    crc0_interleaved_fold crc32P crc32P_natDegree_pos 64 5 K (by norm_num) (mB bs q)
      (mB_length bs q) (regPoly c),
    (crc0_interleaved crc32P crc32P_natDegree_pos 64 5 K (by norm_num) (mB bs q)
      (mB_length bs q) (regPoly c)).2]

theorem ofBytes_flatMap {β : Type*} (l : List β) (f : β → List (BitVec 8)) :
    Message.ofBytes (l.flatMap f) = l.flatMap fun a => Message.ofBytes (f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.flatMap_cons, ofBytes_append, ih]

theorem flat_eq (bs : List (BitVec 8)) (q K : ℕ) (h : q + 40 * (K + 1) ≤ bs.length) :
    ((List.range (K + 1)).flatMap fun k => (List.range 5).flatMap fun n => mB bs q k n) =
      Message.ofBytes ((bs.drop q).take (40 * (K + 1))) := by
  rw [take_drop_chunks bs q 40 (K + 1)
    (fun k => (List.range 5).flatMap fun n => wbytes (wordLE bs (q + 40 * k + 8 * n)))]
  · rw [ofBytes_flatMap]
    refine List.flatMap_congr fun k _ => ?_
    rw [ofBytes_flatMap]
    rfl
  · intro k hk
    rw [show (40 : ℕ) = 8 * 5 from rfl] at h ⊢
    rw [take_drop_chunks bs (q + 8 * 5 * k) 8 5]
    intro n hn
    rw [wbytes_wordLE bs _ (by nlinarith)]

theorem braided_holds (crc : BitVec 32) (bs : List (BitVec 8)) (q K : ℕ)
    (h : q + 40 * (K + 1) ≤ bs.length) :
    Holds32 ((braidedResult crc bs q K).setWidth 64) (crc32Poly crc bs) := by
  rw [holds32_iff]
  unfold braidedResult
  rw [regPoly_not, regPoly_crcBytes, regPoly_foldLast, flat_eq bs q K h, regPoly_crcBytes,
    ← crc0_append, ← crc0_append, ← ofBytes_append, ← ofBytes_append, crc32Poly_eq,
    ← List.drop_drop, List.take_append_drop, List.take_append_drop]

end ZlibCrc32.Crcz.PartM

namespace ZlibCrc32.Crcz
end ZlibCrc32.Crcz
end


open ZlibCrc32 ZlibCrc32.Crcz in
theorem solution (crc : BitVec 32) (bs : List (BitVec 8)) (q K : ℕ)
    (h : q + 40 * (K + 1) ≤ bs.length) :
    Holds32 ((braidedResult crc bs q K).setWidth 64) (crc32Poly crc bs) :=

  ZlibCrc32.Crcz.PartM.braided_holds crc bs q K h
