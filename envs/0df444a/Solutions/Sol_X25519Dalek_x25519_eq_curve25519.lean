-- Prove2me | solution 1 for X25519Dalek.x25519_eq_curve25519
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T09:11:53.562836+00:00
-- url     : https://prove2.me/submissions/51fdc6c7-6809-4552-8453-2509c287d6a8

import Mathlib
import Definitions.Def_Curve25519Bernstein
import Definitions.Def_X25519Dalek_Rfc7748
import Theorems.Thm_Bernstein_ladder_eq_curve25519

namespace X25519DalekBridge

open X25519Dalek

/-- The field `F_p` of Bernstein's bundle. -/
abbrev F := ZMod Bernstein.p25519

theorem p_eq : X25519Dalek.p25519 = Bernstein.p25519 := rfl

theorem p_pos : 0 < Bernstein.p25519 := by unfold Bernstein.p25519; norm_num

theorem cast_mod (a : ℕ) : (((a % X25519Dalek.p25519 : ℕ)) : F) = (a : F) := by
  rw [p_eq]; exact ZMod.natCast_mod a _

theorem cast_fpAdd (a b : ℕ) : ((fpAdd a b : ℕ) : F) = (a : F) + (b : F) := by
  unfold fpAdd; rw [cast_mod]; push_cast; rfl

theorem cast_fpSub (a b : ℕ) : ((fpSub a b : ℕ) : F) = (a : F) - (b : F) := by
  unfold fpSub
  rw [cast_mod, p_eq]
  have h : b % Bernstein.p25519 ≤ a + Bernstein.p25519 :=
    le_trans (Nat.mod_lt _ p_pos).le (Nat.le_add_left _ _)
  rw [Nat.cast_sub h, Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_self]
  ring

theorem cast_fpMul (a b : ℕ) : ((fpMul a b : ℕ) : F) = (a : F) * (b : F) := by
  unfold fpMul; rw [cast_mod, Nat.cast_mul, cast_mod, cast_mod]

theorem cast_fpSq (a : ℕ) : ((fpSq a : ℕ) : F) = (a : F) ^ 2 := by
  unfold fpSq; rw [cast_fpMul]; ring

theorem cast_modPowLoop : ∀ (fuel base exp acc : ℕ), exp < 2 ^ fuel →
    ((modPowLoop fuel base exp X25519Dalek.p25519 acc : ℕ) : F) = (acc : F) * (base : F) ^ exp
  | 0, base, exp, acc, h => by
    have : exp = 0 := by simpa using h
    subst this; rw [modPowLoop, cast_mod]; simp
  | fuel + 1, base, exp, acc, h => by
    rw [modPowLoop]
    by_cases h0 : exp = 0
    · subst h0; simp [cast_mod]
    · have h0' : (exp == 0) = false := by simpa using h0
      simp only [h0', Bool.false_eq_true, if_false]
      have hlt : exp / 2 < 2 ^ fuel := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at h; exact h
      rw [cast_modPowLoop fuel _ _ _ hlt, cast_mod, Nat.cast_mul]
      have hd := Nat.div_add_mod exp 2
      rcases Nat.mod_two_eq_zero_or_one exp with he | he
      · have : (exp % 2 == 1) = false := by simp [he]
        simp only [this, Bool.false_eq_true, if_false]
        conv_rhs => rw [← hd, he]
        ring
      · have : (exp % 2 == 1) = true := by simp [he]
        simp only [this, if_true]
        rw [cast_mod, Nat.cast_mul]
        conv_rhs => rw [← hd, he]
        ring

theorem cast_fpInv (a : ℕ) : ((fpInv a : ℕ) : F) = (a : F) ^ (Bernstein.p25519 - 2) := by
  unfold fpInv fpPow modPow
  rw [cast_modPowLoop _ _ _ _ (by unfold X25519Dalek.p25519; norm_num), cast_mod]
  simp [p_eq]

/-- The state `(x₂, z₂, x₃, z₃)` of the two projective pairs, in `F_p`. -/
def toSt (x0 x1 : MontProjPoint) : F × F × F × F :=
  ((x0.U : F), (x0.W : F), (x1.U : F), (x1.W : F))

theorem step0 (u1 : ℕ) (x0 x1 : MontProjPoint) :
    toSt (montDiffAddAndDouble u1 x0 x1).1 (montDiffAddAndDouble u1 x0 x1).2 =
      Bernstein.ladderStep (121665 : F) (u1 : F) false (toSt x0 x1) := by
  simp only [montDiffAddAndDouble, Bernstein.ladderStep, toSt, cast_fpAdd, cast_fpSub,
    cast_fpMul, cast_fpSq, Bool.false_eq_true, if_false]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> (simp <;> ring_nf)

theorem step1 (u1 : ℕ) (x0 x1 : MontProjPoint) :
    toSt (montDiffAddAndDouble u1 x1 x0).2 (montDiffAddAndDouble u1 x1 x0).1 =
      Bernstein.ladderStep (121665 : F) (u1 : F) true (toSt x0 x1) := by
  simp only [montDiffAddAndDouble, Bernstein.ladderStep, toSt, cast_fpAdd, cast_fpSub,
    cast_fpMul, cast_fpSq, if_true]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> (simp <;> ring_nf)

theorem loop_eq (k u1 : ℕ) : ∀ (fuel : ℕ) (x0 x1 : MontProjPoint),
    (((montLadderLoop fuel k u1 x0 x1).U : F), ((montLadderLoop fuel k u1 x0 x1).W : F)) =
      ((Bernstein.ladderIter (121665 : F) (u1 : F) k fuel (toSt x0 x1)).1,
       (Bernstein.ladderIter (121665 : F) (u1 : F) k fuel (toSt x0 x1)).2.1)
  | 0, x0, x1 => by simp [montLadderLoop, Bernstein.ladderIter, toSt]
  | fuel + 1, x0, x1 => by
    rw [montLadderLoop, Bernstein.ladderIter, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ fuel) with hb | hb
    · simp only [hb, show decide ((0 : ℕ) = 1) = false from rfl,
        show ((0 : ℕ) == 1) = false from rfl, Bool.false_eq_true, if_false]
      rw [← step0, loop_eq k u1 fuel]
    · simp only [hb, decide_true,
        show ((1 : ℕ) == 1) = true from rfl, if_true]
      rw [← step1, loop_eq k u1 fuel]

theorem x25519Ladder_eq (k u : ℕ) :
    x25519Ladder k u = (Bernstein.ladder k (u : F)).val := by
  have hc : ((x25519Ladder k u : ℕ) : F) = Bernstein.ladder k (u : F) := by
    unfold x25519Ladder Bernstein.ladder
    have hl := loop_eq k (u % X25519Dalek.p25519) 255 ⟨1, 0⟩ ⟨u % X25519Dalek.p25519, 1⟩
    simp only [Prod.mk.injEq] at hl
    simp only [cast_fpMul, cast_fpInv, hl.1, hl.2]
    have : toSt ⟨1, 0⟩ ⟨u % X25519Dalek.p25519, 1⟩ = ((1 : F), (0 : F), (u : F), (1 : F)) := by
      simp [toSt, cast_mod]
    rw [this, cast_mod]
  rw [← hc, ZMod.val_natCast, Nat.mod_eq_of_lt]
  unfold x25519Ladder fpMul
  rw [← p_eq]
  exact Nat.mod_lt _ (by unfold X25519Dalek.p25519; norm_num)

/-! ## Bytes -/

theorem foldr_acc (l : List (BitVec 8)) (acc : ℕ) :
    l.foldr (fun b acc => acc * 256 + b.toNat) acc = acc * 256 ^ l.length + leBytesToNat l := by
  induction l with
  | nil => simp [leBytesToNat]
  | cons b l ih =>
    unfold leBytesToNat at *
    simp only [List.foldr_cons, List.length_cons]
    rw [ih]
    ring

theorem leBytes_lt : ∀ l : List (BitVec 8), leBytesToNat l < 256 ^ l.length
  | [] => by simp [leBytesToNat]
  | b :: l => by
    have ih := leBytes_lt l
    have hb : b.toNat < 256 := b.isLt
    have : leBytesToNat (b :: l) = leBytesToNat l * 256 + b.toNat := rfl
    rw [this, List.length_cons, pow_succ]
    nlinarith

theorem foldr_range (n : ℕ) : ∀ (len acc : ℕ),
    ((List.range len).map (fun i => BitVec.ofNat 8 ((n / (256 ^ i)) % 256))).foldr
      (fun b acc => acc * 256 + b.toNat) acc = acc * 256 ^ len + n % 256 ^ len
  | 0, acc => by simp [Nat.mod_one]
  | len + 1, acc => by
    rw [List.range_succ, List.map_append, List.foldr_append]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [foldr_range n len, BitVec.toNat_ofNat, show (2 : ℕ) ^ 8 = 256 from rfl, Nat.mod_mod,
      Nat.mod_pow_succ (b := 256)]
    ring

theorem leBytes_natToLeBytes (len n : ℕ) : leBytesToNat (natToLeBytes len n) = n % 256 ^ len := by
  unfold leBytesToNat natToLeBytes
  rw [foldr_range]; simp

theorem clamp_mem (s : List (BitVec 8)) (hs : s.length = 32) :
    clampScalar s ∈ Bernstein.secretKeys := by
  unfold clampScalar
  rw [List.take_of_length_le (by omega)]
  unfold clampScalarBytes
  have hb0 : ∀ x : BitVec 8, (x &&& 0xf8#8).toNat % 8 = 0 := by decide
  have hb31 : ∀ x : BitVec 8, 64 ≤ ((x &&& 0x7f#8) ||| 0x40#8).toNat ∧
      ((x &&& 0x7f#8) ||| 0x40#8).toNat ≤ 127 := by decide
  generalize hM : (s.drop 1).take 30 = M
  have hMl : M.length = 30 := by rw [← hM]; simp [hs]
  have hMlt := leBytes_lt M
  rw [hMl] at hMlt
  have key : ∀ b0 b31 : BitVec 8, leBytesToNat ([b0] ++ M ++ [b31]) =
      (b31.toNat * 256 ^ M.length + leBytesToNat M) * 256 + b0.toNat := by
    intro b0 b31
    rw [leBytesToNat, List.foldr_append, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil]
    rw [foldr_acc]
    ring
  rw [key, hMl]
  have h0 := hb0 (s.getD 0 0#8)
  have h0' := (s.getD 0 0#8 &&& 0xf8#8).isLt
  have h31 := hb31 (s.getD 31 0#8)
  generalize (s.getD 0 0#8 &&& 0xf8#8).toNat = a at *
  generalize ((s.getD 31 0#8 &&& 0x7f#8) ||| 0x40#8).toNat = c at *
  generalize leBytesToNat M = m at *
  norm_num at *
  refine ⟨((c * 1766847064778384329583297500742918515827483896875618958121606201292619776 + m) * 256 + a - 2 ^ 254) / 8, ?_, ?_⟩
  · norm_num; omega
  · norm_num; omega

theorem x25519Ladder_lt (k u : ℕ) : x25519Ladder k u < Bernstein.p25519 := by
  unfold x25519Ladder fpMul
  rw [← p_eq]
  exact Nat.mod_lt _ (by unfold X25519Dalek.p25519; norm_num)

theorem main [Fact Bernstein.p25519.Prime] (s u : List (BitVec 8))
    (hs : s.length = 32) (_hu : u.length = 32) :
    leBytesToNat (x25519 s u) = Bernstein.curve25519 (clampScalar s) (decodeU255 u) := by
  have hq : decodeU255 u < 2 ^ 256 :=
    lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  rw [(Bernstein.ladder_eq_curve25519 (clampScalar s) (clamp_mem s hs)).2.2.2 _ hq, x25519,
    leBytes_natToLeBytes, Nat.mod_eq_of_lt, x25519Ladder_eq]
  exact lt_trans (x25519Ladder_lt _ _) (by unfold Bernstein.p25519; norm_num)

end X25519DalekBridge

theorem solution [Fact Bernstein.p25519.Prime] (s u : List (BitVec 8))
    (hs : s.length = 32) (hu : u.length = 32) :
    X25519Dalek.leBytesToNat (X25519Dalek.x25519 s u) =
      Bernstein.curve25519 (X25519Dalek.clampScalar s) (X25519Dalek.decodeU255 u) :=
  X25519DalekBridge.main s u hs hu
