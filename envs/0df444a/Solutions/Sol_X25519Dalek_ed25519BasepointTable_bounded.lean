-- Prove2me | solution 1 for X25519Dalek.ed25519BasepointTable_bounded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T10:34:55.319067+00:00
-- url     : https://prove2.me/submissions/d6734572-7179-4011-9732-96bf647fe91a

import Mathlib
import Definitions.Def_X25519Dalek_Spec

section
/-! # The limbs of the basepoint table are below `2 ^ 52`

After google-deepmind/code-verification @ 8c8d371f, `Shared51/InternalSpecs.lean`
(`ed25519BasepointTableBytes_bounded`, Apache-2.0), with a simpler word checker. -/

namespace X25519Dalek.Edw

open X25519Dalek

theorem readLE_congr_off (bs bs' : List (BitVec 8)) (off1 off2 n : Nat)
    (h : ∀ i, i < n → bs.getD (off1 + i) 0#8 = bs'.getD (off2 + i) 0#8) :
    ByteSlice.readLE bs off1 n = ByteSlice.readLE bs' off2 n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [ByteSlice.readLE, ih (fun i hi => h i (by omega)), h k (by omega)]

theorem getD_slice (buf : List (BitVec 8)) (off n i : Nat) (d : BitVec 8) (h : i < n) :
    (ByteSlice.slice buf off n).getD i d = buf.getD (off + i) d := by
  unfold ByteSlice.slice
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt h, List.getElem?_drop]

theorem readLE_slice_eq (bs : List (BitVec 8)) (off m k : Nat) (hk : k + 8 ≤ m) :
    ByteSlice.readLE (ByteSlice.slice bs off m) k 8 = ByteSlice.readLE bs (off + k) 8 := by
  apply readLE_congr_off
  intro i hi
  rw [getD_slice bs off m (k + i) 0#8 (by omega), Nat.add_assoc]

/-- Every one of the first `rem` little-endian 64-bit words of `bs` is `< bound`. -/
def checkWordsBounded (bs : List (BitVec 8)) (bound : Nat) : Nat → Bool
  | 0 => true
  | rem + 1 =>
    decide ((ByteSlice.readLE bs 0 8).toNat < bound) && checkWordsBounded (bs.drop 8) bound rem

theorem of_checkWordsBounded {bs : List (BitVec 8)} {bound rem k : Nat}
    (h : checkWordsBounded bs bound rem = true) (hk : k < rem) :
    (ByteSlice.readLE bs (8 * k) 8).toNat < bound := by
  induction rem generalizing bs k with
  | zero => omega
  | succ rem ih =>
    simp only [checkWordsBounded, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases k with _ | k
    · simpa using h.1
    · have e : ByteSlice.readLE bs (8 * (k + 1)) 8 = ByteSlice.readLE (bs.drop 8) (8 * k) 8 := by
        apply readLE_congr_off
        intro i _
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
        congr 2; omega
      rw [e]; exact ih h.2 (by omega)

theorem checkWordsBounded_table_0 :
    checkWordsBounded (ed25519BasepointTableBytes.drop 0) (2 ^ 52) 240 = true := by decide +kernel

theorem checkWordsBounded_table_1 :
    checkWordsBounded (ed25519BasepointTableBytes.drop 1920) (2 ^ 52) 240 = true := by decide +kernel

theorem checkWordsBounded_table_2 :
    checkWordsBounded (ed25519BasepointTableBytes.drop 3840) (2 ^ 52) 240 = true := by decide +kernel

theorem checkWordsBounded_table_3 :
    checkWordsBounded (ed25519BasepointTableBytes.drop 5760) (2 ^ 52) 240 = true := by decide +kernel

theorem checkWordsBounded_table_4 :
    checkWordsBounded (ed25519BasepointTableBytes.drop 7680) (2 ^ 52) 240 = true := by decide +kernel

theorem checkWordsBounded_table_5 :
    checkWordsBounded (ed25519BasepointTableBytes.drop 9600) (2 ^ 52) 240 = true := by decide +kernel

theorem checkWordsBounded_table_6 :
    checkWordsBounded (ed25519BasepointTableBytes.drop 11520) (2 ^ 52) 240 = true := by decide +kernel

theorem checkWordsBounded_table_7 :
    checkWordsBounded (ed25519BasepointTableBytes.drop 13440) (2 ^ 52) 240 = true := by decide +kernel

theorem checkWordsBounded_table_8 :
    checkWordsBounded (ed25519BasepointTableBytes.drop 15360) (2 ^ 52) 240 = true := by decide +kernel

theorem checkWordsBounded_table_9 :
    checkWordsBounded (ed25519BasepointTableBytes.drop 17280) (2 ^ 52) 240 = true := by decide +kernel

theorem checkWordsBounded_table_10 :
    checkWordsBounded (ed25519BasepointTableBytes.drop 19200) (2 ^ 52) 240 = true := by decide +kernel

theorem checkWordsBounded_table_11 :
    checkWordsBounded (ed25519BasepointTableBytes.drop 21120) (2 ^ 52) 240 = true := by decide +kernel

theorem checkWordsBounded_table_12 :
    checkWordsBounded (ed25519BasepointTableBytes.drop 23040) (2 ^ 52) 240 = true := by decide +kernel

theorem checkWordsBounded_table_13 :
    checkWordsBounded (ed25519BasepointTableBytes.drop 24960) (2 ^ 52) 240 = true := by decide +kernel

theorem checkWordsBounded_table_14 :
    checkWordsBounded (ed25519BasepointTableBytes.drop 26880) (2 ^ 52) 240 = true := by decide +kernel

theorem checkWordsBounded_table_15 :
    checkWordsBounded (ed25519BasepointTableBytes.drop 28800) (2 ^ 52) 240 = true := by decide +kernel

theorem checkWordsBounded_append {bs : List (BitVec 8)} {bound a b : Nat}
    (h1 : checkWordsBounded bs bound a = true) (h2 : checkWordsBounded (bs.drop (8 * a)) bound b = true) :
    checkWordsBounded bs bound (a + b) = true := by
  induction a generalizing bs with
  | zero => simpa using h2
  | succ a ih =>
    simp only [checkWordsBounded, Bool.and_eq_true] at h1
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [checkWordsBounded, Bool.and_eq_true]
    refine ⟨h1.1, ih h1.2 ?_⟩
    rw [List.drop_drop, show 8 + 8 * a = 8 * (a + 1) by omega]; exact h2

theorem checkWordsBounded_table :
    checkWordsBounded ed25519BasepointTableBytes (2 ^ 52) 3840 = true := by
  have h1 := checkWordsBounded_append checkWordsBounded_table_0 (b := 240)
    (by simpa using checkWordsBounded_table_1)
  have h2 := checkWordsBounded_append h1 (b := 240) (by simpa using checkWordsBounded_table_2)
  have h3 := checkWordsBounded_append h2 (b := 240) (by simpa using checkWordsBounded_table_3)
  have h4 := checkWordsBounded_append h3 (b := 240) (by simpa using checkWordsBounded_table_4)
  have h5 := checkWordsBounded_append h4 (b := 240) (by simpa using checkWordsBounded_table_5)
  have h6 := checkWordsBounded_append h5 (b := 240) (by simpa using checkWordsBounded_table_6)
  have h7 := checkWordsBounded_append h6 (b := 240) (by simpa using checkWordsBounded_table_7)
  have h8 := checkWordsBounded_append h7 (b := 240) (by simpa using checkWordsBounded_table_8)
  have h9 := checkWordsBounded_append h8 (b := 240) (by simpa using checkWordsBounded_table_9)
  have h10 := checkWordsBounded_append h9 (b := 240) (by simpa using checkWordsBounded_table_10)
  have h11 := checkWordsBounded_append h10 (b := 240) (by simpa using checkWordsBounded_table_11)
  have h12 := checkWordsBounded_append h11 (b := 240) (by simpa using checkWordsBounded_table_12)
  have h13 := checkWordsBounded_append h12 (b := 240) (by simpa using checkWordsBounded_table_13)
  have h14 := checkWordsBounded_append h13 (b := 240) (by simpa using checkWordsBounded_table_14)
  have h15 := checkWordsBounded_append h14 (b := 240) (by simpa using checkWordsBounded_table_15)
  simpa using h15

theorem table_length : ed25519BasepointTableBytes.length = 30720 := by decide +kernel

/-- All 3,840 limbs of the read-only basepoint table are `< 2 ^ 52`. -/
theorem table_bounded52 : fe51BasepointTable32Bounded ed25519BasepointTableBytes (2 ^ 52) := by
  refine ⟨table_length, fun i hi => ?_⟩
  have hlen : (ByteSlice.slice ed25519BasepointTableBytes (960 * i) 960).length = 960 := by
    simp only [ByteSlice.slice, List.length_take, List.length_drop, table_length]; omega
  have hlimb (j : Nat) (hj : j < 120) :
      (ByteSlice.readLE (ByteSlice.slice ed25519BasepointTableBytes (960 * i) 960) (8 * j) 8).toNat
        < 2 ^ 52 := by
    rw [readLE_slice_eq _ _ _ _ (by omega), show 960 * i + 8 * j = 8 * (120 * i + j) by omega]
    exact of_checkWordsBounded checkWordsBounded_table (by omega)
  have hentry (e : Nat) (he : e < 8) :
      fe51AffineNielsBoundedAt (ByteSlice.slice ed25519BasepointTableBytes (960 * i) 960)
        (120 * e) (2 ^ 52) := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    all_goals first
      | (have := hlimb (15 * e) (by omega); rwa [show 8 * (15 * e) = 120 * e by omega] at this)
      | (have := hlimb (15 * e + 1) (by omega); rwa [show 8 * (15 * e + 1) = 120 * e + 8 by omega] at this)
      | (have := hlimb (15 * e + 2) (by omega); rwa [show 8 * (15 * e + 2) = 120 * e + 16 by omega] at this)
      | (have := hlimb (15 * e + 3) (by omega); rwa [show 8 * (15 * e + 3) = 120 * e + 24 by omega] at this)
      | (have := hlimb (15 * e + 4) (by omega); rwa [show 8 * (15 * e + 4) = 120 * e + 32 by omega] at this)
      | (have := hlimb (15 * e + 5) (by omega); rwa [show 8 * (15 * e + 5) = 120 * e + 40 by omega] at this)
      | (have := hlimb (15 * e + 6) (by omega); rwa [show 8 * (15 * e + 6) = 120 * e + 40 + 8 by omega] at this)
      | (have := hlimb (15 * e + 7) (by omega); rwa [show 8 * (15 * e + 7) = 120 * e + 40 + 16 by omega] at this)
      | (have := hlimb (15 * e + 8) (by omega); rwa [show 8 * (15 * e + 8) = 120 * e + 40 + 24 by omega] at this)
      | (have := hlimb (15 * e + 9) (by omega); rwa [show 8 * (15 * e + 9) = 120 * e + 40 + 32 by omega] at this)
      | (have := hlimb (15 * e + 10) (by omega); rwa [show 8 * (15 * e + 10) = 120 * e + 80 by omega] at this)
      | (have := hlimb (15 * e + 11) (by omega); rwa [show 8 * (15 * e + 11) = 120 * e + 80 + 8 by omega] at this)
      | (have := hlimb (15 * e + 12) (by omega); rwa [show 8 * (15 * e + 12) = 120 * e + 80 + 16 by omega] at this)
      | (have := hlimb (15 * e + 13) (by omega); rwa [show 8 * (15 * e + 13) = 120 * e + 80 + 24 by omega] at this)
      | (have := hlimb (15 * e + 14) (by omega); rwa [show 8 * (15 * e + 14) = 120 * e + 80 + 32 by omega] at this)
  exact ⟨hlen, hentry 0 (by omega), hentry 1 (by omega), hentry 2 (by omega), hentry 3 (by omega),
    hentry 4 (by omega), hentry 5 (by omega), hentry 6 (by omega), hentry 7 (by omega)⟩

end X25519Dalek.Edw
end

open X25519Dalek in
theorem solution : fe51BasepointTable32Bounded ed25519BasepointTableBytes (2 ^ 52) :=
  X25519Dalek.Edw.table_bounded52
