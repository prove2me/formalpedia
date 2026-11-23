-- Prove2me | solution 1 for X25519Dalek.fe51_to_bytes_eq_natToLeBytes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T14:24:54.843382+00:00
-- url     : https://prove2.me/submissions/4bd4e8c7-0f1a-42f0-a733-b43514569079

import Definitions.Def_X25519Dalek_PlacedObj
import Definitions.Def_X25519Dalek_Rfc7748
import Definitions.Def_X25519Dalek_Spec
import Mathlib

section
section
set_option autoImplicit false

namespace X25519Dalek.TB

open Arm64

def packCanonical51Bytes (u0 u1 u2 u3 u4 : BitVec 64) : List (BitVec 8) :=
  [BitVec.zeroExtend 8 u0, BitVec.zeroExtend 8 (u0 >>> 8), BitVec.zeroExtend 8 (u0 >>> 16),
   BitVec.zeroExtend 8 (u0 >>> 24), BitVec.zeroExtend 8 (u0 >>> 32), BitVec.zeroExtend 8 (u0 >>> 40),
   BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (u0 >>> 48)) &&& 18446744069414584327#64 |||
     (BitVec.setWidth 64 (BitVec.setWidth 32 u1) &&& 536870911#64) <<< 3),
   BitVec.zeroExtend 8 (u1 >>> 5), BitVec.zeroExtend 8 (u1 >>> 13), BitVec.zeroExtend 8 (u1 >>> 21),
   BitVec.zeroExtend 8 (u1 >>> 29), BitVec.zeroExtend 8 (u1 >>> 37),
   BitVec.truncate 8 (BitVec.setWidth 32 (u1 >>> 45 &&& 63#64) ||| BitVec.setWidth 32 u2 <<< 6),
   BitVec.zeroExtend 8 (u2 >>> 2), BitVec.zeroExtend 8 (u2 >>> 10), BitVec.zeroExtend 8 (u2 >>> 18),
   BitVec.zeroExtend 8 (u2 >>> 26), BitVec.zeroExtend 8 (u2 >>> 34), BitVec.zeroExtend 8 (u2 >>> 42),
   BitVec.truncate 8 (BitVec.setWidth 32 (u2 >>> 50 &&& 1#64) ||| BitVec.setWidth 32 u3 <<< 1),
   BitVec.zeroExtend 8 (u3 >>> 7), BitVec.zeroExtend 8 (u3 >>> 15), BitVec.zeroExtend 8 (u3 >>> 23),
   BitVec.zeroExtend 8 (u3 >>> 31), BitVec.zeroExtend 8 (u3 >>> 39),
   BitVec.truncate 8 (BitVec.setWidth 32 (u3 >>> 47 &&& 15#64) ||| BitVec.setWidth 32 u4 <<< 4),
   BitVec.zeroExtend 8 (u4 >>> 4), BitVec.zeroExtend 8 (u4 >>> 12), BitVec.zeroExtend 8 (u4 >>> 20),
   BitVec.zeroExtend 8 (u4 >>> 28), BitVec.zeroExtend 8 (u4 >>> 36), BitVec.zeroExtend 8 (u4 >>> 44 &&& 127#64)]

theorem bv64_and_mask51_toNat (x : BitVec 64) : (x &&& 2251799813685247#64).toNat = x.toNat % 2 ^ 51 := by
  rw [BitVec.toNat_and]
  have : (2251799813685247#64 : BitVec 64).toNat = 2 ^ 51 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
theorem bv64_ushr51_toNat (x : BitVec 64) : (x >>> 51).toNat = x.toNat / 2 ^ 51 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
theorem bv64_zext32_mul19_toNat (x : BitVec 64) (hx : x.toNat < 8) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 x) * 19#64).toNat = x.toNat * 19 := by
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32), Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)]

theorem fe51_carry1_nat (l0 l1 l2 l3 l4 h0 h1 h2 h3 h4 : Nat)
    (nh0 : h0 = l0 % 2 ^ 51 + (l4 / 2 ^ 51) * 19) (nh1 : h1 = l1 % 2 ^ 51 + l0 / 2 ^ 51)
    (nh2 : h2 = l2 % 2 ^ 51 + l1 / 2 ^ 51) (nh3 : h3 = l3 % 2 ^ 51 + l2 / 2 ^ 51)
    (nh4 : h4 = l4 % 2 ^ 51 + l3 / 2 ^ 51) :
    l0 + l1 * 2 ^ 51 + l2 * 2 ^ 102 + l3 * 2 ^ 153 + l4 * 2 ^ 204 =
      (h0 + h1 * 2 ^ 51 + h2 * 2 ^ 102 + h3 * 2 ^ 153 + h4 * 2 ^ 204) + (l4 / 2 ^ 51) * p25519 := by
  unfold p25519; omega

theorem fe51_carry_chain (a0 a1 a2 a3 a4 u1 u2 u3 u4 : Nat)
    (hu1 : u1 = a1 + a0 / 2 ^ 51) (hu2 : u2 = a2 + u1 / 2 ^ 51)
    (hu3 : u3 = a3 + u2 / 2 ^ 51) (hu4 : u4 = a4 + u3 / 2 ^ 51) :
    (a0 + a1 * 2 ^ 51 + a2 * 2 ^ 102 + a3 * 2 ^ 153 + a4 * 2 ^ 204 =
      (a0 % 2 ^ 51) + (u1 % 2 ^ 51) * 2 ^ 51 + (u2 % 2 ^ 51) * 2 ^ 102 +
      (u3 % 2 ^ 51) * 2 ^ 153 + (u4 % 2 ^ 51) * 2 ^ 204 + (u4 / 2 ^ 51) * 2 ^ 255) ∧
    (a0 % 2 ^ 51) + (u1 % 2 ^ 51) * 2 ^ 51 + (u2 % 2 ^ 51) * 2 ^ 102 +
      (u3 % 2 ^ 51) * 2 ^ 153 + (u4 % 2 ^ 51) * 2 ^ 204 < 2 ^ 255 := by omega

theorem fe51_q_le_one (h0 h1 h2 h3 h4 q0 q1 q2 q3 q : Nat)
    (bh0 : h0 < 2 ^ 51 + 152) (bh1 : h1 < 2 ^ 51 + 8)
    (bh2 : h2 < 2 ^ 51 + 8) (bh3 : h3 < 2 ^ 51 + 8) (bh4 : h4 < 2 ^ 51 + 8)
    (nq0 : q0 = (h0 + 19) / 2 ^ 51) (nq1 : q1 = (h1 + q0) / 2 ^ 51)
    (nq2 : q2 = (h2 + q1) / 2 ^ 51) (nq3 : q3 = (h3 + q2) / 2 ^ 51)
    (nq : q = (h4 + q3) / 2 ^ 51) : q ≤ 1 := by omega

theorem fe51_mod_of_carry_chains (H q Rq qu Ru : Nat)
    (hH : H < 2 ^ 255 + 2 ^ 208) (hq : q ≤ 1) (hRq_lt : Rq < 2 ^ 255) (hRu_lt : Ru < 2 ^ 255)
    (hc1 : H + 19 = Rq + q * 2 ^ 255) (hc2 : H + q * 19 = Ru + qu * 2 ^ 255) :
    H % p25519 = Ru := by
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
  · rw [Nat.mod_eq_of_lt (by unfold p25519; omega)]; omega
  · have h_eq : H = Ru + p25519 := by unfold p25519; omega
    rw [h_eq, Nat.add_mod_right, Nat.mod_eq_of_lt (by unfold p25519 at h_eq ⊢; omega)]

theorem fe51_h_bounds (l0 l1 l2 l3 l4 h0 h1 h2 h3 h4 : Nat)
    (hl0 : l0 < 2 ^ 54) (hl1 : l1 < 2 ^ 54) (hl2 : l2 < 2 ^ 54) (hl3 : l3 < 2 ^ 54) (hl4 : l4 < 2 ^ 54)
    (nh0 : h0 = l0 % 2 ^ 51 + (l4 / 2 ^ 51) * 19) (nh1 : h1 = l1 % 2 ^ 51 + l0 / 2 ^ 51)
    (nh2 : h2 = l2 % 2 ^ 51 + l1 / 2 ^ 51) (nh3 : h3 = l3 % 2 ^ 51 + l2 / 2 ^ 51)
    (nh4 : h4 = l4 % 2 ^ 51 + l3 / 2 ^ 51) :
    h0 < 2 ^ 51 + 152 ∧ h1 < 2 ^ 51 + 8 ∧ h2 < 2 ^ 51 + 8 ∧ h3 < 2 ^ 51 + 8 ∧ h4 < 2 ^ 51 + 8 ∧
    h0 + h1 * 2 ^ 51 + h2 * 2 ^ 102 + h3 * 2 ^ 153 + h4 * 2 ^ 204 < 2 ^ 255 + 2 ^ 208 := by omega

theorem fe51_add19_comm (h0 h1 h2 h3 h4 x : Nat) :
    (h0 + x) + h1 * 2 ^ 51 + h2 * 2 ^ 102 + h3 * 2 ^ 153 + h4 * 2 ^ 204 =
      (h0 + h1 * 2 ^ 51 + h2 * 2 ^ 102 + h3 * 2 ^ 153 + h4 * 2 ^ 204) + x := by omega

theorem fe51_canonicalize_nat
    (l0 l1 l2 l3 l4 h0 h1 h2 h3 h4 q0 q1 q2 q3 q u0 u1 u2 u3 u4 : Nat)
    (hl0 : l0 < 2 ^ 54) (hl1 : l1 < 2 ^ 54) (hl2 : l2 < 2 ^ 54) (hl3 : l3 < 2 ^ 54) (hl4 : l4 < 2 ^ 54)
    (nh0 : h0 = l0 % 2 ^ 51 + (l4 / 2 ^ 51) * 19) (nh1 : h1 = l1 % 2 ^ 51 + l0 / 2 ^ 51)
    (nh2 : h2 = l2 % 2 ^ 51 + l1 / 2 ^ 51) (nh3 : h3 = l3 % 2 ^ 51 + l2 / 2 ^ 51)
    (nh4 : h4 = l4 % 2 ^ 51 + l3 / 2 ^ 51)
    (nq0 : q0 = (h0 + 19) / 2 ^ 51) (nq1 : q1 = (h1 + q0) / 2 ^ 51)
    (nq2 : q2 = (h2 + q1) / 2 ^ 51) (nq3 : q3 = (h3 + q2) / 2 ^ 51) (nq : q = (h4 + q3) / 2 ^ 51)
    (nu0 : u0 = h0 + q * 19) (nu1 : u1 = h1 + u0 / 2 ^ 51) (nu2 : u2 = h2 + u1 / 2 ^ 51)
    (nu3 : u3 = h3 + u2 / 2 ^ 51) (nu4 : u4 = h4 + u3 / 2 ^ 51) :
    (l0 + l1 * 2 ^ 51 + l2 * 2 ^ 102 + l3 * 2 ^ 153 + l4 * 2 ^ 204) % p25519 =
      (u0 % 2 ^ 51) + (u1 % 2 ^ 51) * 2 ^ 51 + (u2 % 2 ^ 51) * 2 ^ 102 +
      (u3 % 2 ^ 51) * 2 ^ 153 + (u4 % 2 ^ 51) * 2 ^ 204 := by
  rw [fe51_carry1_nat l0 l1 l2 l3 l4 h0 h1 h2 h3 h4 nh0 nh1 nh2 nh3 nh4, Nat.add_mul_mod_self_right]
  obtain ⟨bh0, bh1, bh2, bh3, bh4, bhH⟩ :=
    fe51_h_bounds l0 l1 l2 l3 l4 h0 h1 h2 h3 h4 hl0 hl1 hl2 hl3 hl4 nh0 nh1 nh2 nh3 nh4
  have hq_le := fe51_q_le_one h0 h1 h2 h3 h4 q0 q1 q2 q3 q bh0 bh1 bh2 bh3 bh4 nq0 nq1 nq2 nq3 nq
  obtain ⟨hc_q, hlt_q⟩ := fe51_carry_chain (h0 + 19) h1 h2 h3 h4 (h1 + q0) (h2 + q1) (h3 + q2) (h4 + q3)
    (congrArg (h1 + ·) nq0) (congrArg (h2 + ·) nq1) (congrArg (h3 + ·) nq2) (congrArg (h4 + ·) nq3)
  rw [← nq, fe51_add19_comm] at hc_q
  obtain ⟨hc_u, hlt_u⟩ := fe51_carry_chain u0 h1 h2 h3 h4 u1 u2 u3 u4 nu1 nu2 nu3 nu4
  have hc_u' : (h0 + h1 * 2 ^ 51 + h2 * 2 ^ 102 + h3 * 2 ^ 153 + h4 * 2 ^ 204) + q * 19 =
      ((u0 % 2 ^ 51) + (u1 % 2 ^ 51) * 2 ^ 51 + (u2 % 2 ^ 51) * 2 ^ 102 +
        (u3 % 2 ^ 51) * 2 ^ 153 + (u4 % 2 ^ 51) * 2 ^ 204) + (u4 / 2 ^ 51) * 2 ^ 255 := by
    rw [← fe51_add19_comm, ← nu0, hc_u]
  exact fe51_mod_of_carry_chains _ q _ (u4 / 2 ^ 51) _ bhH hq_le hlt_q hlt_u hc_q hc_u'
theorem bv64_mask51_add_ushr51_toNat (a b : BitVec 64) :
    ((a &&& 2251799813685247#64) + b >>> 51).toNat = a.toNat % 2 ^ 51 + b.toNat / 2 ^ 51 := by
  rw [BitVec.toNat_add, bv64_and_mask51_toNat, bv64_ushr51_toNat]
  have := b.isLt; omega
theorem bv64_mask51_add_mul19_toNat (a b : BitVec 64) (hb : b.toNat < 2 ^ 54) :
    ((a &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (b >>> 51)) * 19#64).toNat =
      a.toNat % 2 ^ 51 + (b.toNat / 2 ^ 51) * 19 := by
  rw [BitVec.toNat_add, bv64_and_mask51_toNat, bv64_zext32_mul19_toNat, bv64_ushr51_toNat]; · omega
  · rw [bv64_ushr51_toNat]; omega
theorem bv64_add19_ushr51_toNat (a : BitVec 64) (ha : a.toNat < 2 ^ 52) :
    ((a + 19#64) >>> 51).toNat = (a.toNat + 19) / 2 ^ 51 := by
  rw [bv64_ushr51_toNat, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
theorem bv64_add_ushr51_toNat_of_lt (a b : BitVec 64) (ha : a.toNat < 2 ^ 52) :
    (a + b >>> 51).toNat = a.toNat + b.toNat / 2 ^ 51 := by
  rw [BitVec.toNat_add, bv64_ushr51_toNat]; have := b.isLt; omega
theorem bv64_add_ushr51_ushr51_toNat_of_lt (a b : BitVec 64) (ha : a.toNat < 2 ^ 52) :
    ((a + b >>> 51) >>> 51).toNat = (a.toNat + (b >>> 51).toNat) / 2 ^ 51 := by
  rw [bv64_ushr51_toNat, BitVec.toNat_add, bv64_ushr51_toNat]; have := b.isLt; omega
theorem bv64_add_mul19_toNat_of_lt (a q : BitVec 64) (ha : a.toNat < 2 ^ 52) (hq : q.toNat ≤ 1) :
    (a + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64).toNat = a.toNat + q.toNat * 19 := by
  rw [BitVec.toNat_add, bv64_zext32_mul19_toNat] <;> omega

theorem fe51_to_bytes_canonical_val (l0 l1 l2 l3 l4 : BitVec 64)
    (hl0 : l0.toNat < 2 ^ 54) (hl1 : l1.toNat < 2 ^ 54)
    (hl2 : l2.toNat < 2 ^ 54) (hl3 : l3.toNat < 2 ^ 54) (hl4 : l4.toNat < 2 ^ 54)
    (h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4 : BitVec 64)
    (hh0 : h0 = (l0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l4 >>> 51)) * 19#64)
    (hh1 : h1 = (l1 &&& 2251799813685247#64) + l0 >>> 51)
    (hh2 : h2 = (l2 &&& 2251799813685247#64) + l1 >>> 51)
    (hh3 : h3 = (l3 &&& 2251799813685247#64) + l2 >>> 51)
    (hh4 : h4 = (l4 &&& 2251799813685247#64) + l3 >>> 51)
    (hq : q = (h4 + (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51)
    (hu0 : u0 = h0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64)
    (hu1 : u1 = h1 + u0 >>> 51) (hu2 : u2 = h2 + u1 >>> 51)
    (hu3 : u3 = h3 + u2 >>> 51) (hu4 : u4 = h4 + u3 >>> 51) :
    fe51Val l0 l1 l2 l3 l4 % p25519 =
      (u0.toNat % 2 ^ 51) + (u1.toNat % 2 ^ 51) * 2 ^ 51 +
      (u2.toNat % 2 ^ 51) * 2 ^ 102 + (u3.toNat % 2 ^ 51) * 2 ^ 153 + (u4.toNat % 2 ^ 51) * 2 ^ 204 := by
  have nh0 : h0.toNat = l0.toNat % 2 ^ 51 + (l4.toNat / 2 ^ 51) * 19 := hh0 ▸ bv64_mask51_add_mul19_toNat l0 l4 hl4
  have nh1 : h1.toNat = l1.toNat % 2 ^ 51 + l0.toNat / 2 ^ 51 := hh1 ▸ bv64_mask51_add_ushr51_toNat l1 l0
  have nh2 : h2.toNat = l2.toNat % 2 ^ 51 + l1.toNat / 2 ^ 51 := hh2 ▸ bv64_mask51_add_ushr51_toNat l2 l1
  have nh3 : h3.toNat = l3.toNat % 2 ^ 51 + l2.toNat / 2 ^ 51 := hh3 ▸ bv64_mask51_add_ushr51_toNat l3 l2
  have nh4 : h4.toNat = l4.toNat % 2 ^ 51 + l3.toNat / 2 ^ 51 := hh4 ▸ bv64_mask51_add_ushr51_toNat l4 l3
  obtain ⟨bh0, bh1, bh2, bh3, bh4, _⟩ :=
    fe51_h_bounds l0.toNat l1.toNat l2.toNat l3.toNat l4.toNat h0.toNat h1.toNat h2.toNat h3.toNat h4.toNat
      hl0 hl1 hl2 hl3 hl4 nh0 nh1 nh2 nh3 nh4
  have bh0' : h0.toNat < 2 ^ 52 := Nat.lt_trans bh0 (by decide)
  have bh1' : h1.toNat < 2 ^ 52 := Nat.lt_trans bh1 (by decide)
  have bh2' : h2.toNat < 2 ^ 52 := Nat.lt_trans bh2 (by decide)
  have bh3' : h3.toNat < 2 ^ 52 := Nat.lt_trans bh3 (by decide)
  have bh4' : h4.toNat < 2 ^ 52 := Nat.lt_trans bh4 (by decide)
  have e0 := bv64_add19_ushr51_toNat h0 bh0'
  have e1 := bv64_add_ushr51_ushr51_toNat_of_lt h1 (h0 + 19#64) bh1'
  have e2 := bv64_add_ushr51_ushr51_toNat_of_lt h2 (h1 + (h0 + 19#64) >>> 51) bh2'
  have e3 := bv64_add_ushr51_ushr51_toNat_of_lt h3 (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) bh3'
  have nq : q.toNat = (h4.toNat + ((h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51).toNat) / 2 ^ 51 :=
    hq ▸ bv64_add_ushr51_ushr51_toNat_of_lt h4 (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) bh4'
  have hq_le := fe51_q_le_one h0.toNat h1.toNat h2.toNat h3.toNat h4.toNat
    ((h0 + 19#64) >>> 51).toNat ((h1 + (h0 + 19#64) >>> 51) >>> 51).toNat
    ((h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51).toNat
    ((h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51).toNat
    q.toNat bh0 bh1 bh2 bh3 bh4 e0 e1 e2 e3 nq
  have nu0 : u0.toNat = h0.toNat + q.toNat * 19 := hu0 ▸ bv64_add_mul19_toNat_of_lt h0 q bh0' hq_le
  have nu1 : u1.toNat = h1.toNat + u0.toNat / 2 ^ 51 := hu1 ▸ bv64_add_ushr51_toNat_of_lt h1 u0 bh1'
  have nu2 : u2.toNat = h2.toNat + u1.toNat / 2 ^ 51 := hu2 ▸ bv64_add_ushr51_toNat_of_lt h2 u1 bh2'
  have nu3 : u3.toNat = h3.toNat + u2.toNat / 2 ^ 51 := hu3 ▸ bv64_add_ushr51_toNat_of_lt h3 u2 bh3'
  have nu4 : u4.toNat = h4.toNat + u3.toNat / 2 ^ 51 := hu4 ▸ bv64_add_ushr51_toNat_of_lt h4 u3 bh4'
  exact fe51_canonicalize_nat l0.toNat l1.toNat l2.toNat l3.toNat l4.toNat
    h0.toNat h1.toNat h2.toNat h3.toNat h4.toNat ((h0 + 19#64) >>> 51).toNat
    ((h1 + (h0 + 19#64) >>> 51) >>> 51).toNat ((h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51).toNat
    ((h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51).toNat
    q.toNat u0.toNat u1.toNat u2.toNat u3.toNat u4.toNat
    hl0 hl1 hl2 hl3 hl4 nh0 nh1 nh2 nh3 nh4 e0 e1 e2 e3 nq nu0 nu1 nu2 nu3 nu4

theorem fe51_byte6_eq (u0 u1 : BitVec 64) :
    BitVec.zeroExtend 8
      (BitVec.setWidth 64 (BitVec.setWidth 32 (u0 >>> 48)) &&& 18446744069414584327#64 |||
        (BitVec.setWidth 64 (BitVec.setWidth 32 u1) &&& 536870911#64) <<< 3) =
      BitVec.ofNat 8 (((u0.toNat % 2 ^ 51 + (u1.toNat % 2 ^ 51) * 2 ^ 51) / 2 ^ 48) % 256) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hu := Nat.lt_two_pow_self (n := 64)
  interval_cases i <;>
    simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat] <;>
    simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, BitVec.getLsbD,
      Nat.testBit_eq_decide_div_mod_eq, decide_eq_decide] <;> simp <;> omega

theorem fe51_byte12_eq (u1 u2 : BitVec 64) :
    BitVec.truncate 8 (BitVec.setWidth 32 (u1 >>> 45 &&& 63#64) ||| BitVec.setWidth 32 u2 <<< 6) =
      BitVec.ofNat 8 (((u1.toNat % 2 ^ 51 + (u2.toNat % 2 ^ 51) * 2 ^ 51) / 2 ^ 45) % 256) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hu := Nat.lt_two_pow_self (n := 64)
  interval_cases i <;>
    simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat] <;>
    simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, BitVec.getLsbD,
      Nat.testBit_eq_decide_div_mod_eq, decide_eq_decide] <;> simp <;> omega

theorem fe51_byte19_eq (u2 u3 : BitVec 64) :
    BitVec.truncate 8 (BitVec.setWidth 32 (u2 >>> 50 &&& 1#64) ||| BitVec.setWidth 32 u3 <<< 1) =
      BitVec.ofNat 8 (((u2.toNat % 2 ^ 51 + (u3.toNat % 2 ^ 51) * 2 ^ 51) / 2 ^ 50) % 256) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hu := Nat.lt_two_pow_self (n := 64)
  interval_cases i <;>
    simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat] <;>
    simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, BitVec.getLsbD,
      Nat.testBit_eq_decide_div_mod_eq, decide_eq_decide] <;> simp <;> omega

theorem fe51_byte25_eq (u3 u4 : BitVec 64) :
    BitVec.truncate 8 (BitVec.setWidth 32 (u3 >>> 47 &&& 15#64) ||| BitVec.setWidth 32 u4 <<< 4) =
      BitVec.ofNat 8 (((u3.toNat % 2 ^ 51 + (u4.toNat % 2 ^ 51) * 2 ^ 51) / 2 ^ 47) % 256) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hu := Nat.lt_two_pow_self (n := 64)
  interval_cases i <;>
    simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat] <;>
    simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, BitVec.getLsbD,
      Nat.testBit_eq_decide_div_mod_eq, decide_eq_decide] <;> simp <;> omega

theorem fe51_byte31_eq (u4 : BitVec 64) :
    BitVec.zeroExtend 8 (u4 >>> 44 &&& 127#64) =
      BitVec.ofNat 8 (((u4.toNat % 2 ^ 51) / 2 ^ 44) % 256) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hu := Nat.lt_two_pow_self (n := 64)
  interval_cases i <;>
    simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat] <;>
    simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, BitVec.getLsbD,
      Nat.testBit_eq_decide_div_mod_eq, decide_eq_decide] <;> simp <;> omega

theorem limb_div_step (c R n m : Nat) (hc : c < 2 ^ 51) (hm : n = 2 ^ 51 * m) :
    (c + R * 2 ^ 51) / n = R / m := by
  have hd : (c + R * 2 ^ 51) / 2 ^ 51 = R := by omega
  rw [hm, ← Nat.div_div_eq_div_mul, hd]

theorem limb_byte_interior (u : BitVec 64) (R s k : Nat) (hk : 2 ^ 51 = 2 ^ s * (256 * k)) :
    BitVec.ofNat 8 ((((u.toNat % 2 ^ 51) + R * 2 ^ 51) / 2 ^ s) % 256) =
      BitVec.zeroExtend 8 (u >>> s) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change (((u.toNat % 2 ^ 51 + R * 2 ^ 51) / 2 ^ s) % 256) % 256 = (u.toNat / 2 ^ s) % 256
  rw [Nat.mod_mod]
  have h1 : u.toNat % 2 ^ 51 + R * 2 ^ 51 = u.toNat % 2 ^ 51 + 2 ^ s * (256 * (k * R)) := by
    rw [hk, Nat.mul_comm R, Nat.mul_assoc, Nat.mul_assoc]
  have h2 : u.toNat = u.toNat % 2 ^ 51 + 2 ^ s * (256 * (k * (u.toNat / 2 ^ 51))) := by
    calc u.toNat = u.toNat % 2 ^ 51 + 2 ^ 51 * (u.toNat / 2 ^ 51) := by rw [Nat.add_comm, Nat.div_add_mod]
      _ = u.toNat % 2 ^ 51 + 2 ^ s * (256 * (k * (u.toNat / 2 ^ 51))) := by rw [hk, Nat.mul_assoc, Nat.mul_assoc]
  have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
  rw [h1, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]
  conv => rhs; rw [h2, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]

theorem limb_byte_last (u : BitVec 64) (s k : Nat) (hk : 2 ^ 51 = 2 ^ s * (256 * k)) :
    BitVec.ofNat 8 (((u.toNat % 2 ^ 51) / 2 ^ s) % 256) = BitVec.zeroExtend 8 (u >>> s) := by
  simpa using limb_byte_interior u 0 s k hk

theorem limb_byte_boundary (c d R s k : Nat) (hk : 2 ^ 102 = 2 ^ s * (256 * k)) :
    ((c + (d + R * 2 ^ 51) * 2 ^ 51) / 2 ^ s) % 256 = ((c + d * 2 ^ 51) / 2 ^ s) % 256 := by
  have h1 : c + (d + R * 2 ^ 51) * 2 ^ 51 = (c + d * 2 ^ 51) + 2 ^ s * (256 * (k * R)) := by
    have hpow : (2 ^ 51 : Nat) * 2 ^ 51 = 2 ^ 102 := by decide
    rw [Nat.add_mul, ← Nat.add_assoc, Nat.mul_assoc R, hpow, hk, Nat.mul_comm R, Nat.mul_assoc, Nat.mul_assoc]
  rw [h1, Nat.add_mul_div_left _ _ (Nat.two_pow_pos s), Nat.add_mul_mod_self_left]

theorem limb_byte_boundary_bv (u v : BitVec 64) (R s k : Nat) (hk : 2 ^ 102 = 2 ^ s * (256 * k)) :
    BitVec.ofNat 8 ((((u.toNat % 2 ^ 51) + ((v.toNat % 2 ^ 51) + R * 2 ^ 51) * 2 ^ 51) / 2 ^ s) % 256) =
      BitVec.ofNat 8 ((((u.toNat % 2 ^ 51) + (v.toNat % 2 ^ 51) * 2 ^ 51) / 2 ^ s) % 256) := by
  rw [limb_byte_boundary (u.toNat % 2 ^ 51) (v.toNat % 2 ^ 51) R s k hk]

theorem natToLeBytes_32_eq (n : Nat) :
    natToLeBytes 32 n =
      [BitVec.ofNat 8 ((n / 2 ^ 0) % 256), BitVec.ofNat 8 ((n / 2 ^ 8) % 256), BitVec.ofNat 8 ((n / 2 ^ 16) % 256), BitVec.ofNat 8 ((n / 2 ^ 24) % 256),
       BitVec.ofNat 8 ((n / 2 ^ 32) % 256), BitVec.ofNat 8 ((n / 2 ^ 40) % 256), BitVec.ofNat 8 ((n / 2 ^ 48) % 256), BitVec.ofNat 8 ((n / 2 ^ 56) % 256),
       BitVec.ofNat 8 ((n / 2 ^ 64) % 256), BitVec.ofNat 8 ((n / 2 ^ 72) % 256), BitVec.ofNat 8 ((n / 2 ^ 80) % 256), BitVec.ofNat 8 ((n / 2 ^ 88) % 256),
       BitVec.ofNat 8 ((n / 2 ^ 96) % 256), BitVec.ofNat 8 ((n / 2 ^ 104) % 256), BitVec.ofNat 8 ((n / 2 ^ 112) % 256), BitVec.ofNat 8 ((n / 2 ^ 120) % 256),
       BitVec.ofNat 8 ((n / 2 ^ 128) % 256), BitVec.ofNat 8 ((n / 2 ^ 136) % 256), BitVec.ofNat 8 ((n / 2 ^ 144) % 256), BitVec.ofNat 8 ((n / 2 ^ 152) % 256),
       BitVec.ofNat 8 ((n / 2 ^ 160) % 256), BitVec.ofNat 8 ((n / 2 ^ 168) % 256), BitVec.ofNat 8 ((n / 2 ^ 176) % 256), BitVec.ofNat 8 ((n / 2 ^ 184) % 256),
       BitVec.ofNat 8 ((n / 2 ^ 192) % 256), BitVec.ofNat 8 ((n / 2 ^ 200) % 256), BitVec.ofNat 8 ((n / 2 ^ 208) % 256), BitVec.ofNat 8 ((n / 2 ^ 216) % 256),
       BitVec.ofNat 8 ((n / 2 ^ 224) % 256), BitVec.ofNat 8 ((n / 2 ^ 232) % 256), BitVec.ofNat 8 ((n / 2 ^ 240) % 256), BitVec.ofNat 8 ((n / 2 ^ 248) % 256)] := rfl

theorem packCanonical51Bytes_eq_natToLeBytes (u0 u1 u2 u3 u4 : BitVec 64) :
    packCanonical51Bytes u0 u1 u2 u3 u4 =
      natToLeBytes 32 ((u0.toNat % 2 ^ 51) + ((u1.toNat % 2 ^ 51) + ((u2.toNat % 2 ^ 51) +
        ((u3.toNat % 2 ^ 51) + (u4.toNat % 2 ^ 51) * 2 ^ 51) * 2 ^ 51) * 2 ^ 51) * 2 ^ 51) := by
  let V4 := u4.toNat % 2 ^ 51; let V3 := (u3.toNat % 2 ^ 51) + V4 * 2 ^ 51
  let V2 := (u2.toNat % 2 ^ 51) + V3 * 2 ^ 51; let V1 := (u1.toNat % 2 ^ 51) + V2 * 2 ^ 51
  let V0 := (u0.toNat % 2 ^ 51) + V1 * 2 ^ 51
  change packCanonical51Bytes u0 u1 u2 u3 u4 = natToLeBytes 32 V0; rw [natToLeBytes_32_eq]
  have d0 (n m : Nat) (h : n = 2 ^ 51 * m) : V0 / n = V1 / m := limb_div_step (u0.toNat % 2 ^ 51) V1 n m (Nat.mod_lt _ (by decide)) h
  have d1 (n m : Nat) (h : n = 2 ^ 51 * m) : V1 / n = V2 / m := limb_div_step (u1.toNat % 2 ^ 51) V2 n m (Nat.mod_lt _ (by decide)) h
  have d2 (n m : Nat) (h : n = 2 ^ 51 * m) : V2 / n = V3 / m := limb_div_step (u2.toNat % 2 ^ 51) V3 n m (Nat.mod_lt _ (by decide)) h
  have d3 (n m : Nat) (h : n = 2 ^ 51 * m) : V3 / n = V4 / m := limb_div_step (u3.toNat % 2 ^ 51) V4 n m (Nat.mod_lt _ (by decide)) h
  rw [d0 (2 ^ 56) (2 ^ 5) (by decide), d0 (2 ^ 64) (2 ^ 13) (by decide), d0 (2 ^ 72) (2 ^ 21) (by decide), d0 (2 ^ 80) (2 ^ 29) (by decide),
      d0 (2 ^ 88) (2 ^ 37) (by decide), d0 (2 ^ 96) (2 ^ 45) (by decide), d0 (2 ^ 104) (2 ^ 53) (by decide), d1 (2 ^ 53) (2 ^ 2) (by decide),
      d0 (2 ^ 112) (2 ^ 61) (by decide), d1 (2 ^ 61) (2 ^ 10) (by decide), d0 (2 ^ 120) (2 ^ 69) (by decide), d1 (2 ^ 69) (2 ^ 18) (by decide),
      d0 (2 ^ 128) (2 ^ 77) (by decide), d1 (2 ^ 77) (2 ^ 26) (by decide), d0 (2 ^ 136) (2 ^ 85) (by decide), d1 (2 ^ 85) (2 ^ 34) (by decide),
      d0 (2 ^ 144) (2 ^ 93) (by decide), d1 (2 ^ 93) (2 ^ 42) (by decide), d0 (2 ^ 152) (2 ^ 101) (by decide), d1 (2 ^ 101) (2 ^ 50) (by decide),
      d0 (2 ^ 160) (2 ^ 109) (by decide), d1 (2 ^ 109) (2 ^ 58) (by decide), d2 (2 ^ 58) (2 ^ 7) (by decide),
      d0 (2 ^ 168) (2 ^ 117) (by decide), d1 (2 ^ 117) (2 ^ 66) (by decide), d2 (2 ^ 66) (2 ^ 15) (by decide),
      d0 (2 ^ 176) (2 ^ 125) (by decide), d1 (2 ^ 125) (2 ^ 74) (by decide), d2 (2 ^ 74) (2 ^ 23) (by decide),
      d0 (2 ^ 184) (2 ^ 133) (by decide), d1 (2 ^ 133) (2 ^ 82) (by decide), d2 (2 ^ 82) (2 ^ 31) (by decide),
      d0 (2 ^ 192) (2 ^ 141) (by decide), d1 (2 ^ 141) (2 ^ 90) (by decide), d2 (2 ^ 90) (2 ^ 39) (by decide),
      d0 (2 ^ 200) (2 ^ 149) (by decide), d1 (2 ^ 149) (2 ^ 98) (by decide), d2 (2 ^ 98) (2 ^ 47) (by decide),
      d0 (2 ^ 208) (2 ^ 157) (by decide), d1 (2 ^ 157) (2 ^ 106) (by decide), d2 (2 ^ 106) (2 ^ 55) (by decide), d3 (2 ^ 55) (2 ^ 4) (by decide),
      d0 (2 ^ 216) (2 ^ 165) (by decide), d1 (2 ^ 165) (2 ^ 114) (by decide), d2 (2 ^ 114) (2 ^ 63) (by decide), d3 (2 ^ 63) (2 ^ 12) (by decide),
      d0 (2 ^ 224) (2 ^ 173) (by decide), d1 (2 ^ 173) (2 ^ 122) (by decide), d2 (2 ^ 122) (2 ^ 71) (by decide), d3 (2 ^ 71) (2 ^ 20) (by decide),
      d0 (2 ^ 232) (2 ^ 181) (by decide), d1 (2 ^ 181) (2 ^ 130) (by decide), d2 (2 ^ 130) (2 ^ 79) (by decide), d3 (2 ^ 79) (2 ^ 28) (by decide),
      d0 (2 ^ 240) (2 ^ 189) (by decide), d1 (2 ^ 189) (2 ^ 138) (by decide), d2 (2 ^ 138) (2 ^ 87) (by decide), d3 (2 ^ 87) (2 ^ 36) (by decide),
      d0 (2 ^ 248) (2 ^ 197) (by decide), d1 (2 ^ 197) (2 ^ 146) (by decide), d2 (2 ^ 146) (2 ^ 95) (by decide), d3 (2 ^ 95) (2 ^ 44) (by decide)]
  rw [limb_byte_interior u0 V1 0 (2 ^ 43) (by decide), BitVec.ushiftRight_zero,
      limb_byte_interior u0 V1 8 (2 ^ 35) (by decide), limb_byte_interior u0 V1 16 (2 ^ 27) (by decide),
      limb_byte_interior u0 V1 24 (2 ^ 19) (by decide), limb_byte_interior u0 V1 32 (2 ^ 11) (by decide),
      limb_byte_interior u0 V1 40 (2 ^ 3) (by decide), limb_byte_boundary_bv u0 u1 V2 48 (2 ^ 46) (by decide), ← fe51_byte6_eq u0 u1,
      limb_byte_interior u1 V2 5 (2 ^ 38) (by decide), limb_byte_interior u1 V2 13 (2 ^ 30) (by decide),
      limb_byte_interior u1 V2 21 (2 ^ 22) (by decide), limb_byte_interior u1 V2 29 (2 ^ 14) (by decide),
      limb_byte_interior u1 V2 37 (2 ^ 6) (by decide), limb_byte_boundary_bv u1 u2 V3 45 (2 ^ 49) (by decide), ← fe51_byte12_eq u1 u2,
      limb_byte_interior u2 V3 2 (2 ^ 41) (by decide), limb_byte_interior u2 V3 10 (2 ^ 33) (by decide),
      limb_byte_interior u2 V3 18 (2 ^ 25) (by decide), limb_byte_interior u2 V3 26 (2 ^ 17) (by decide),
      limb_byte_interior u2 V3 34 (2 ^ 9) (by decide), limb_byte_interior u2 V3 42 (2 ^ 1) (by decide),
      limb_byte_boundary_bv u2 u3 V4 50 (2 ^ 44) (by decide), ← fe51_byte19_eq u2 u3,
      limb_byte_interior u3 V4 7 (2 ^ 36) (by decide), limb_byte_interior u3 V4 15 (2 ^ 28) (by decide),
      limb_byte_interior u3 V4 23 (2 ^ 20) (by decide), limb_byte_interior u3 V4 31 (2 ^ 12) (by decide),
      limb_byte_interior u3 V4 39 (2 ^ 4) (by decide), ← fe51_byte25_eq u3 u4,
      limb_byte_last u4 4 (2 ^ 39) (by decide), limb_byte_last u4 12 (2 ^ 31) (by decide),
      limb_byte_last u4 20 (2 ^ 23) (by decide), limb_byte_last u4 28 (2 ^ 15) (by decide),
      limb_byte_last u4 36 (2 ^ 7) (by decide), ← fe51_byte31_eq u4]; rfl

theorem fe51_horner_eq (c0 c1 c2 c3 c4 : Nat) :
    c0 + c1 * 2 ^ 51 + c2 * 2 ^ 102 + c3 * 2 ^ 153 + c4 * 2 ^ 204 =
      c0 + (c1 + (c2 + (c3 + c4 * 2 ^ 51) * 2 ^ 51) * 2 ^ 51) * 2 ^ 51 := by omega

theorem fe51_to_bytes_math (l0 l1 l2 l3 l4 : BitVec 64)
    (hl0 : l0.toNat < 2 ^ 54) (hl1 : l1.toNat < 2 ^ 54) (hl2 : l2.toNat < 2 ^ 54) (hl3 : l3.toNat < 2 ^ 54) (hl4 : l4.toNat < 2 ^ 54)
    (h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4 : BitVec 64)
    (hh0 : h0 = (l0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l4 >>> 51)) * 19#64)
    (hh1 : h1 = (l1 &&& 2251799813685247#64) + l0 >>> 51) (hh2 : h2 = (l2 &&& 2251799813685247#64) + l1 >>> 51)
    (hh3 : h3 = (l3 &&& 2251799813685247#64) + l2 >>> 51) (hh4 : h4 = (l4 &&& 2251799813685247#64) + l3 >>> 51)
    (hq : q = (h4 + (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51)
    (hu0 : u0 = h0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64)
    (hu1 : u1 = h1 + u0 >>> 51) (hu2 : u2 = h2 + u1 >>> 51) (hu3 : u3 = h3 + u2 >>> 51) (hu4 : u4 = h4 + u3 >>> 51) :
    packCanonical51Bytes u0 u1 u2 u3 u4 = natToLeBytes 32 (fe51Val l0 l1 l2 l3 l4 % p25519) := by
  have hval := fe51_to_bytes_canonical_val l0 l1 l2 l3 l4 hl0 hl1 hl2 hl3 hl4
    h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4 hh0 hh1 hh2 hh3 hh4 hq hu0 hu1 hu2 hu3 hu4
  rw [hval, fe51_horner_eq, packCanonical51Bytes_eq_natToLeBytes]

end X25519Dalek.TB

end
end

section
section
namespace X25519Dalek

theorem fe51_to_bytes_eq_natToLeBytes_dev (l0 l1 l2 l3 l4 : BitVec 64)
    (hl0 : l0.toNat < 2 ^ 54) (hl1 : l1.toNat < 2 ^ 54) (hl2 : l2.toNat < 2 ^ 54) (hl3 : l3.toNat < 2 ^ 54) (hl4 : l4.toNat < 2 ^ 54)
    (h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4 : BitVec 64)
    (hh0 : h0 = (l0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l4 >>> 51)) * 19#64)
    (hh1 : h1 = (l1 &&& 2251799813685247#64) + l0 >>> 51) (hh2 : h2 = (l2 &&& 2251799813685247#64) + l1 >>> 51)
    (hh3 : h3 = (l3 &&& 2251799813685247#64) + l2 >>> 51) (hh4 : h4 = (l4 &&& 2251799813685247#64) + l3 >>> 51)
    (hq : q = (h4 + (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51)
    (hu0 : u0 = h0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64)
    (hu1 : u1 = h1 + u0 >>> 51) (hu2 : u2 = h2 + u1 >>> 51) (hu3 : u3 = h3 + u2 >>> 51) (hu4 : u4 = h4 + u3 >>> 51) :
    [BitVec.zeroExtend 8 u0, BitVec.zeroExtend 8 (u0 >>> 8), BitVec.zeroExtend 8 (u0 >>> 16),
      BitVec.zeroExtend 8 (u0 >>> 24), BitVec.zeroExtend 8 (u0 >>> 32), BitVec.zeroExtend 8 (u0 >>> 40),
      BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (u0 >>> 48)) &&& 18446744069414584327#64 |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 u1) &&& 536870911#64) <<< 3),
      BitVec.zeroExtend 8 (u1 >>> 5), BitVec.zeroExtend 8 (u1 >>> 13), BitVec.zeroExtend 8 (u1 >>> 21),
      BitVec.zeroExtend 8 (u1 >>> 29), BitVec.zeroExtend 8 (u1 >>> 37),
      BitVec.truncate 8 (BitVec.setWidth 32 (u1 >>> 45 &&& 63#64) ||| BitVec.setWidth 32 u2 <<< 6),
      BitVec.zeroExtend 8 (u2 >>> 2), BitVec.zeroExtend 8 (u2 >>> 10), BitVec.zeroExtend 8 (u2 >>> 18),
      BitVec.zeroExtend 8 (u2 >>> 26), BitVec.zeroExtend 8 (u2 >>> 34), BitVec.zeroExtend 8 (u2 >>> 42),
      BitVec.truncate 8 (BitVec.setWidth 32 (u2 >>> 50 &&& 1#64) ||| BitVec.setWidth 32 u3 <<< 1),
      BitVec.zeroExtend 8 (u3 >>> 7), BitVec.zeroExtend 8 (u3 >>> 15), BitVec.zeroExtend 8 (u3 >>> 23),
      BitVec.zeroExtend 8 (u3 >>> 31), BitVec.zeroExtend 8 (u3 >>> 39),
      BitVec.truncate 8 (BitVec.setWidth 32 (u3 >>> 47 &&& 15#64) ||| BitVec.setWidth 32 u4 <<< 4),
      BitVec.zeroExtend 8 (u4 >>> 4), BitVec.zeroExtend 8 (u4 >>> 12), BitVec.zeroExtend 8 (u4 >>> 20),
      BitVec.zeroExtend 8 (u4 >>> 28), BitVec.zeroExtend 8 (u4 >>> 36), BitVec.zeroExtend 8 (u4 >>> 44 &&& 127#64)]
      = natToLeBytes 32 (fe51Val l0 l1 l2 l3 l4 % p25519) := by
  exact TB.fe51_to_bytes_math l0 l1 l2 l3 l4 hl0 hl1 hl2 hl3 hl4 h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4
    hh0 hh1 hh2 hh3 hh4 hq hu0 hu1 hu2 hu3 hu4

end X25519Dalek

end
end

section
open X25519Dalek

theorem solution (l0 l1 l2 l3 l4 : BitVec 64)
    (hl0 : l0.toNat < 2 ^ 54) (hl1 : l1.toNat < 2 ^ 54) (hl2 : l2.toNat < 2 ^ 54) (hl3 : l3.toNat < 2 ^ 54) (hl4 : l4.toNat < 2 ^ 54)
    (h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4 : BitVec 64)
    (hh0 : h0 = (l0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l4 >>> 51)) * 19#64)
    (hh1 : h1 = (l1 &&& 2251799813685247#64) + l0 >>> 51) (hh2 : h2 = (l2 &&& 2251799813685247#64) + l1 >>> 51)
    (hh3 : h3 = (l3 &&& 2251799813685247#64) + l2 >>> 51) (hh4 : h4 = (l4 &&& 2251799813685247#64) + l3 >>> 51)
    (hq : q = (h4 + (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51)
    (hu0 : u0 = h0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64)
    (hu1 : u1 = h1 + u0 >>> 51) (hu2 : u2 = h2 + u1 >>> 51) (hu3 : u3 = h3 + u2 >>> 51) (hu4 : u4 = h4 + u3 >>> 51) :
    [BitVec.zeroExtend 8 u0, BitVec.zeroExtend 8 (u0 >>> 8), BitVec.zeroExtend 8 (u0 >>> 16),
      BitVec.zeroExtend 8 (u0 >>> 24), BitVec.zeroExtend 8 (u0 >>> 32), BitVec.zeroExtend 8 (u0 >>> 40),
      BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (u0 >>> 48)) &&& 18446744069414584327#64 |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 u1) &&& 536870911#64) <<< 3),
      BitVec.zeroExtend 8 (u1 >>> 5), BitVec.zeroExtend 8 (u1 >>> 13), BitVec.zeroExtend 8 (u1 >>> 21),
      BitVec.zeroExtend 8 (u1 >>> 29), BitVec.zeroExtend 8 (u1 >>> 37),
      BitVec.truncate 8 (BitVec.setWidth 32 (u1 >>> 45 &&& 63#64) ||| BitVec.setWidth 32 u2 <<< 6),
      BitVec.zeroExtend 8 (u2 >>> 2), BitVec.zeroExtend 8 (u2 >>> 10), BitVec.zeroExtend 8 (u2 >>> 18),
      BitVec.zeroExtend 8 (u2 >>> 26), BitVec.zeroExtend 8 (u2 >>> 34), BitVec.zeroExtend 8 (u2 >>> 42),
      BitVec.truncate 8 (BitVec.setWidth 32 (u2 >>> 50 &&& 1#64) ||| BitVec.setWidth 32 u3 <<< 1),
      BitVec.zeroExtend 8 (u3 >>> 7), BitVec.zeroExtend 8 (u3 >>> 15), BitVec.zeroExtend 8 (u3 >>> 23),
      BitVec.zeroExtend 8 (u3 >>> 31), BitVec.zeroExtend 8 (u3 >>> 39),
      BitVec.truncate 8 (BitVec.setWidth 32 (u3 >>> 47 &&& 15#64) ||| BitVec.setWidth 32 u4 <<< 4),
      BitVec.zeroExtend 8 (u4 >>> 4), BitVec.zeroExtend 8 (u4 >>> 12), BitVec.zeroExtend 8 (u4 >>> 20),
      BitVec.zeroExtend 8 (u4 >>> 28), BitVec.zeroExtend 8 (u4 >>> 36), BitVec.zeroExtend 8 (u4 >>> 44 &&& 127#64)]
      = natToLeBytes 32 (fe51Val l0 l1 l2 l3 l4 % p25519) := by
  apply X25519Dalek.fe51_to_bytes_eq_natToLeBytes_dev <;> assumption

end
