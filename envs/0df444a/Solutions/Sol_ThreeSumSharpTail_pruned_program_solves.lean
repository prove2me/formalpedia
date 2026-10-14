-- Prove2me | solution 1 for ThreeSumSharpTail.pruned_program_solves
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T20:57:13.411964+00:00
-- url     : https://prove2.me/submissions/2fa28e8d-0fae-44e3-a2e4-e366fea0a0d5

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_APSP299791_Defs5
import Theorems.Thm_ThreeSumSharpTail_pruned_program_correct

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt}
    (h : P[p]? = some body) (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h

theorem Exec.append {s : Stmt} {σ σ' : State} {c : ℕ}
    (h : Exec lim P d s σ σ' c) (R : Program) :
    Exec lim (P ++ R) d s σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (getElem?_append_of_eq_some h₂ R) h₃ ih

theorem Ends.append {s σ T Q} (h : Ends lim P d s σ T Q) (R : Program) :
    Ends lim (P ++ R) d s σ T Q := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.append R, hc, hq⟩
end Light
end

section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Meets.append {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T : ℕ}
    {R : ℤ → (ℕ → ℤ) → Prop} (h : Meets lim P p d vals μ T R) (P' : Program) :
    Meets lim (P ++ P') p d vals μ T R := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp P', he.append P'⟩
end Light
end

section
-- Source module: ThreeSumApsp.Util.Ceil
public section
namespace Light

namespace Nat

/-- `a ⌈/⌉ b ≤ k` says that `k` pieces of size `b` cover `a`. Mathlib's `ceilDiv_le_iff_le_mul` has
`b * k` on the right. -/
theorem ceilDiv_le_iff {a b k : ℕ} (hb : 0 < b) : a ⌈/⌉ b ≤ k ↔ a ≤ k * b := by
  rw [ceilDiv_le_iff_le_mul hb, Nat.mul_comm]

/-- `i < a ⌈/⌉ b` says that `i` pieces of size `b` do not cover `a`. -/
theorem lt_ceilDiv_iff {a b i : ℕ} (hb : 0 < b) : i < a ⌈/⌉ b ↔ i * b < a := by
  rw [← Nat.not_le, ceilDiv_le_iff hb, Nat.not_le]

/-- The ceiling of the real quotient of two natural numbers, in natural numbers. -/
theorem ceil_div_eq_ceilDiv (a : ℕ) {b : ℕ} (hb : 0 < b) : ⌈(a : ℝ) / (b : ℝ)⌉₊ = a ⌈/⌉ b := by
  refine eq_of_forall_ge_iff fun k => ?_
  rw [Nat.ceil_le, div_le_iff₀ (Nat.cast_pos.2 hb), ceilDiv_le_iff hb]
  exact_mod_cast Iff.rfl

/-- Rounding `n ≥ 1` up to a power of `b` costs at most a factor `b`. -/
theorem pow_clog_le_mul {b n : ℕ} (hb : 1 < b) (hn : 1 ≤ n) : b ^ Nat.clog b n ≤ b * n := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn
  · simp [Nat.clog_one_right, hb.le]
  · have hpos : 0 < Nat.clog b n := Nat.clog_pos hb hn
    have hlt := Nat.pow_pred_clog_lt_self hb hn
    calc b ^ Nat.clog b n = b * b ^ (Nat.clog b n).pred := by
          rw [← Nat.pow_succ', Nat.succ_pred_eq_of_pos hpos]
      _ ≤ b * n := Nat.mul_le_mul_left b hlt.le

end Nat

namespace Real

end Real


end Light
end
end

section
-- Source module: ThreeSumApsp.Programs.Sec2.Theorem5.Places
@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

namespace Par

end Par

namespace Par

end Par

/-- The places of the shared block: each area begins where the one before it ends. -/
theorem Par.places (p : Par) (b0 : ℕ) :
    p.aDIR b0 = b0 ∧ p.aP3 b0 = b0 + 32 ∧ p.aP4 b0 = p.aP3 b0 + (p.L + 1)
      ∧ p.aP7 b0 = p.aP4 b0 + (p.L + 1)
      ∧ p.aP10 b0 = p.aP7 b0 + (p.L + 1) ∧ p.aPAS b0 = p.aP10 b0 + (p.L + 1)
      ∧ p.aPHI b0 = p.aPAS b0 + (p.L + 2) ∧ p.aPSI b0 = p.aPHI b0 + 70
      ∧ p.aMASK b0 = p.aPSI b0 + 70 ∧ p.aBAND b0 = p.aMASK b0 + p.KK * p.L
      ∧ p.aBLOCK b0 = p.aBAND b0 + p.N ∧ p.aDIG3 b0 = p.aBLOCK b0 + p.N
      ∧ p.aDIG4 b0 = p.aDIG3 b0 + p.N * p.Lo ∧ p.aENCA b0 = p.aDIG4 b0 + p.D * p.m
      ∧ p.aENCB b0 = p.aENCA b0 + p.nB * p.T ∧ p.aARR b0 = p.aENCB b0 + p.nB * p.T
      ∧ p.aZS b0 = p.aARR b0 + p.S7 ∧ p.sharedEnd b0 = p.aZS b0 + p.S7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace Par
variable (p : Par)

end Par

end Light.Sec2
end
end

section
-- Source module: ThreeSumApsp.Sec4.Theorem30
@[expose] public section

open Finset

namespace ThreeSumApsp

/-- Proof of Theorem 30, "Preprocessing": "we store the K₀² subsets, in O(KL) ≤ O(10^L) operations".
Read as the inequality `K L ≤ 10^L` (constant 1). -/
theorem Theorem30.subsets (L m : ℕ) : ThreeSumApsp.K L m * L ≤ 10 ^ L := by
  calc ThreeSumApsp.K L m * L ≤ 2 ^ L * 2 ^ L :=
        Nat.mul_le_mul (Nat.choose_le_two_pow L m) Nat.lt_two_pow_self.le
    _ = 4 ^ L := by rw [← Nat.mul_pow]
    _ ≤ 10 ^ L := Nat.pow_le_pow_left (by norm_num) L

/-- Proof of Theorem 30, "Preprocessing": "K N₀ D ≤ 7^L". This bounds the number of nonzero entries
of the input array of a band, which is why forming it takes `O(L · 7^L)` operations. -/
theorem Theorem30.K_mul_N0_mul_D_le (L m : ℕ) : ThreeSumApsp.K L m * ThreeSumApsp.N0 L m * ThreeSumApsp.D m ≤ 7 ^ L := by
  -- one summand of the binomial expansion of `(4 + 3)^L`
  calc ThreeSumApsp.K L m * ThreeSumApsp.N0 L m * ThreeSumApsp.D m = L.choose m * 4 ^ m * 3 ^ (L - m) := by unfold ThreeSumApsp.K ThreeSumApsp.N0 ThreeSumApsp.D; ring
    _ ≤ 7 ^ L := Nat.choose_mul_pow_mul_pow_le 4 3 L m

/-- Proof of Theorem 30, "Preprocessing": forming the input array of a band takes "O(L · 7^L)
operations", which is within the "O(10^L) operations" of its encoding ("This is the last term of
(8)"). Read as the inequality `L · 7^L ≤ 2 · 10^L`; the constant 1 fails at `L = 3`. From `L = 3`
on, one more level multiplies the left-hand side by `7(L+1)/L ≤ 10`. -/
theorem Theorem30.form_array : ∀ L : ℕ, L * 7 ^ L ≤ 2 * 10 ^ L
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | 3 => by norm_num
  | L + 4 =>
    calc (L + 4) * 7 ^ (L + 4) = (7 * (L + 4)) * 7 ^ (L + 3) := by ring
      _ ≤ (10 * (L + 3)) * 7 ^ (L + 3) := Nat.mul_le_mul_right _ (by omega)
      _ = 10 * ((L + 3) * 7 ^ (L + 3)) := by ring
      _ ≤ 10 * (2 * 10 ^ (L + 3)) := Nat.mul_le_mul_left _ (Theorem30.form_array (L + 3))
      _ = 2 * 10 ^ (L + 4) := by ring

/-- Proof of Theorem 30, "Word size": "Since N ≥ N₀ = 3^{L-m} and L ≥ 10m, we have 10^L ≤ N^{5/2}".
Stated after squaring, to stay in the natural numbers. -/
theorem Theorem30.ten_pow_le (L m N : ℕ) (hL : 10 * m ≤ L) (hN : ThreeSumApsp.N0 L m ≤ N) :
    (10 ^ L) ^ 2 ≤ N ^ 5 := by
  -- squared once more: `10^{4L} ≤ 3^{9L} ≤ 3^{10(L-m)}`
  have hsq : ((10 ^ L) ^ 2) ^ 2 ≤ ((3 ^ (L - m)) ^ 5) ^ 2 :=
    calc ((10 ^ L) ^ 2) ^ 2 = 10000 ^ L := by
          rw [← pow_mul, ← pow_mul, mul_comm L, pow_mul]; norm_num
      _ ≤ 19683 ^ L := Nat.pow_le_pow_left (by norm_num) L
      _ = 3 ^ (9 * L) := by rw [pow_mul]; norm_num
      _ ≤ 3 ^ ((L - m) * 5 * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = ((3 ^ (L - m)) ^ 5) ^ 2 := by rw [pow_mul, pow_mul]
  exact ((Nat.pow_le_pow_iff_left (by norm_num)).mp hsq).trans (Nat.pow_le_pow_left hN 5)
end ThreeSumApsp
end
end

section
-- Source module: ThreeSumApsp.Programs.Sec4.Theorem30.Memory
@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-- The tables and the areas lie as Areas says. -/
theorem areas (p : Sec2.Par) (t b0 : ℕ) : Areas p t b0 := by
  have hplaces := p.places b0
  have hWD : aWD p b0 = p.sharedEnd b0 := rfl
  have hCUR : aCUR p b0 = aWD p b0 + p.L := rfl
  have hBOX : aBOX p b0 = aCUR p b0 + p.L := rfl
  have hSS : aSS p b0 = aBOX p b0 + p.L := rfl
  have hFP : aFP p b0 = aSS p b0 + p.m := rfl
  have hROOTS : aROOTS p b0 = aFP p b0 + 1 := rfl
  have hTR : aTR p b0 = aROOTS p b0 + p.nB * p.nB := rfl
  have hTOP : Light.Sec4.top p t b0 = aTR p b0 + trieCap p t + 1 := rfl
  constructor <;> omega

/-- The directory lies before the areas of Section 4. -/
theorem wd_ge (p : Sec2.Par) (b0 : ℕ) : b0 + 32 ≤ aWD p b0 := by
  obtain ⟨⟩ := Light.Sec4.areas p 0 b0
  omega

/-- The shared block ends behind its base address. -/
theorem base_le_sharedEnd (p : Sec2.Par) (b0 : ℕ) : b0 ≤ p.sharedEnd b0 :=
  (Nat.le_add_right b0 32).trans (wd_ge p b0)

/-- The block holds more than its directory. -/
theorem base_add_lt_top (p : Sec2.Par) (t b0 : ℕ) : b0 + 32 < Light.Sec4.top p t b0 := by
  obtain ⟨⟩ := Light.Sec4.areas p t b0
  omega

/-- The block is not empty. -/
theorem base_lt_top (p : Sec2.Par) (t b0 : ℕ) : b0 < Light.Sec4.top p t b0 :=
  (Nat.le_add_right b0 32).trans_lt (base_add_lt_top p t b0)

/-- The scratch strings of a query lie in the block. -/
theorem scratch_in_block (p : Sec2.Par) (t b0 : ℕ) :
    b0 ≤ aWD p b0 ∧ aWD p b0 + (3 * p.L + p.m) ≤ Light.Sec4.top p t b0 := by
  obtain ⟨⟩ := Light.Sec4.areas p t b0
  omega

namespace Dir

end Dir
end Light.Sec4
end
end

section
-- Source module: ThreeSumApsp.Programs.Sec4.ChoosingParameters.Setup
@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

namespace Query31

end Query31

theorem abs_padInnerCols_le {N D₀ D' : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ} {U : ℤ}
    (h : ∀ i j, |X i j| ≤ U) (hU : 0 ≤ U) (i : Fin N) (j : Fin D') :
    |padInnerCols D' X i j| ≤ U := by
  unfold padInnerCols
  split_ifs
  · exact h _ _
  · simpa using hU

theorem abs_padInnerRows_le {N D₀ D' : ℕ} {Y : Matrix (Fin D₀) (Fin N) ℤ} {U : ℤ}
    (h : ∀ i j, |Y i j| ≤ U) (hU : 0 ≤ U) (i : Fin D') (j : Fin N) :
    |padInnerRows D' Y i j| ≤ U := by
  unfold padInnerRows
  split_ifs
  · exact h _ _
  · simpa using hU

theorem le_D_logFour (D₀ : ℕ) : D₀ ≤ ThreeSumApsp.D (logFour D₀) := Nat.le_pow_clog (by norm_num) D₀

/-- The ceiling ⌈log₄ D⌉ in natural numbers. -/
theorem ceil_logb_four (D₀ : ℕ) : ⌈Real.logb 4 (D₀ : ℝ)⌉₊ = logFour D₀ := by
  have := Real.natCeil_logb_natCast 4 D₀
  simpa [logFour] using this

/-- m ≤ 4 D, because m ≤ 4^m ≤ 4 D. -/
theorem logFour_le_four_mul {D₀ : ℕ} (hD : 1 ≤ D₀) : logFour D₀ ≤ 4 * D₀ :=
  le_trans (Nat.lt_pow_self (by norm_num)).le (Nat.pow_clog_le_mul (b := 4) (by norm_num) hD)

/-- m ≥ 1 means D ≥ 2. -/
theorem two_le_of_clog {D₀ : ℕ} (h : 1 ≤ logFour D₀) : 2 ≤ D₀ := by
  by_contra hc
  have : logFour D₀ = 0 := Nat.clog_of_right_le_one (by omega) 4
  omega

end Light.Sec4
end
end

section
-- Source module: ThreeSumApsp.Programs.Sec4.ChoosingParameters.Parameters
@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-- t ≤ m. -/
theorem RatParams.t_le (G : RatParams) (m : ℕ) : G.t m ≤ m := by
  unfold RatParams.t
  have hq := G.hq
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  have h1 : 10 * G.p * m ≤ 9 * G.q * m := Nat.mul_le_mul_right _ G.hθ.le
  have h2 : G.p * m ≤ G.q * m := by
    have e1 : 10 * G.p * m = 10 * (G.p * m) := by ring
    have e2 : 9 * G.q * m = 9 * (G.q * m) := by ring
    omega
  omega

/-- Below the threshold a structure has three cells. -/
theorem structEnd_small (h : logFour D₀ < G.m₀) (N fr : ℕ) : structEnd G N D₀ fr = fr + 3 :=
  if_pos h

/-- For m ≥ m₀ a structure ends with the block of Theorem 30. -/
theorem structEnd_large (h : G.m₀ ≤ logFour D₀) (N fr : ℕ) :
    structEnd G N D₀ fr = G.blockEnd N D₀ fr :=
  if_neg (not_lt.2 h)

/-- The block of Theorem 30 begins after the first three cells. -/
theorem add_three_le_blockAt (N D₀ fr : ℕ) : fr + 3 ≤ blockAt N D₀ fr := by
  unfold blockAt
  omega

/-- The block of Theorem 30 is not empty. -/
theorem RatParams.blockAt_lt_blockEnd (G : RatParams) (N D₀ fr : ℕ) :
    blockAt N D₀ fr < G.blockEnd N D₀ fr :=
  base_lt_top _ _ _

/-- The cells that a query of Theorem 30 writes lie in the block. -/
theorem RatParams.scratch_in_block (G : RatParams) (N D₀ fr : ℕ) :
    blockAt N D₀ fr ≤ aWD (parOf G N D₀) (blockAt N D₀ fr) ∧
      aWD (parOf G N D₀) (blockAt N D₀ fr) + (3 * (parOf G N D₀).L + (parOf G N D₀).m)
        ≤ G.blockEnd N D₀ fr :=
  Sec4.scratch_in_block _ _ _
end Light.Sec4
end
end

section
-- Source module: ThreeSumApsp.Programs.Sec4.Theorem30.TimeOfBlock
@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

/-- `(L + 1)² ≤ 10^L`. -/
theorem succ_sq_le_ten_pow (L : ℕ) : (L + 1) ^ 2 ≤ 10 ^ L := by
  have hfour : (L + 1) ^ 2 ≤ 4 ^ L := by
    induction L with
    | zero => simp
    | succ L ih =>
      calc (L + 1 + 1) ^ 2 ≤ 4 * (L + 1) ^ 2 := by
            rw [show (L + 1 + 1) ^ 2 = L * L + 4 * L + 4 by ring,
              show 4 * (L + 1) ^ 2 = 4 * (L * L) + 8 * L + 4 by ring]
            omega
        _ ≤ 4 * 4 ^ L := Nat.mul_le_mul_left _ ih
        _ = 4 ^ (L + 1) := by ring
  exact hfour.trans (Nat.pow_le_pow_left (by norm_num) L)

private theorem sizeFacts (p : Sec2.Par) (hL1 : 1 ≤ p.L) (hmL : p.m ≤ p.L) :
    SizeFacts p.L p.m p.K p.KK p.N0 p.D p.S7 p.T :=
  ⟨succ_sq_le_ten_pow p.L, Theorem30.subsets p.L p.m, Theorem30.K_mul_N0_mul_D_le p.L p.m,
    Theorem30.form_array p.L, Nat.pow_le_pow_left (by norm_num) p.L, Nat.sqrt_le _,
    Nat.choose_pos hmL, Nat.one_le_pow _ _ (by norm_num), Nat.one_le_pow _ _ (by norm_num), hL1,
    hmL⟩

/-- The length of the shared block. -/
theorem sharedEnd_sub_le (p : Sec2.Par) (b0 : ℕ) (hL1 : 1 ≤ p.L) (hmL : p.m ≤ p.L) :
    p.sharedEnd b0 - b0 ≤ 190 * 10 ^ p.L + 2 * (p.N * (p.L + 1)) + 2 * (p.nB * 10 ^ p.L) := by
  obtain ⟨sq, KL, KND, LS, ST, KKle, K1, N1, D1, L1, mL⟩ := sizeFacts p hL1 hmL
  have hLo : p.Lo ≤ p.L := Nat.sub_le _ _
  simp only [Sec2.Par.sharedEnd, Sec2.Par.aZS, Sec2.Par.aARR, Sec2.Par.aENCB, Sec2.Par.aENCA,
    Sec2.Par.aDIG4, Sec2.Par.aDIG3, Sec2.Par.aBLOCK, Sec2.Par.aBAND, Sec2.Par.aMASK, Sec2.Par.aPSI,
    Sec2.Par.aPHI, Sec2.Par.aPAS, Sec2.Par.aP10, Sec2.Par.aP7, Sec2.Par.aP4, Sec2.Par.aP3]
  change _ ≤ 190 * p.T + 2 * (p.N * (p.L + 1)) + 2 * (p.nB * p.T)
  generalize p.T = T at *
  generalize p.S7 = S7 at *
  generalize p.K = K at *
  generalize p.KK = KK at *
  generalize p.N0 = N0 at *
  generalize p.D = D at *
  generalize p.nB = nB at *
  generalize p.Lo = Lo at *
  generalize p.N = N at *
  generalize p.L = L at *
  generalize p.m = m at *
  have hLT : L + 1 ≤ T := (Nat.le_self_pow (by norm_num) _).trans sq
  have hDS : D ≤ S7 := le_trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos K1 N1)) KND
  have hmask : KK * L ≤ K * L := Nat.mul_le_mul_right _ KKle
  have hdig3 : N * Lo ≤ N * L := Nat.mul_le_mul_left _ hLo
  have hdig4 : D * m ≤ L * S7 := (Nat.mul_le_mul hDS mL).trans (le_of_eq (Nat.mul_comm _ _))
  rw [Nat.mul_add_one N L]
  omega

/-- The length of the block, split into the shared block, the scratch strings, and the tries with
their roots. -/
theorem top_sub_eq (p : Sec2.Par) (t b0 : ℕ) :
    Light.Sec4.top p t b0 - b0 = (p.sharedEnd b0 - b0) + (3 * p.L + p.m + 2)
      + (1 + p.nB * p.nB * (11 * (1 + p.L * (boxes p.L p.m t).card)) + p.nB * p.nB) := by
  have := base_le_sharedEnd p b0
  simp only [Light.Sec4.top, aTR, aROOTS, aFP, aSS, aBOX, aCUR, aWD, trieCap]
  omega

end Light.Sec4
end
end

section
-- Source module: ThreeSumApsp.Programs.Sec4.Theorem30.WordSize
@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

/-- There are at most `11^L` cubes. -/
theorem card_boxes_le (L m t : ℕ) : (boxes L m t).card ≤ 11 ^ L := by
  have hsymbols : Fintype.card CubeSymbol = 11 := rfl
  calc (boxes L m t).card ≤ (univ : Finset (Cube L)).card := card_filter_le _ _
    _ = 11 ^ L := by rw [card_univ, Fintype.card_fun, hsymbols, Fintype.card_fin]

/-- The number of bands is at most `N + 1`. -/
theorem numBands_le (L m N : ℕ) (hmL : m ≤ L) : numBands L m N ≤ N + 1 := by
  have hband : 1 ≤ bandSize L m :=
    Nat.mul_pos (Nat.sqrt_pos.mpr (Nat.choose_pos hmL)) (Nat.one_le_pow _ _ (by norm_num))
  have hN : N ≤ bandSize L m * N := Nat.le_mul_of_pos_left _ hband
  refine Nat.div_le_of_le_mul ?_
  rw [Nat.mul_add_one]
  omega

/-- `N₀ ≤ N` under the hypotheses of Theorem 30. -/
theorem N0_le_N {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) : N0 p.L p.m ≤ p.N := by
  have hmL : p.m ≤ p.L := by have := h.L_ge; omega
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (K p.L p.m : ℝ) :=
    Real.one_le_sqrt.2 (by exact_mod_cast Nat.choose_pos hmL)
  exact_mod_cast (le_mul_of_one_le_left (Nat.cast_nonneg _) hsqrt).trans h.N_ge

/-- "Since N ≥ N₀ = 3^{L-m} and L ≥ 10m, we have 10^L ≤ N^{5/2}": so all these quantities are at
most `(10^L)² ≤ N^5`. -/
theorem below {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) : Light.Sec4.Below p t ((p.N + 1) ^ 5) := by
  have hmL : p.m ≤ p.L := by have := h.L_ge; omega
  have hsq := Theorem30.ten_pow_le p.L p.m p.N h.L_ge (N0_le_N h)
  have hN5 : p.N ^ 5 ≤ (p.N + 1) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have hten : 10 ^ p.L ≤ (10 ^ p.L) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hT : 10 ^ p.L ≤ (p.N + 1) ^ 5 := by omega
  have hN1 : p.N + 1 ≤ (p.N + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
  have hL1 : p.L + 1 ≤ (p.L + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h11 : 11 ^ p.L ≤ (10 ^ p.L) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) _
  exact ⟨by omega, hT, (Nat.pow_le_pow_left (by norm_num) _).trans hT,
    (hL1.trans (succ_sq_le_ten_pow p.L)).trans hT,
    (Nat.pow_le_pow_right (by norm_num) hmL).trans hT,
    (card_boxes_le _ _ _).trans (by omega), (numBands_le p.L p.m p.N hmL).trans hN1, by omega⟩

/-- The length of the block is at most `222 B⁴`. -/
theorem top_sub_le_pow {p : Sec2.Par} {t B : ℕ} (h : Hyp30 p t) (hB : Light.Sec4.Below p t B) (b0 : ℕ) :
    Light.Sec4.top p t b0 - b0 ≤ 222 * B ^ 4 := by
  have hmL : p.m ≤ p.L := by have := h.L_ge; omega
  have hL1 : 1 ≤ p.L := by have := h.L_ge; have := h.m_pos; omega
  obtain ⟨hone, hT, -, hL, -, hbx, hnB, hN⟩ := hB
  have hshared := sharedEnd_sub_le p b0 hL1 hmL
  rw [top_sub_eq]
  generalize p.sharedEnd b0 - b0 = E at *
  generalize (boxes p.L p.m t).card = bx at *
  generalize p.nB = nB at *
  generalize 10 ^ p.L = T at *
  -- each product of two of the quantities is at most B², and so on
  have hNL : p.N * (p.L + 1) ≤ B * B := Nat.mul_le_mul hN hL
  have hnT : nB * T ≤ B * B := Nat.mul_le_mul hnB hT
  have hnn : nB * nB ≤ B * B := Nat.mul_le_mul hnB hnB
  have hLb : p.L * bx ≤ B * B := Nat.mul_le_mul (by omega) hbx
  have htries : nB * nB * (11 * (1 + p.L * bx)) ≤ B * B * (11 * (B + B * B)) :=
    Nat.mul_le_mul hnn (by omega)
  -- and every power of B up to the fourth is at most B⁴
  have hpow : ∀ j ≤ 4, B ^ j ≤ B ^ 4 := fun j hj => Nat.pow_le_pow_right hone hj
  have hB0 := hpow 0 (by norm_num)
  have hB1 := hpow 1 (by norm_num)
  have hB2 := hpow 2 (by norm_num)
  have hB3 := hpow 3 (by norm_num)
  rw [pow_zero] at hB0
  rw [pow_one] at hB1
  rw [show B ^ 2 = B * B by ring] at hB2
  rw [show B ^ 3 = B * B * B by ring] at hB3
  rw [show B * B * (11 * (B + B * B)) = 11 * (B * B * B) + 11 * B ^ 4 by ring] at htries
  omega

end Light.Sec4
end
end

section
namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam

namespace List

theorem sharpTail_sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := rfl

end List

private theorem sharpTail_abs_getD_le {xs : List ℤ} {U : ℕ}
    (h : ∀ z ∈ xs, |z| ≤ (U : ℤ)) (hU : 0 ≤ (U : ℤ)) (i : ℕ) :
    |xs.getD i 0| ≤ (U : ℤ) := by
  by_cases hi : i < xs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    simpa using hU

private theorem sharpTail_ends_mono {lim : Limits} {P : Program} {d : ℕ}
    {body : Stmt} {σ : State} {T T' : ℕ} {R R' : State → Prop}
    (h : Ends lim P d body σ T R) (hT : T ≤ T') (hR : ∀ σ', R σ' → R' σ') :
    Ends lim P d body σ T' R' := by
  rcases h with ⟨σ', c, hrun, hc, hpost⟩
  exact ⟨σ', c, hrun, hc.trans hT, hR σ' hpost⟩

/-- The matrices reconstructed from the row-major arrays in a native `ThinInst`. -/
theorem sharpTail_matAt_thinMX {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ}
    (h : x.Pre μ fr) : MatAt μ x.x (thinMX x) := by
  intro i j
  have hlt : (i : ℕ) * x.D + j < x.X.length := by
    rw [h.lenX]
    have hi := Nat.mul_le_mul_right x.D (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at hi
    have hj := j.isLt
    omega
  rw [Nat.add_assoc, h.segX.getD hlt 0]
  rfl

theorem sharpTail_matAt_thinMY {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ}
    (h : x.Pre μ fr) : MatAt μ x.y (thinMY x) := by
  intro i j
  have hlt : (i : ℕ) * x.N + j < x.Y.length := by
    rw [h.lenY]
    have hi := Nat.mul_le_mul_right x.N (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at hi
    have hj := j.isLt
    omega
  rw [Nat.add_assoc, h.segY.getD hlt 0]
  rfl

theorem sharpTail_entryN_thin (x : ThinInst) {I J : ℕ} (hI : I < x.N) (hJ : J < x.N) :
    entryN (thinMX x) (thinMY x) I J = thinEntry x.N x.D x.X x.Y I J := by
  rw [entryN, dif_pos ⟨hI, hJ⟩, Matrix.mul_apply, thinEntry, List.sharpTail_sum_map_range,
    Finset.sum_range]
  rfl

theorem sharpTail_map_entryN_thin {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ}
    (h : x.Pre μ fr) :
    (x.WI.zip x.WJ).map (fun q => entryN (thinMX x) (thinMY x) q.1 q.2) =
      thinOut x.N x.D x.X x.Y x.WI x.WJ :=
  List.map_congr_left fun _ hq =>
    sharpTail_entryN_thin x (h.ltWI _ (List.of_mem_zip hq).1) (h.ltWJ _ (List.of_mem_zip hq).2)

/-- Generic bridge from the actual `OfflineSpec32P` to the native light-language task.  It keeps
the program parameters `G` arbitrary; the caller supplies exactly the `Lim31` and depth facts that
the offline procedure requires. -/
theorem offline32_meets_thinTask_of_Lim31 {lim : Limits} {P : Program} {c d : ℕ}
    {G : RatParams} (task : OfflineSpec32P lim P c G) {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hlim : Lim31 lim G x.N x.D fr (x.U : ℤ))
    (hdepth : (d + 1) + (G.L (logFour x.D) + 8) ≤ lim.depth) :
    Meets lim P Proc.offline32 (d + 1)
      [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
      (tOffline32P c G x.N x.D x.w) (fun r μ' => thinTask.Post x μ fr r μ') := by
  have hU0 : (0 : ℤ) ≤ (x.U : ℤ) := by positivity
  have hspec := task x.N x.D x.x x.y x.wi x.wj x.out fr (thinMX x) (thinMY x) (x.U : ℤ)
    (x.U : ℤ) μ x.WI x.WJ
    { one_le_D := hpre.D_pos, one_le_N := hpre.N_pos, lim := hlim
      absX := fun i j => sharpTail_abs_getD_le hpre.leX hU0 _
      absY := fun i j => sharpTail_abs_getD_le hpre.leY hU0 _
      belowX := hpre.belowX, belowY := hpre.belowY }
    { matX := sharpTail_matAt_thinMX hpre, matY := sharpTail_matAt_thinMY hpre
      rows := hpre.segWI, cols := hpre.segWJ
      length_eq := by rw [hpre.lenWI, hpre.lenWJ]
      rows_lt := hpre.ltWI, cols_lt := hpre.ltWJ
      rows_le := by rw [hpre.lenWI]; exact hpre.belowWI
      cols_le := by rw [hpre.lenWI]; exact hpre.belowWJ
      out_le := by rw [hpre.lenWI]; exact hpre.belowOut
      out_matX := by rw [hpre.lenWI]; exact hpre.apartX
      out_matY := by rw [hpre.lenWI]; exact hpre.apartY
      out_rows := by rw [hpre.lenWI]; exact hpre.apartWI
      out_cols := by rw [hpre.lenWI]; exact hpre.apartWJ }
  rw [hpre.lenWI, sharpTail_map_entryN_thin hpre] at hspec
  rcases hspec (d + 1) hdepth with ⟨body, hbody, hends⟩
  refine ⟨body, hbody, sharpTail_ends_mono hends le_rfl ?_⟩
  intro σ hσ
  exact ⟨hσ.1, fun a ha => hσ.2 a ha.1 ha.2⟩

/-- The actual rational-parameter program has the native offline-task specification for every
parameter record `G`. -/
theorem program31P_offline32_meets_thinTask (G : RatParams) {lim : Limits} {x : ThinInst}
    {μ : ℕ → ℤ} {fr d : ℕ} (hpre : x.Pre μ fr)
    (hlim : Lim31 lim G x.N x.D fr (x.U : ℤ))
    (hdepth : (d + 1) + (G.L (logFour x.D) + 8) ≤ lim.depth) :
    Meets lim (program31P G) Proc.offline32 (d + 1)
      [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
      (tOffline32P cShared30 G x.N x.D x.w) (fun r μ' => thinTask.Post x μ fr r μ') := by
  exact offline32_meets_thinTask_of_Lim31
    (ThreeSumSharpTail.pruned_program_correct G lim) hpre hlim hdepth

/-! ## Generic need and limits -/

private noncomputable def sharpTailWordNeed (G : RatParams) (N D U : ℕ) : ℕ :=
  1000 + 400 * D + N * D + D * (U * U) + ((N + 1) ^ 5) ^ 3 * (U * U)
    + 7 * ((N + 1) ^ 5 * U) + 10 * (N + 1) ^ 5 + N ^ 5 * D + N ^ 5
    + extraWord31 G D

/-- Polynomially shaped need for the actual routine; all parameter-specific word/depth terms are
kept explicit in `G`. -/
noncomputable def sharpTailNeed (G : RatParams) : List ℕ → Need
  | [N, D, _, U] =>
      ⟨sharpTailWordNeed G N D U,
        4 + N + 8 * (N * D) + 222 * ((N + 1) ^ 5) ^ 4,
        4 * G.a * D + G.b + 10⟩
  | _ => ⟨0, 0, 0⟩

private def sharpTailPolyCoeff (G : RatParams) : ℕ :=
  1500 + 4 * (G.a + G.b + G.p + G.q + G.m₀)

private theorem sharpTail_polyCoeff_le (G : RatParams) :
    sharpTailPolyCoeff G ≤ 2 ^ (12 + G.a + G.b + G.p + G.q + G.m₀) := by
  let S := G.a + G.b + G.p + G.q + G.m₀
  have hs : S ≤ 2 ^ S := Nat.lt_two_pow_self.le
  have h1 : 1 ≤ 2 ^ S := Nat.one_le_two_pow
  have hsum : 12 + G.a + G.b + G.p + G.q + G.m₀ = 12 + S := by
    dsimp [S]
    omega
  have hcoeff : sharpTailPolyCoeff G ≤ 4096 * 2 ^ S := by
    change 1500 + 4 * S ≤ 4096 * 2 ^ S
    have hs4 := Nat.mul_le_mul_left 4 hs
    have h1500 := Nat.mul_le_mul_left 1500 h1
    omega
  have hpow :
      4096 * (2 ^ (G.a + G.b + G.p + G.q) * 2 ^ G.m₀) = 2 ^ (12 + S) := by
    rw [show 4096 = 2 ^ 12 by norm_num, ← pow_add, ← pow_add]
  calc
    sharpTailPolyCoeff G ≤ 4096 * 2 ^ S := hcoeff
    _ = 4096 * (2 ^ (G.a + G.b + G.p + G.q) * 2 ^ G.m₀) := by
      congr 1
      dsimp [S]
      rw [pow_add]
    _ = 2 ^ (12 + S) := hpow
    _ = 2 ^ (12 + G.a + G.b + G.p + G.q + G.m₀) := by rw [← hsum]

private theorem sharpTailNeed_poly (G : RatParams) : PolyNeedN (sharpTailNeed G) := by
  refine ⟨12 + G.a + G.b + G.p + G.q + G.m₀, 20, ?_⟩
  intro ps
  cases ps with
  | nil => simp [sharpTailNeed]
  | cons N ps =>
    cases ps with
    | nil => simp [sharpTailNeed]
    | cons D ps =>
      cases ps with
      | nil => simp [sharpTailNeed]
      | cons w ps =>
        cases ps with
        | nil => simp [sharpTailNeed]
        | cons U ps =>
          cases ps with
          | cons z zs => simp [sharpTailNeed]
          | nil =>
            generalize hQdef : ((N + 1) * (D + 1) * (w + 1) * (U + 1)) = Q
            let q20 := Q ^ 20
            have hQpos : 0 < Q := by rw [← hQdef]; positivity
            have hQ : 1 ≤ Q := by omega
            have hN1 : N + 1 ≤ Q := by
              rw [← hQdef]
              calc
                N + 1 ≤ (N + 1) * (D + 1) := Nat.le_mul_of_pos_right _ (by omega)
                _ ≤ ((N + 1) * (D + 1)) * (w + 1) := Nat.le_mul_of_pos_right _ (by omega)
                _ ≤ ((N + 1) * (D + 1) * (w + 1)) * (U + 1) :=
                  Nat.le_mul_of_pos_right _ (by omega)
            have hD1 : D + 1 ≤ Q := by
              rw [← hQdef]
              calc
                D + 1 ≤ (N + 1) * (D + 1) := Nat.le_mul_of_pos_left _ (by omega)
                _ ≤ ((N + 1) * (D + 1)) * (w + 1) := Nat.le_mul_of_pos_right _ (by omega)
                _ ≤ ((N + 1) * (D + 1) * (w + 1)) * (U + 1) :=
                  Nat.le_mul_of_pos_right _ (by omega)
            have hw1 : w + 1 ≤ Q := by
              rw [← hQdef]
              calc
                w + 1 ≤ ((N + 1) * (D + 1)) * (w + 1) :=
                  Nat.le_mul_of_pos_left _ (by positivity)
                _ ≤ ((N + 1) * (D + 1) * (w + 1)) * (U + 1) :=
                  Nat.le_mul_of_pos_right _ (by positivity)
            have hU1 : U + 1 ≤ Q := by
              rw [← hQdef]
              exact Nat.le_mul_of_pos_left _ (by positivity)
            have hN : N ≤ Q := by omega
            have hD : D ≤ Q := by omega
            have hU : U ≤ Q := by omega
            have hQ20 : 1 ≤ q20 := by
              dsimp [q20]
              exact Nat.one_le_pow 20 Q hQpos
            have hN20 : N ^ 20 ≤ q20 := by
              dsimp [q20]
              exact Nat.pow_le_pow_left hN 20
            have hD20 : D ^ 20 ≤ q20 := by
              dsimp [q20]
              exact Nat.pow_le_pow_left hD 20
            have hU20 : U ^ 20 ≤ q20 := by
              dsimp [q20]
              exact Nat.pow_le_pow_left hU 20
            have hND : N * D ≤ q20 := by
              calc
                N * D ≤ Q * Q := Nat.mul_le_mul hN hD
                _ = Q ^ 2 := by ring
                _ ≤ q20 := Nat.pow_le_pow_right hQpos (show 2 ≤ 20 by omega)
            have hDUU : D * (U * U) ≤ q20 := by
              calc
                D * (U * U) ≤ Q * (Q * Q) := Nat.mul_le_mul hD (Nat.mul_le_mul hU hU)
                _ = Q ^ 3 := by ring
                _ ≤ q20 := Nat.pow_le_pow_right hQpos (show 3 ≤ 20 by omega)
            have hBig : ((N + 1) ^ 5) ^ 3 * (U * U) ≤ q20 := by
              calc
                ((N + 1) ^ 5) ^ 3 * (U * U) ≤ Q ^ 15 * (Q * Q) := by
                  calc
                    _ = (N + 1) ^ 15 * (U * U) := by rw [← pow_mul]
                    _ ≤ Q ^ 15 * (Q * Q) :=
                      Nat.mul_le_mul (Nat.pow_le_pow_left hN1 15)
                        (Nat.mul_le_mul hU hU)
                _ = Q ^ 17 := by
                  rw [show 17 = 15 + 2 by omega, pow_add, pow_two]
                _ ≤ q20 := Nat.pow_le_pow_right hQpos (show 17 ≤ 20 by omega)
            have hBU : (N + 1) ^ 5 * U ≤ q20 := by
              calc
                (N + 1) ^ 5 * U ≤ Q ^ 5 * Q := by
                  exact Nat.mul_le_mul (Nat.pow_le_pow_left hN1 5) hU
                _ = Q ^ 6 := by ring
                _ ≤ q20 := Nat.pow_le_pow_right hQpos (show 6 ≤ 20 by omega)
            have hB : (N + 1) ^ 5 ≤ q20 := by
              calc
                (N + 1) ^ 5 ≤ Q ^ 5 := Nat.pow_le_pow_left hN1 5
                _ ≤ q20 := Nat.pow_le_pow_right hQpos (show 5 ≤ 20 by omega)
            have hB4 : ((N + 1) ^ 5) ^ 4 ≤ q20 := by
              calc
                ((N + 1) ^ 5) ^ 4 ≤ Q ^ 20 := by
                  calc
                    _ = (N + 1) ^ 20 := by rw [← pow_mul]
                    _ ≤ Q ^ 20 := Nat.pow_le_pow_left hN1 20
                _ = q20 := rfl
            have hN5D : N ^ 5 * D ≤ q20 := by
              calc
                N ^ 5 * D ≤ Q ^ 5 * Q := Nat.mul_le_mul (Nat.pow_le_pow_left hN 5) hD
                _ = Q ^ 6 := by rw [← pow_succ]
                _ ≤ q20 := Nat.pow_le_pow_right hQpos (show 6 ≤ 20 by omega)
            have hN5 : N ^ 5 ≤ q20 := by
              calc
                N ^ 5 ≤ Q ^ 5 := Nat.pow_le_pow_left hN 5
                _ ≤ q20 := Nat.pow_le_pow_right hQpos (show 5 ≤ 20 by omega)
            have hlog : logFour D ≤ 4 * D := by
              by_cases hDpos : 1 ≤ D
              · exact logFour_le_four_mul hDpos
              · have hzero : D = 0 := by omega
                simp [logFour, hzero]
            have hQpow_le : Q ≤ Q ^ 20 := by
              calc
                Q = Q ^ 1 := by simp
                _ ≤ Q ^ 20 := Nat.pow_le_pow_right hQ (by omega)
            have hDq : D ≤ q20 := hD.trans (by simpa [q20] using hQpow_le)
            have hNq : N ≤ q20 := hN.trans (by simpa [q20] using hQpow_le)
            have hQq : Q ≤ q20 := by simpa [q20] using hQpow_le
            have hqpos20 : 0 < q20 := by omega
            have hAq : G.a * logFour D ≤ 4 * G.a * q20 := by
              calc
                G.a * logFour D ≤ G.a * (4 * D) := Nat.mul_le_mul_left _ hlog
                _ = 4 * G.a * D := by ring
                _ ≤ 4 * G.a * q20 := Nat.mul_le_mul_left _ hDq
            have hPq : G.p * logFour D ≤ 4 * G.p * q20 := by
              calc
                G.p * logFour D ≤ G.p * (4 * D) := Nat.mul_le_mul_left _ hlog
                _ = 4 * G.p * D := by ring
                _ ≤ 4 * G.p * q20 := Nat.mul_le_mul_left _ hDq
            have hword : sharpTailWordNeed G N D U ≤
                (1000 + 400 + 1 + 1 + 1 + 7 + 10 + 1 + 1 + 4 * G.a + G.b +
                  4 * G.p + G.q + G.m₀) * q20 := by
              generalize hq20 : q20 = z at *
              dsimp [sharpTailWordNeed, extraWord31]
              have hz1 : 1 ≤ z := by omega
              have h1000 : 1000 ≤ 1000 * z := Nat.mul_le_mul_left 1000 hz1
              have h400D : 400 * D ≤ 400 * z := Nat.mul_le_mul_left 400 hDq
              have hN' : N ≤ z := hNq
              have hD' : D ≤ z := hDq
              have hGb : G.b ≤ G.b * z := Nat.le_mul_of_pos_right G.b hqpos20
              have hGq : G.q ≤ G.q * z := Nat.le_mul_of_pos_right G.q hqpos20
              have hGm : G.m₀ ≤ G.m₀ * z := Nat.le_mul_of_pos_right G.m₀ hqpos20
              have hdist :
                  (1000 + 400 + 1 + 1 + 1 + 7 + 10 + 1 + 1 + 4 * G.a + G.b +
                    4 * G.p + G.q + G.m₀) * z =
                  1000 * z + 400 * z + z + z + z + 7 * z + 10 * z + z + z +
                    4 * G.a * z + G.b * z + 4 * G.p * z + G.q * z + G.m₀ * z := by ring
              rw [hdist]
              omega
            have hcell : 4 + N + 8 * (N * D) + 222 * ((N + 1) ^ 5) ^ 4 ≤
                (4 + 1 + 8 + 222) * q20 := by
              generalize hq20 : q20 = z at *
              have hz1 : 1 ≤ z := by omega
              have h4 : 4 ≤ 4 * z := Nat.mul_le_mul_left 4 hz1
              have hN' : N ≤ z := hNq
              have hND' : 8 * (N * D) ≤ 8 * z := Nat.mul_le_mul_left 8 hND
              have hB4' : 222 * ((N + 1) ^ 5) ^ 4 ≤ 222 * z := Nat.mul_le_mul_left 222 hB4
              have hdist : (4 + 1 + 8 + 222) * z = 4 * z + z + 8 * z + 222 * z := by ring
              rw [hdist]
              omega
            have hdepth : 4 * G.a * D + G.b + 10 ≤
                (4 * G.a + G.b + 10) * q20 := by
              have hDq' : D ≤ q20 := hDq
              generalize hq20 : q20 = z at *
              have hz1 : 1 ≤ z := by omega
              have hGAD : 4 * G.a * D ≤ 4 * G.a * z := Nat.mul_le_mul_left (4 * G.a) hDq'
              have hGb : G.b ≤ G.b * z := Nat.le_mul_of_pos_right G.b (by omega)
              have h10 : 10 ≤ 10 * z := Nat.mul_le_mul_left 10 hz1
              have hdist : (4 * G.a + G.b + 10) * z = 4 * G.a * z + G.b * z + 10 * z := by ring
              rw [hdist]
              omega
            have hcoeffWord :
                1000 + 400 + 1 + 1 + 1 + 7 + 10 + 1 + 1 + 4 * G.a + G.b +
                    4 * G.p + G.q + G.m₀ ≤ sharpTailPolyCoeff G := by
              dsimp [sharpTailPolyCoeff]
              omega
            have hcoeffCell : 4 + 1 + 8 + 222 ≤ sharpTailPolyCoeff G := by
              dsimp [sharpTailPolyCoeff]
              omega
            have hcoeffDepth : 4 * G.a + G.b + 10 ≤ sharpTailPolyCoeff G := by
              dsimp [sharpTailPolyCoeff]
              omega
            have hmulWord := Nat.mul_le_mul_right q20 hcoeffWord
            have hmulCell := Nat.mul_le_mul_right q20 hcoeffCell
            have hmulDepth := Nat.mul_le_mul_right q20 hcoeffDepth
            have hpolyCoeff := sharpTail_polyCoeff_le G
            have hpoly : sharpTailPolyCoeff G * q20 ≤
                2 ^ (12 + G.a + G.b + G.p + G.q + G.m₀) * q20 :=
              Nat.mul_le_mul_right q20 hpolyCoeff
            have hQpow : q20 = ((N + 1) * (D + 1) * (w + 1) * (U + 1)) ^ 20 := by
              dsimp [q20]
              rw [← hQdef]
            have hQpow' : q20 = ((N + 1) * ((D + 1) * ((w + 1) * (U + 1)))) ^ 20 := by
              rw [hQpow]
              congr 1
              ring
            simp only [sharpTailNeed, polyBound, List.map_cons, List.map_nil,
              List.prod_cons, List.prod_nil, mul_one]
            rw [← hQpow']
            constructor
            · exact hword.trans (hmulWord.trans hpoly)
            · constructor
              · exact hcell.trans (hmulCell.trans hpoly)
              · exact hdepth.trans (hmulDepth.trans hpoly)

private theorem sharpTail_fits_of_need {G : RatParams} {lim : Limits} {N D w U fr d : ℕ}
    (ok : (sharpTailNeed G [N, D, w, U]).Ok lim fr d) {n : ℕ}
    (hn : n ≤ sharpTailWordNeed G N D U) : (n : ℤ) ≤ lim.word := by
  have hn' : (n : ℤ) ≤ (sharpTailWordNeed G N D U : ℤ) := by exact_mod_cast hn
  exact hn'.trans ok.word

private theorem sharpTail_top_le_of_need {G : RatParams} {lim : Limits} {N D w U fr d : ℕ}
    (hD : 1 ≤ D) (H : G.Hyp N D)
    (ok : (sharpTailNeed G [N, D, w, U]).Ok lim fr d) :
    top (parOf G N D) (switchOf31 G D) (blockAt N D fr) ≤ lim.space := by
  have hcells : fr + (4 + N + 8 * (N * D) + 222 * ((N + 1) ^ 5) ^ 4) ≤ lim.space := ok.cells
  have hblock : top (parOf G N D) (switchOf31 G D) (blockAt N D fr) - blockAt N D fr
      ≤ 222 * ((N + 1) ^ 5) ^ 4 := top_sub_le_pow H (Light.Sec4.below H) _
  have hpad : N * ThreeSumApsp.D (logFour D) ≤ 4 * (N * D) :=
    (Nat.mul_le_mul_left N (Nat.pow_clog_le_mul (b := 4) (by norm_num) hD)).trans_eq (by ring)
  have hbase : blockAt N D fr = fr + 3 + N * ThreeSumApsp.D (logFour D)
      + N * ThreeSumApsp.D (logFour D) := rfl
  have hle := (G.blockAt_lt_blockEnd N D fr).le
  omega

private theorem sharpTail_lim30_of_below {G : RatParams} {lim : Limits} {N D U fr B : ℕ}
    (hB : Light.Sec4.Below (parOf G N D) (switchOf31 G D) B) (std : Std lim)
    (hspace : top (parOf G N D) (switchOf31 G D) (blockAt N D fr) ≤ lim.space)
    (fits : ∀ n : ℕ, n ≤ B ^ 3 * (U * U) + 7 * (B * U) + 10 * B →
      (n : ℤ) ≤ lim.word) :
    Lim30 lim (parOf G N D) (switchOf31 G D) (blockAt N D fr) (U : ℤ) := by
  have hvalue : 10 ^ (parOf G N D).m *
      ((7 ^ (parOf G N D).L * U) * (7 ^ (parOf G N D).L * U)) ≤ B ^ 3 * (U * U) := by
    calc
      _ ≤ B * ((B * U) * (B * U)) := by
        exact Nat.mul_le_mul hB.tenm
          (Nat.mul_le_mul (Nat.mul_le_mul_right U hB.S7)
            (Nat.mul_le_mul_right U hB.S7))
      _ = B ^ 3 * (U * U) := by ring
  have henc : 7 ^ ((parOf G N D).L + 1) * U ≤ 7 * (B * U) := by
    calc
      7 ^ ((parOf G N D).L + 1) * U = 7 * (7 ^ (parOf G N D).L * U) := by ring
      _ ≤ 7 * (B * U) := by gcongr; exact hB.S7
  have hpow : 10 ^ ((parOf G N D).L + 1) ≤ 10 * B := by
    calc
      10 ^ ((parOf G N D).L + 1) = 10 * 10 ^ (parOf G N D).L := by ring
      _ ≤ 10 * B := by gcongr; exact hB.T
  exact {
    std := std
    space := hspace
    value := by exact_mod_cast fits _ (hvalue.trans (by omega))
    enc := by exact_mod_cast fits _ (henc.trans (by omega))
    pow := fits _ (hpow.trans (by omega)) }

/-- Arbitrary-parameter construction of all limit facts required by the true routine. -/
theorem sharpTail_lim31_of_need {G : RatParams} {lim : Limits} {N D w U fr d : ℕ}
    {C tp tq : ℝ} (hD : 1 ≤ D) (hCost : CostsWithinP G C N D tp tq)
    (ok : (sharpTailNeed G [N, D, w, U]).Ok lim fr d) :
    Lim31 lim G N D fr (U : ℤ) := by
  have fits {n : ℕ} := sharpTail_fits_of_need ok (n := n)
  have h4 : 4 ^ logFour D ≤ 4 * D := Nat.pow_clog_le_mul (b := 4) (by norm_num) hD
  have hm4 : logFour D ≤ 4 * D := logFour_le_four_mul hD
  have h100 : (100 : ℤ) ≤ lim.word := by
    exact_mod_cast fits (n := 100) (by dsimp [sharpTailWordNeed]; omega)
  have std : Std lim := ⟨ok.space, h100⟩
  have large (hm : G.m₀ ≤ logFour D) :
      Lim30 lim (parOf G N D) (switchOf31 G D) (blockAt N D fr) (U : ℤ) := by
    have H : G.Hyp N D := (hCost.above hm).1
    exact sharpTail_lim30_of_below (G := G) (B := (N + 1) ^ 5)
      (Light.Sec4.below H) std (sharpTail_top_le_of_need hD H ok)
      (fun n hn => fits (hn.trans (by dsimp [sharpTailWordNeed, extraWord31]; omega)))
  refine { std := std, space := ?_, pow := ?_, mword := ?_, m0word := ?_, ip := ?_, large := large }
  · dsimp [structEnd]
    split_ifs with h
    · have hc : fr + (4 + N + 8 * (N * D) + 222 * ((N + 1) ^ 5) ^ 4) ≤ lim.space := by
        simpa [sharpTailNeed] using ok.cells
      have h3 : fr + 3 ≤ fr + (4 + N + 8 * (N * D) + 222 * ((N + 1) ^ 5) ^ 4) := by omega
      exact h3.trans hc
    · exact (large (not_lt.mp h)).space
  · exact_mod_cast fits (by dsimp [sharpTailWordNeed, extraWord31]; omega)
  · exact_mod_cast fits (by dsimp [sharpTailWordNeed, extraWord31]; omega)
  · exact_mod_cast fits (by dsimp [sharpTailWordNeed, extraWord31]; omega)
  · exact_mod_cast fits (by dsimp [sharpTailWordNeed, extraWord31]; omega)

theorem sharpTail_depth_of_need {G : RatParams} {lim : Limits} {N D w U fr d : ℕ}
    (hD : 1 ≤ D) (ok : (sharpTailNeed G [N, D, w, U]).Ok lim fr d) :
    (d + 1) + (G.L (logFour D) + 8) ≤ lim.depth := by
  have h := ok.depth
  change d + (4 * G.a * D + G.b + 10) ≤ lim.depth at h
  have hlog := logFour_le_four_mul hD
  have hL : G.L (logFour D) ≤ G.a * logFour D + G.b := by
    unfold RatParams.L
    calc
      (G.a * logFour D + G.b - 1) / G.b ≤ G.a * logFour D + G.b - 1 := Nat.div_le_self _ _
      _ ≤ G.a * logFour D + G.b := by omega
  have hGa : G.a * logFour D ≤ 4 * G.a * D := by
    calc
      G.a * logFour D ≤ G.a * (4 * D) := Nat.mul_le_mul_left G.a hlog
      _ = 4 * G.a * D := by ring
  have hL' : G.L (logFour D) ≤ 4 * G.a * D + G.b := by omega
  omega

#print axioms program31P_offline32_meets_thinTask
#print axioms sharpTail_lim31_of_need

end Light.Sec4
end

/-- Generic native-resource wrapper for the actual parameterized program. -/
theorem solution (G : Light.Sec4.RatParams) :
    ∃ need : List ℕ → Light.Need, Light.PolyNeedN need ∧
      ∀ (R : Light.Program) (lim : Light.Limits) (fr d : ℕ)
        (x : Light.ThinInst) (μ : ℕ → ℤ) (C tp tq : ℝ),
        0 ≤ C → Light.lopCountTask.Pre x μ fr →
        Light.Sec4.CostsWithinP G C x.N x.D tp tq →
        (need [x.N, x.D, x.w, x.U]).Ok lim fr d →
        Light.Meets lim (Light.Sec4.program31P G ++ R) Light.Sec4.Proc.offline32 (d + 1)
          [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
          (Light.Sec4.tOffline32P Light.Sec4.cShared30 G x.N x.D x.w)
          (fun r μ' => Light.lopCountTask.Post x μ fr r μ') := by
  refine ⟨Light.Sec4.sharpTailNeed G, Light.Sec4.sharpTailNeed_poly G, ?_⟩
  intro R lim fr d x μ C tp tq hC hPre hCost hok
  have hlim := Light.Sec4.sharpTail_lim31_of_need hCost.one_le_D hCost hok
  have hdepth := Light.Sec4.sharpTail_depth_of_need hCost.one_le_D hok
  exact (Light.Sec4.program31P_offline32_meets_thinTask G hPre.1 hlim hdepth).append R

#print axioms solution
