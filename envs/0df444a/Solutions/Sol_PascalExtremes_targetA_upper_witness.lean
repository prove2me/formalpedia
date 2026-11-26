-- Prove2me | solution 1 for PascalExtremes.targetA_upper_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:57:20.772831+00:00
-- url     : https://prove2.me/submissions/e002fadb-ab46-49a0-985a-42b9002eb210

module
public import Definitions.Def_PascalExtremes_Basic
public import Definitions.Def_PascalExtremes_Powers
public import Definitions.Def_PascalExtremes_CarryBounds
public import Mathlib.Tactic
public import Definitions.Def_PascalExtremes_TargetA
public import Theorems.Thm_PascalExtremes_lt_pow_rP
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
public import Theorems.Thm_PascalExtremes_padicVal_choose_le_of_common_suffix
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff


section
@[expose] public section
namespace PascalExtremes
private lemma mul_lt_pow_succ_rP
    {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    p * m < p ^ (rP p m + 1) := by
  have hmPow : m < p ^ rP p m := lt_pow_rP hp.one_lt
  have hmul := (Nat.mul_lt_mul_left hp.pos).2 hmPow
  simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
end PascalExtremes
end
end

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p m N : ℕ} (hp : p.Prime) (hm2 : 2 ≤ m) (hpm : ¬ p ∣ m)
    (hrow : AdmissibleRow m N) :
    ∃ k, Admissible N m k ∧
      padicValNat p (N.choose k) ≤ rP p m := by
  have hm : 0 < m := by omega
  rcases hrow.2 with ⟨q, hN⟩
  have hmq : m < m * q := by
    simpa [hN] using hrow.1
  have hq2 : 2 ≤ q := by
    by_contra h
    have hqLt2 : q < 2 := by omega
    interval_cases q <;> simp_all
  let t := Nat.log p q
  let P := p ^ t
  let lam := q / P
  let b := q % P
  have hPpos : 0 < P := by
    dsimp [P]
    exact pow_pos hp.pos t
  have hPleq : P ≤ q := by
    dsimp [P, t]
    exact Nat.pow_log_le_self p (by omega)
  have hqLt : q < P * p := by
    dsimp [P, t]
    simpa [pow_succ, Nat.mul_comm] using
      (Nat.lt_pow_succ_log_self hp.one_lt q)
  have hbLt : b < P := by
    dsimp [b]
    exact Nat.mod_lt _ hPpos
  have hqDecomp : q = b + P * lam := by
    dsimp [b, P, lam]
    exact (Nat.mod_add_div q (p ^ t)).symm
  have hlamPos : 0 < lam := by
    by_contra h
    have hlam0 : lam = 0 := Nat.eq_zero_of_not_pos h
    rw [hlam0, mul_zero, add_zero] at hqDecomp
    omega
  have hlamLt : lam < p := by
    by_contra h
    have hpLam : p ≤ lam := Nat.le_of_not_gt h
    have hmul : P * p ≤ P * lam := Nat.mul_le_mul_left P hpLam
    have hPle : P * lam ≤ q := by omega
    exact (Nat.not_le_of_gt hqLt) (hmul.trans hPle)
  have hpmul : p * m < p ^ (rP p m + 1) :=
    mul_lt_pow_succ_rP hp hm
  by_cases hb0 : b = 0
  · by_cases hlam1 : lam = 1
    · have hqP : q = P := by
        rw [hb0, hlam1, mul_one, zero_add] at hqDecomp
        exact hqDecomp
      have hqPow : q = p ^ t := by simpa [P] using hqP
      have htpos : 0 < t := by
        by_contra ht
        have ht0 : t = 0 := Nat.eq_zero_of_not_pos ht
        rw [ht0, pow_zero] at hqPow
        omega
      let t' := t - 1
      let k := m * p ^ t'
      have htEq : t = t' + 1 := by
        dsimp [t']
        omega
      have hqShift : q = p ^ t' * p := by
        rw [hqPow, htEq, pow_succ]
      have hkAdm : Admissible N m k := by
        refine ⟨?_, ?_, ?_⟩
        · exact Nat.mul_pos hm (pow_pos hp.pos _)
        · rw [hN, hqShift]
          dsimp [k]
          have hpow : 0 < p ^ t' := pow_pos hp.pos _
          have hmp : m < m * p := by
            nlinarith [hp.two_le]
          nlinarith
        · exact dvd_mul_right m _
      refine ⟨k, hkAdm, ?_⟩
      have hNform : N = 0 + p ^ t' * (m * p) := by
        rw [hN, hqShift]
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      have hkform : k = 0 + p ^ t' * m := by
        simp [k, Nat.mul_comm]
      exact padicVal_choose_le_of_common_suffix
        hp (lt_trans hm hrow.1) hkAdm.2.1.le
        (by exact pow_pos hp.pos _)
        hNform hkform (by nlinarith [hp.two_le])
        (by simpa [Nat.mul_comm] using hpmul)
    · have hlam2 : 2 ≤ lam := by omega
      let k := m * P
      have hkAdm : Admissible N m k := by
        refine ⟨Nat.mul_pos hm hPpos, ?_, dvd_mul_right m P⟩
        rw [hN, hqDecomp, hb0]
        dsimp [k]
        have hPm : 0 < P * m := Nat.mul_pos hPpos hm
        have hmlt : m < m * lam := by nlinarith
        nlinarith
      refine ⟨k, hkAdm, ?_⟩
      have hNform : N = 0 + P * (m * lam) := by
        rw [hN, hqDecomp, hb0]
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      have hkform : k = 0 + P * m := by
        simp [k, Nat.mul_comm]
      have hs : m * lam < p ^ (rP p m + 1) := by
        have hle : m * lam ≤ m * (p - 1) :=
          Nat.mul_le_mul_left m (by omega)
        have hpPred : p - 1 < p := by omega
        have hlt0 : m * (p - 1) < m * p :=
          (Nat.mul_lt_mul_left hm).2 hpPred
        have hlt : m * (p - 1) < p * m := by
          simpa [Nat.mul_comm] using hlt0
        exact (hle.trans_lt hlt).trans hpmul
      exact padicVal_choose_le_of_common_suffix
        hp (lt_trans hm hrow.1) hkAdm.2.1.le
        (by exact hPpos)
        hNform hkform (by nlinarith) hs
  · have hbPos : 0 < b := Nat.pos_of_ne_zero hb0
    let k := m * b
    let u := (m * b) % P
    let X := (m * b) / P
    have hmbDecomp : m * b = u + P * X := by
      dsimp [u, X]
      exact (Nat.mod_add_div (m * b) P).symm
    have huLt : u < P := by
      dsimp [u]
      exact Nat.mod_lt _ hPpos
    have hXLt : X < m := by
      dsimp [X]
      rw [Nat.div_lt_iff_lt_mul hPpos]
      exact (Nat.mul_lt_mul_left hm).2 hbLt
    have hkAdm : Admissible N m k := by
      refine ⟨Nat.mul_pos hm hbPos, ?_, dvd_mul_right m b⟩
      rw [hN]
      dsimp [k]
      have hbq : b < q := by
        rw [hqDecomp]
        have hPLamPos : 0 < P * lam := Nat.mul_pos hPpos hlamPos
        omega
      exact (Nat.mul_lt_mul_left hm).2 hbq
    refine ⟨k, hkAdm, ?_⟩
    have hNform : N = u + P * (X + m * lam) := by
      rw [hN, hqDecomp]
      calc
        m * (b + P * lam) = m * b + P * (m * lam) := by ring
        _ = (u + P * X) + P * (m * lam) := by rw [hmbDecomp]
        _ = u + P * (X + m * lam) := by ring
    have hkform : k = u + P * X := by
      dsimp [k]
      exact hmbDecomp
    have hsltPm : X + m * lam < p * m := by
      have hlamLe : lam ≤ p - 1 := by omega
      have hmulLe : m * lam ≤ m * (p - 1) :=
        Nat.mul_le_mul_left m hlamLe
      calc
        X + m * lam < m + m * lam := Nat.add_lt_add_right hXLt _
        _ ≤ m + m * (p - 1) := Nat.add_le_add_left hmulLe _
        _ = m * p := by
          calc
            m + m * (p - 1) = m * 1 + m * (p - 1) := by simp
            _ = m * (1 + (p - 1)) := (Nat.mul_add _ _ _).symm
            _ = m * p := by
              congr 1
              omega
        _ = p * m := Nat.mul_comm _ _
    have hs : X + m * lam < p ^ (rP p m + 1) :=
      hsltPm.trans hpmul
    exact padicVal_choose_le_of_common_suffix
      hp (lt_trans hm hrow.1) hkAdm.2.1.le
      huLt hNform hkform (Nat.le_add_right _ _) hs
end PascalExtremes
