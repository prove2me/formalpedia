-- Prove2me | solution 1 for PascalExtremes.targetB_lower_multiplier_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:04:15.38837+00:00
-- url     : https://prove2.me/submissions/c9c4fe97-e6f8-400a-9ada-6a0ad05c42a4

module
public import Definitions.Def_PascalExtremes_TargetB
public import Definitions.Def_PascalExtremes_Scaling
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetBMinimality
public import Theorems.Thm_PascalExtremes_targetB_pure_power_witness_le
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
public import Theorems.Thm_PascalExtremes_not_carryAt_iff_mod_pow_le
public import Theorems.Thm_PascalExtremes_not_p_dvd_pow_add_one
public import Theorems.Thm_PascalExtremes_padicVal_choose_eq_carryCount
public import Theorems.Thm_PascalExtremes_padicVal_choose_le_of_common_suffix
public import Theorems.Thm_PascalExtremes_q0_lt_pow_two_a
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff


section
@[expose] public section
namespace PascalExtremes
private theorem targetB_fallback_choose_le
    {p a t q h : ℕ} (hp : p.Prime) (ha : 2 ≤ a)
    (ht0 : a ≤ t) (ht1 : t ≤ 2 * a - 2)
    (hhpos : 0 < h) (hhsmall : h < p ^ (a - 1))
    (hqh : q + h = p ^ (t + 1))
    (hmh : (p ^ a + 1) * h < p ^ (t + 1)) :
    padicValNat p
      (((p ^ a + 1) * q).choose
        ((p ^ a + 1) * p ^ (a - 1))) ≤ a := by
  letI : Fact p.Prime := ⟨hp⟩
  let Q := p ^ a
  let A := p ^ (a - 1)
  let U := p ^ (t + 1)
  let R := U - (Q + 1) * h
  let L := t + a + 1
  let N := (Q + 1) * q
  let k := (Q + 1) * A
  have hApos : 0 < A := by
    dsimp [A]
    exact pow_pos hp.pos _
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact pow_pos hp.pos _
  have hmpos : 0 < Q + 1 := by omega
  have hQA : Q = A * p := by
    calc
      Q = p ^ a := rfl
      _ = p ^ ((a - 1) + 1) := by congr 1 <;> omega
      _ = p ^ (a - 1) * p := pow_succ p (a - 1)
      _ = A * p := rfl
  have htwoA : 2 * A ≤ Q := by
    rw [hQA]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left A hp.two_le
  have hAltQ : A < Q := by
    dsimp [A, Q]
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hAlePt : A ≤ p ^ t := by
    dsimp [A]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  have hUform : U = p ^ t * p := by
    dsimp [U]
    rw [pow_succ]
  have htwoPtU : 2 * p ^ t ≤ U := by
    rw [hUform]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (p ^ t) hp.two_le
  have hhPt : h < p ^ t := hhsmall.trans_le hAlePt
  have hptq : p ^ t < q := by
    have hqh' : q + h = U := by simpa [U] using hqh
    omega
  have hAq : A < q := hAlePt.trans_lt hptq
  have hkn : k ≤ N := by
    dsimp [k, N]
    exact Nat.mul_le_mul_left (Q + 1) hAq.le
  have hmh' : (Q + 1) * h < U := by
    simpa [Q, U] using hmh
  have hRsum : (Q + 1) * h + R = U := by
    dsimp [R]
    exact Nat.add_sub_of_le hmh'.le
  have hRsum' : R + (Q + 1) * h = U := by
    simpa [Nat.add_comm] using hRsum
  have hRpos : 0 < R := by
    dsimp [R]
    exact Nat.sub_pos_of_lt hmh'
  have hRltU : R < U := by
    dsimp [R]
    exact Nat.sub_lt (pow_pos hp.pos _) (Nat.mul_pos hmpos hhpos)
  have hQUL : Q * U = p ^ L := by
    dsimp [Q, U, L]
    rw [← pow_add]
    congr 1
    omega
  have hNform : N = p ^ L + R := by
    have hEq :
        N + (Q + 1) * h = (p ^ L + R) + (Q + 1) * h := by
      calc
        N + (Q + 1) * h = (Q + 1) * (q + h) := by
          dsimp [N]
          ring
        _ = (Q + 1) * U := by rw [show q + h = U by simpa [U] using hqh]
        _ = Q * U + U := by ring
        _ = p ^ L + U := by rw [hQUL]
        _ = p ^ L + ((Q + 1) * h + R) := by rw [hRsum]
        _ = (p ^ L + R) + (Q + 1) * h := by ring
    exact Nat.add_right_cancel hEq
  have hUlePL : U ≤ p ^ L := by
    dsimp [U, L]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  have hRltPL : R < p ^ L := hRltU.trans_le hUlePL
  have hNpos : 0 < N := by
    rw [hNform]
    positivity
  have hNlt : N < p ^ (L + 1) := by
    rw [hNform]
    calc
      p ^ L + R < p ^ L + p ^ L := Nat.add_lt_add_left hRltPL _
      _ = 2 * p ^ L := by omega
      _ ≤ p * p ^ L := Nat.mul_le_mul_right _ hp.two_le
      _ = p ^ (L + 1) := by
        calc
          p * p ^ L = p ^ L * p := Nat.mul_comm _ _
          _ = p ^ (L + 1) := (pow_succ p L).symm
  have hQAhigh : Q * A = p ^ (2 * a - 1) := by
    dsimp [Q, A]
    rw [← pow_add]
    congr 1
    omega
  have hkform : k = A + p ^ (2 * a - 1) := by
    dsimp [k]
    rw [Nat.add_mul, one_mul, hQAhigh]
    omega
  have hlog : Nat.log p N < L + 1 :=
    (Nat.log_lt_iff_lt_pow hp.one_lt (Nat.ne_of_gt hNpos)).2 hNlt
  change padicValNat p (N.choose k) ≤ a
  rw [padicVal_choose_eq_carryCount hkn hlog, carryCount]
  let C := (Finset.Ico 1 (L + 1)).filter fun i ↦ CarryAt p N k i
  have hsub : C ⊆ Finset.Icc (2 * a) L := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hiRange := Finset.mem_Ico.mp hi'.1
    have hcarry := hi'.2
    apply Finset.mem_Icc.mpr
    refine ⟨?_, by omega⟩
    by_contra hlow
    have hiLt : i < 2 * a := by omega
    have hprefix : k % p ^ i ≤ N % p ^ i := by
      by_cases hia : i ≤ a - 1
      · have hdivA : p ^ i ∣ A := by
          dsimp [A]
          exact Nat.pow_dvd_pow p hia
        have hdivK : p ^ i ∣ k := by
          dsimp [k]
          exact dvd_mul_of_dvd_right hdivA (Q + 1)
        rw [Nat.mod_eq_zero_of_dvd hdivK]
        exact Nat.zero_le _
      · have hai : a ≤ i := by omega
        have hiHigh : i ≤ 2 * a - 1 := by omega
        have hdivHigh : p ^ i ∣ p ^ (2 * a - 1) :=
          Nat.pow_dvd_pow p hiHigh
        have hAltPow : A < p ^ i := by
          dsimp [A]
          exact Nat.pow_lt_pow_right hp.one_lt (by omega)
        have hkmod : k % p ^ i = A := by
          rw [hkform, Nat.add_mod,
            Nat.mod_eq_of_lt hAltPow,
            Nat.mod_eq_zero_of_dvd hdivHigh]
          simp [Nat.mod_eq_of_lt hAltPow]
        have hdivTop : p ^ i ∣ p ^ L :=
          Nat.pow_dvd_pow p (by omega)
        have hnmod : N % p ^ i = R % p ^ i := by
          rw [hNform, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdivTop, zero_add]
          simp
        have hRmodGt : A < R % p ^ i := by
          by_cases hit : i ≤ t + 1
          · let J := p ^ (i - a)
            have hJpos : 0 < J := by
              dsimp [J]
              exact pow_pos hp.pos _
            have hPowI : p ^ i = Q * J := by
              dsimp [Q, J]
              rw [← pow_add]
              congr 1
              omega
            have hhPowI : h < p ^ i := by
              exact hhsmall.trans
                (Nat.pow_lt_pow_right hp.one_lt (by omega))
            have hQhmod : (Q * h) % p ^ i = Q * (h % J) := by
              rw [hPowI, Nat.mul_mod_mul_left]
            have hMform : (Q + 1) * h = h + Q * h := by ring
            have hmodJlt : h % J < J := Nat.mod_lt _ hJpos
            have hhsumLtQ : h + A < Q := by omega
            have hQstep : Q * (h % J) + Q ≤ Q * J := by
              calc
                Q * (h % J) + Q = Q * ((h % J) + 1) := by ring
                _ ≤ Q * J :=
                  Nat.mul_le_mul_left Q (Nat.succ_le_iff.mpr hmodJlt)
            have hcandPlus :
                h + Q * (h % J) + A < p ^ i := by
              rw [hPowI]
              calc
                h + Q * (h % J) + A =
                    Q * (h % J) + (h + A) := by ring
                _ < Q * (h % J) + Q := Nat.add_lt_add_left hhsumLtQ _
                _ ≤ Q * J := hQstep
            have hcandLt : h + Q * (h % J) < p ^ i := by
              omega
            have hmMod :
                ((Q + 1) * h) % p ^ i = h + Q * (h % J) := by
              rw [hMform, Nat.add_mod, Nat.mod_eq_of_lt hhPowI, hQhmod]
              exact Nat.mod_eq_of_lt hcandLt
            have hmModPos : 0 < ((Q + 1) * h) % p ^ i := by
              rw [hmMod]
              omega
            have hdivU : p ^ i ∣ U := by
              dsimp [U]
              exact Nat.pow_dvd_pow p hit
            have hmodsum :
                (R % p ^ i + ((Q + 1) * h) % p ^ i) % p ^ i = 0 := by
              rw [← Nat.add_mod, hRsum', Nat.mod_eq_zero_of_dvd hdivU]
            by_contra hnot
            have hRle : R % p ^ i ≤ A := Nat.le_of_not_gt hnot
            have hsumLt :
                R % p ^ i + ((Q + 1) * h) % p ^ i < p ^ i := by
              rw [hmMod]
              exact lt_of_le_of_lt
                (Nat.add_le_add_right hRle _)
                (by
                  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                    using hcandPlus)
            have hzero :
                R % p ^ i + ((Q + 1) * h) % p ^ i = 0 := by
              simpa [Nat.mod_eq_of_lt hsumLt] using hmodsum
            exact (Nat.ne_of_gt hmModPos)
              (Nat.eq_zero_of_add_eq_zero_left hzero)
          · have hti : t + 1 < i := by omega
            have hUltPow : U < p ^ i := by
              dsimp [U]
              exact Nat.pow_lt_pow_right hp.one_lt hti
            have hRltPow : R < p ^ i := hRltU.trans hUltPow
            have hRmod : R % p ^ i = R := Nat.mod_eq_of_lt hRltPow
            let s := t + 1 - a
            have hs0 : 1 ≤ s := by
              dsimp [s]
              omega
            have hs1 : s ≤ a - 1 := by
              dsimp [s]
              omega
            have hUQ : U = Q * p ^ s := by
              dsimp [U, Q, s]
              rw [← pow_add]
              congr 1
              omega
            have hpsLeA : p ^ s ≤ A := by
              dsimp [A]
              exact Nat.pow_le_pow_right hp.pos hs1
            have hpsPos : 0 < p ^ s := pow_pos hp.pos _
            have hpsLtM : p ^ s < Q + 1 :=
              lt_trans (hpsLeA.trans_lt hAltQ) (Nat.lt_succ_self Q)
            have hUplus : U + p ^ s = (Q + 1) * p ^ s := by
              rw [hUQ]
              ring
            have hresPlus : (Q + 1 - p ^ s) + p ^ s = Q + 1 :=
              Nat.sub_add_cancel hpsLtM.le
            have hUzero : U + p ^ s ≡ 0 [MOD Q + 1] := by
              rw [hUplus]
              exact (dvd_mul_right (Q + 1) (p ^ s)).modEq_zero_nat
            have hresZero : (Q + 1 - p ^ s) + p ^ s ≡ 0 [MOD Q + 1] := by
              rw [hresPlus]
              exact (dvd_refl (Q + 1)).modEq_zero_nat
            have hUres : U ≡ Q + 1 - p ^ s [MOD Q + 1] :=
              Nat.ModEq.add_right_cancel' (p ^ s) (hUzero.trans hresZero.symm)
            have hRcongU : R ≡ U [MOD Q + 1] := by
              rw [← hRsum']
              simp
            have hRres : R ≡ Q + 1 - p ^ s [MOD Q + 1] :=
              hRcongU.trans hUres
            have hresLt : Q + 1 - p ^ s < Q + 1 :=
              Nat.sub_lt hmpos hpsPos
            have hRmodM : R % (Q + 1) = Q + 1 - p ^ s := by
              unfold Nat.ModEq at hRres
              simpa [Nat.mod_eq_of_lt hresLt] using hRres
            have hresLeR : Q + 1 - p ^ s ≤ R := by
              rw [← hRmodM]
              exact Nat.mod_le _ _
            have hAres : A + 1 ≤ Q + 1 - p ^ s := by
              omega
            rw [hRmod]
            omega
        rw [hkmod, hnmod]
        exact hRmodGt.le
    have hno : ¬ CarryAt p N k i :=
      (not_carryAt_iff_mod_pow_le hp.pos hkn).2 hprefix
    exact hno hcarry
  have hcard := Finset.card_le_card hsub
  change C.card ≤ a
  calc
    C.card ≤ (Finset.Icc (2 * a) L).card := hcard
    _ ≤ a := by
      simp
      dsimp [L]
      omega
end PascalExtremes
end
end

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p a q : ℕ} (hp : p.Prime) (ha : 2 ≤ a)
    (hq2 : 2 ≤ q) (hqlt : q < q0 p a) :
    ∃ d, 0 < d ∧ d < q ∧
      padicValNat p
        (((p ^ a + 1) * q).choose ((p ^ a + 1) * d)) ≤ a := by
  let Q := p ^ a
  let m := Q + 1
  let t := Nat.log p q
  let P := p ^ t
  let lam := q / P
  let b := q % P
  have hmpos : 0 < m := by dsimp [m]; omega
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact pow_pos hp.pos _
  have hQgePbase : p ≤ Q := by
    dsimp [Q]
    calc
      p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos (by omega)
  have hQgtPbase : p < Q := by
    dsimp [Q]
    calc
      p = p ^ 1 := (pow_one p).symm
      _ < p ^ a := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hPpos : 0 < P := by
    dsimp [P]
    exact pow_pos hp.pos _
  have hPleq : P ≤ q := by
    dsimp [P, t]
    exact Nat.pow_log_le_self p (by omega)
  have hqLtPp : q < P * p := by
    dsimp [P, t]
    simpa [pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self hp.one_lt q
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
    exact (Nat.not_le_of_gt hqLtPp) (hmul.trans hPle)
  have hpowSucc : p ^ (a + 1) = p * Q := by
    dsimp [Q]
    rw [pow_succ, Nat.mul_comm]
  by_cases hb0 : b = 0
  · by_cases hlam1 : lam = 1
    · have hqP : q = P := by
        rw [hb0, hlam1, mul_one, zero_add] at hqDecomp
        exact hqDecomp
      have htpos : 0 < t := by
        by_contra h
        have ht0 : t = 0 := Nat.eq_zero_of_not_pos h
        rw [hqP] at hq2
        dsimp [P] at hq2
        rw [ht0, pow_zero] at hq2
        omega
      let d := p ^ (t - 1)
      have hdpos : 0 < d := by
        dsimp [d]
        exact pow_pos hp.pos _
      have hdlt : d < q := by
        rw [hqP]
        dsimp [d, P]
        exact Nat.pow_lt_pow_right hp.one_lt (by omega)
      refine ⟨d, hdpos, hdlt, ?_⟩
      have hqPow : q = p ^ t := by simpa [P] using hqP
      have hval :=
        targetB_pure_power_witness_le (p := p) (a := a) (t := t)
          hp ha (by omega : 1 ≤ t)
      rw [← hqPow] at hval
      simpa [d] using hval
    · have hlam2 : 2 ≤ lam := by omega
      let d := P
      have hdpos : 0 < d := by simpa [d] using hPpos
      have hdlt : d < q := by
        rw [hqDecomp, hb0, zero_add]
        dsimp [d]
        have hlt : P < P * lam := by
          have := (Nat.mul_lt_mul_left hPpos).2 (show 1 < lam by omega)
          simpa using this
        exact hlt
      refine ⟨d, hdpos, hdlt, ?_⟩
      have hNform :
          m * q = 0 + P * (m * lam) := by
        rw [hqDecomp, hb0]
        ring
      have hkform :
          m * d = 0 + P * m := by
        dsimp [d]
        ring
      have hs : m * lam < p ^ (a + 1) := by
        have hlamQ : lam < Q := hlamLt.trans hQgtPbase
        have hstep : lam + 1 ≤ p := Nat.succ_le_iff.mpr hlamLt
        rw [hpowSucc]
        calc
          m * lam = Q * lam + lam := by
            dsimp [m]
            ring
          _ < Q * lam + Q := Nat.add_lt_add_left hlamQ _
          _ = Q * (lam + 1) := by ring
          _ ≤ Q * p := Nat.mul_le_mul_left Q hstep
          _ = p * Q := Nat.mul_comm _ _
      have hkn : m * d ≤ m * q :=
        Nat.mul_le_mul_left m hdlt.le
      have hval :=
        padicVal_choose_le_of_common_suffix
          (p := p) (n := m * q) (k := m * d)
          (u := 0) (t := t) (s := m * lam) (x := m) (r := a)
          hp (Nat.mul_pos hmpos (by omega)) hkn
          (by simpa [P] using hPpos)
          (by simpa [P] using hNform)
          (by simpa [P] using hkform)
          (by
            simpa using Nat.mul_le_mul_left m (show 1 ≤ lam by omega)) hs
      simpa [m, Q] using hval
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
    let X := (m * b) / P
    let u := (m * b) % P
    have hmbDecomp : m * b = u + P * X := by
      dsimp [u, X]
      exact (Nat.mod_add_div (m * b) P).symm
    have huLt : u < P := by
      dsimp [u]
      exact Nat.mod_lt _ hPpos
    have hXLt : X < m := by
      dsimp [X]
      rw [Nat.div_lt_iff_lt_mul hPpos]
      exact (Nat.mul_lt_mul_left hmpos).2 hbLt
    have hXleQ : X ≤ Q := by
      dsimp [m] at hXLt
      omega
    have hbq : b < q := by
      rw [hqDecomp]
      have hPLamPos : 0 < P * lam := Nat.mul_pos hPpos hlamPos
      omega
    by_cases hgood : X + m * lam < p ^ (a + 1)
    · refine ⟨b, hbpos, hbq, ?_⟩
      have hNform :
          m * q = u + P * (X + m * lam) := by
        rw [hqDecomp]
        calc
          m * (b + P * lam) = m * b + P * (m * lam) := by ring
          _ = (u + P * X) + P * (m * lam) := by rw [hmbDecomp]
          _ = u + P * (X + m * lam) := by ring
      have hkn : m * b ≤ m * q :=
        Nat.mul_le_mul_left m hbq.le
      have hval :=
        padicVal_choose_le_of_common_suffix
          (p := p) (n := m * q) (k := m * b)
          (u := u) (t := t) (s := X + m * lam) (x := X) (r := a)
          hp (Nat.mul_pos hmpos (by omega)) hkn huLt
          (by simpa [P] using hNform)
          (by simpa [P] using hmbDecomp)
          (Nat.le_add_right _ _) hgood
      simpa [m, Q] using hval
    · have hbad : p ^ (a + 1) ≤ X + m * lam :=
        Nat.le_of_not_gt hgood
      have hlamEq : lam = p - 1 := by
        by_contra hne
        have hlamLe : lam ≤ p - 2 := by omega
        have hlamSucc : lam + 1 ≤ p - 1 := by omega
        have hlamQ : lam < Q := hlamLt.trans hQgtPbase
        have hstrict : X + m * lam < p * Q := by
          calc
            X + m * lam = X + (Q + 1) * lam := by rfl
            _ ≤ Q + (Q + 1) * lam :=
              Nat.add_le_add_right hXleQ _
            _ = Q * (lam + 1) + lam := by ring
            _ ≤ Q * (p - 1) + lam :=
              Nat.add_le_add_right (Nat.mul_le_mul_left Q hlamSucc) _
            _ < Q * (p - 1) + Q := Nat.add_lt_add_left hlamQ _
            _ = Q * ((p - 1) + 1) := by ring
            _ = Q * p := by rw [Nat.sub_add_cancel hp.one_le]
            _ = p * Q := Nat.mul_comm _ _
        have : X + m * lam < p ^ (a + 1) := by
          rw [hpowSucc]
          exact hstrict
        exact (Nat.not_lt_of_ge hbad) this
      have hXlow : Q - p + 1 ≤ X := by
        rw [hlamEq] at hbad
        rw [hpowSucc] at hbad
        dsimp [m] at hbad
        let E := Q - p + 1
        let r := p - 1
        have hpEq : p = r + 1 := by
          dsimp [r]
          omega
        have hQEq : Q = E + r := by
          dsimp [E, r]
          omega
        have hid : p * Q = E + (Q + 1) * (p - 1) := by
          rw [hpEq, hQEq]
          dsimp [r]
          ring
        rw [hid] at hbad
        dsimp [E] at hbad
        omega
      let h := P - b
      have hhpos : 0 < h := by
        dsimp [h]
        exact Nat.sub_pos_of_lt hbLt
      have hbh : b + h = P := by
        dsimp [h]
        exact Nat.add_sub_of_le hbLt.le
      have hPXle : P * X ≤ m * b := by
        dsimp [X]
        exact Nat.mul_div_le (m * b) P
      have hEplus : (Q - p + 1) + p = Q + 1 := by
        omega
      have hlowMul : P * (Q - p + 1) ≤ m * b :=
        (Nat.mul_le_mul_left P hXlow).trans hPXle
      have hmPSplit : m * P = m * b + m * h := by
        rw [← Nat.mul_add, hbh]
      have hPEq : P * (Q - p + 1) + p * P = m * P := by
        dsimp [m]
        calc
          P * (Q - p + 1) + p * P =
              P * ((Q - p + 1) + p) := by ring
          _ = P * (Q + 1) := by rw [hEplus]
          _ = (Q + 1) * P := Nat.mul_comm _ _
      have hmhLe : m * h ≤ p * P := by
        omega
      have hpm : ¬ p ∣ m := by
        dsimp [m, Q]
        exact not_p_dvd_pow_add_one hp (by omega)
      have hmhLt : m * h < p * P := by
        refine lt_of_le_of_ne hmhLe ?_
        intro heq
        have hmDiv : m ∣ p * P := ⟨h, heq.symm⟩
        have hpP : p * P = p ^ (t + 1) := by
          dsimp [P]
          calc
            p * p ^ t = p ^ t * p := Nat.mul_comm _ _
            _ = p ^ (t + 1) := (pow_succ p t).symm
        have hcopBase : Nat.Coprime m p := by
          rw [Nat.coprime_comm]
          exact (hp.coprime_iff_not_dvd).2 hpm
        have hcopPow : Nat.Coprime m (p ^ (t + 1)) :=
          (Nat.coprime_pow_right_iff (by omega) m p).2 hcopBase
        have hmOne : m ∣ 1 := by
          apply Nat.Coprime.dvd_of_dvd_mul_right hcopPow
          simpa [one_mul, ← hpP] using hmDiv
        have hmLeOne : m ≤ 1 := Nat.le_of_dvd (by decide) hmOne
        dsimp [m] at hmLeOne
        omega
      have ht0 : a ≤ t := by
        by_contra hnotT
        have htlt : t < a := Nat.lt_of_not_ge hnotT
        have htpow : p ^ (t + 1) ≤ Q := by
          dsimp [Q]
          exact Nat.pow_le_pow_right hp.pos (by omega)
        have hpP : p * P = p ^ (t + 1) := by
          dsimp [P]
          calc
            p * p ^ t = p ^ t * p := Nat.mul_comm _ _
            _ = p ^ (t + 1) := (pow_succ p t).symm
        have hmLe : m ≤ m * h := by
          simpa using Nat.mul_le_mul_left m (show 1 ≤ h by omega)
        have hQltm : Q < m := by
          dsimp [m]
          exact Nat.lt_succ_self Q
        rw [hpP] at hmhLt
        have hloop : p ^ (t + 1) < p ^ (t + 1) := by
          calc
            p ^ (t + 1) ≤ Q := htpow
            _ < m := hQltm
            _ ≤ m * h := hmLe
            _ < p ^ (t + 1) := hmhLt
        exact (Nat.lt_irrefl _) hloop
      have htlt2a : t < 2 * a := by
        have hq0lt : q0 p a < p ^ (2 * a) :=
          q0_lt_pow_two_a hp (by omega)
        have hPlt : P < p ^ (2 * a) :=
          hPleq.trans_lt (hqlt.trans hq0lt)
        dsimp [P] at hPlt
        exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hPlt
      have ht1 : t ≤ 2 * a - 2 := by
        have htLe : t ≤ 2 * a - 1 := by omega
        by_contra hnotT1
        have htEq : t = 2 * a - 1 := by omega
        have hPowEq : p ^ (t + 1) = p ^ (2 * a) := by
          congr 1
          omega
        have hqh : q + h = p ^ (t + 1) := by
          rw [hqDecomp, hlamEq]
          calc
            b + P * (p - 1) + h =
                (b + h) + P * (p - 1) := by omega
            _ = P + P * (p - 1) := by rw [hbh]
            _ = P * p := by
              calc
                P + P * (p - 1) = P * 1 + P * (p - 1) := by simp
                _ = P * (1 + (p - 1)) := (Nat.mul_add _ _ _).symm
                _ = P * p := by congr 1 <;> omega
            _ = p ^ (t + 1) := by
              dsimp [P]
              rw [pow_succ]
        have hQleH : Q ≤ h := by
          have hq' := hqlt
          dsimp [q0] at hq'
          rw [hPowEq] at hqh
          omega
        have hP2 : p ^ (2 * a) = Q * Q := by
          dsimp [Q]
          rw [show 2 * a = a + a by omega, pow_add]
        have hbig : p ^ (2 * a) < m * h := by
          rw [hP2]
          have hstrictQ : Q * Q < (Q + 1) * Q :=
            (Nat.mul_lt_mul_right hQpos).2 (Nat.lt_succ_self Q)
          have hleH : (Q + 1) * Q ≤ (Q + 1) * h :=
            Nat.mul_le_mul_left (Q + 1) hQleH
          dsimp [m]
          exact hstrictQ.trans_le hleH
        have hpP : p * P = p ^ (t + 1) := by
          dsimp [P]
          calc
            p * p ^ t = p ^ t * p := Nat.mul_comm _ _
            _ = p ^ (t + 1) := (pow_succ p t).symm
        rw [hpP, hPowEq] at hmhLt
        exact (Nat.not_lt_of_ge hbig.le) hmhLt
      have hqh : q + h = p ^ (t + 1) := by
        rw [hqDecomp, hlamEq]
        calc
          b + P * (p - 1) + h =
              (b + h) + P * (p - 1) := by omega
          _ = P + P * (p - 1) := by rw [hbh]
          _ = P * p := by
            calc
              P + P * (p - 1) = P * 1 + P * (p - 1) := by simp
              _ = P * (1 + (p - 1)) := (Nat.mul_add _ _ _).symm
              _ = P * p := by congr 1 <;> omega
          _ = p ^ (t + 1) := by
            dsimp [P]
            rw [pow_succ]
      have hhsmall : h < p ^ (a - 1) := by
        let s := t + 1 - a
        have hsLe : s ≤ a - 1 := by
          dsimp [s]
          omega
        have hpowFact : p ^ (t + 1) = Q * p ^ s := by
          dsimp [Q, s]
          rw [← pow_add]
          congr 1
          omega
        have hQhLt : Q * h < p ^ (t + 1) := by
          have hmGtQ : Q < m := by dsimp [m]; omega
          have hmulLt : Q * h < m * h :=
            (Nat.mul_lt_mul_right hhpos).2 hmGtQ
          have hpP : p * P = p ^ (t + 1) := by
            dsimp [P]
            calc
              p * p ^ t = p ^ t * p := Nat.mul_comm _ _
              _ = p ^ (t + 1) := (pow_succ p t).symm
          exact hmulLt.trans (by simpa [hpP] using hmhLt)
        rw [hpowFact] at hQhLt
        have hslt : h < p ^ s :=
          (Nat.mul_lt_mul_left hQpos).mp hQhLt
        exact hslt.trans_le
          (Nat.pow_le_pow_right hp.pos hsLe)
      let d := p ^ (a - 1)
      have hdpos : 0 < d := by
        dsimp [d]
        exact pow_pos hp.pos _
      have hptq : p ^ t < q := by
        have hhPt : h < p ^ t := hhsmall.trans_le
          (Nat.pow_le_pow_right hp.pos (by omega))
        have hpowTwo : 2 * p ^ t ≤ p ^ (t + 1) := by
          rw [pow_succ]
          simpa [Nat.mul_comm] using Nat.mul_le_mul_left (p ^ t) hp.two_le
        omega
      have hdlt : d < q := by
        dsimp [d]
        exact (Nat.pow_le_pow_right hp.pos (by omega)).trans_lt hptq
      refine ⟨d, hdpos, hdlt, ?_⟩
      have hfb :=
        targetB_fallback_choose_le hp ha ht0 ht1 hhpos hhsmall hqh
          (by
            dsimp [m, Q] at hmhLt ⊢
            have hpP : p * P = p ^ (t + 1) := by
              dsimp [P]
              calc
                p * p ^ t = p ^ t * p := Nat.mul_comm _ _
                _ = p ^ (t + 1) := (pow_succ p t).symm
            simpa [hpP] using hmhLt)
      simpa [d] using hfb
end PascalExtremes
