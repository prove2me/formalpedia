-- Prove2me | solution 1 for PascalExtremes.targetA_attainment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:59:09.618598+00:00
-- url     : https://prove2.me/submissions/55c93859-6e19-47cd-87b8-90d18d934bd3

module
public import Definitions.Def_PascalExtremes_TargetA
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Theorems.Thm_PascalExtremes_carryAt_iff_mod_pow_lt
public import Theorems.Thm_PascalExtremes_lt_pow_rP
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
public import Theorems.Thm_PascalExtremes_not_carryAt_iff_mod_pow_le
public import Theorems.Thm_PascalExtremes_one_le_padicVal_choose_of_carry
public import Theorems.Thm_PascalExtremes_one_le_rP
public import Theorems.Thm_PascalExtremes_padicVal_G_eq_of_lower_bound_of_witness
public import Theorems.Thm_PascalExtremes_padicVal_choose_eq_carryCount
public import Theorems.Thm_PascalExtremes_pow_pred_rP_le
public import Theorems.Thm_PascalExtremes_targetA_upper_witness
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff


section
@[expose] public section
namespace PascalExtremes
private theorem forced_extremal_carry
    {p m r A c L ell k : ℕ}
    (hp : p.Prime) (hm : 0 < m)
    (hrL : r - 1 ≤ L) (hell : ell ≤ r - 1)
    (hc : c < p ^ (L - ell))
    (hmEq : m = c + p ^ (r - 1) * A)
    (hmod : p ^ (L - ell) ≡ p ^ (r - 1 - ell) [MOD m])
    (hk : Admissible (A * p ^ L + c) m k) :
    CarryAt p (A * p ^ L + c) k (L - ell) := by
  have hellL : ell ≤ L := hell.trans hrL
  have hpowPos : 0 < p ^ (L - ell) := pow_pos hp.pos _
  have hkn : k ≤ A * p ^ L + c := hk.2.1.le
  by_contra hcarry
  have hkmodLe :
      k % p ^ (L - ell) ≤ (A * p ^ L + c) % p ^ (L - ell) :=
    (not_carryAt_iff_mod_pow_le hp.pos hkn).1 hcarry
  have hdivPow : p ^ (L - ell) ∣ p ^ L :=
    Nat.pow_dvd_pow p (Nat.sub_le _ _)
  have hNmod :
      (A * p ^ L + c) % p ^ (L - ell) = c := by
    rw [Nat.add_comm, Nat.add_mod,
      Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdivPow A),
      add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hc]
  let u := k % p ^ (L - ell)
  let B := k / p ^ (L - ell)
  have huLe : u ≤ c := by
    dsimp [u]
    simpa [hNmod] using hkmodLe
  have hpowSplit :
      p ^ L = p ^ (L - ell) * p ^ ell := by
    rw [← pow_add]
    congr 1
    exact (Nat.sub_add_cancel hellL).symm
  have hNdiv :
      (A * p ^ L + c) / p ^ (L - ell) = A * p ^ ell := by
    have hform :
        A * p ^ L + c = c + p ^ (L - ell) * (A * p ^ ell) := by
      rw [hpowSplit]
      ring
    rw [hform, Nat.add_mul_div_left _ _ hpowPos, Nat.div_eq_of_lt hc, zero_add]
  have hBLe : B ≤ A * p ^ ell := by
    dsimp [B]
    have hdiv :=
      Nat.div_le_div_right (c := p ^ (L - ell)) hk.2.1.le
    simpa [hNdiv] using hdiv
  let D := p ^ (r - 1 - ell)
  have hDpos : 0 < D := by
    dsimp [D]
    exact pow_pos hp.pos _
  have hpowTop : p ^ ell * D = p ^ (r - 1) := by
    dsimp [D]
    rw [← pow_add]
    congr 1
    omega
  have hDBLe : D * B ≤ p ^ (r - 1) * A := by
    calc
      D * B ≤ D * (A * p ^ ell) := Nat.mul_le_mul_left D hBLe
      _ = p ^ (r - 1) * A := by
        rw [← hpowTop]
        ring
  have hkDecomp : u + p ^ (L - ell) * B = k := by
    dsimp [u, B]
    exact Nat.mod_add_div k (p ^ (L - ell))
  have hkMod : k ≡ u + D * B [MOD m] := by
    rw [← hkDecomp]
    exact (hmod.mul_right B).add_left u
  have hkZero : k ≡ 0 [MOD m] := hk.2.2.modEq_zero_nat
  have hzZero : u + D * B ≡ 0 [MOD m] :=
    hkMod.symm.trans hkZero
  have hzDiv : m ∣ u + D * B :=
    Nat.modEq_zero_iff_dvd.mp hzZero
  have hzLe : u + D * B ≤ m := by
    rw [hmEq]
    exact Nat.add_le_add huLe hDBLe
  by_cases hz0 : u + D * B = 0
  · have hu0 : u = 0 :=
      Nat.eq_zero_of_add_eq_zero_right hz0
    have hDB0 : D * B = 0 :=
      Nat.eq_zero_of_add_eq_zero_left hz0
    have hB0 : B = 0 := by
      rcases Nat.mul_eq_zero.mp hDB0 with hD | hB
      · exact False.elim (Nat.ne_of_gt hDpos hD)
      · exact hB
    have hk0 : k = 0 := by
      rw [← hkDecomp, hu0, hB0]
      simp
    exact (Nat.ne_of_gt hk.1) hk0
  · have hzPos : 0 < u + D * B := Nat.pos_of_ne_zero hz0
    have hmLe : m ≤ u + D * B := Nat.le_of_dvd hzPos hzDiv
    have hzEq : u + D * B = m := Nat.le_antisymm hzLe hmLe
    have huEq : u = c := by omega
    have hDBEq : D * B = p ^ (r - 1) * A := by omega
    have hBEq : B = A * p ^ ell := by
      apply Nat.mul_left_cancel hDpos
      calc
        D * B = p ^ (r - 1) * A := hDBEq
        _ = D * (A * p ^ ell) := by
          rw [← hpowTop]
          ring
    have hkEq :
        k = A * p ^ L + c := by
      calc
        k = u + p ^ (L - ell) * B := hkDecomp.symm
        _ = c + p ^ (L - ell) * (A * p ^ ell) := by
          rw [huEq, hBEq]
        _ = A * p ^ L + c := by
          rw [hpowSplit]
          ring
    exact hk.2.1.ne hkEq
private theorem top_interval_lower_bound
    {p m r A c L : ℕ}
    (hp : p.Prime) (hm : 0 < m)
    (hr2 : 2 ≤ r)
    (hrL : r ≤ L)
    (h2rL : 2 * (r - 1) ≤ L)
    (hcP : c < p ^ (r - 1))
    (hmEq : m = c + p ^ (r - 1) * A)
    (hmods :
      ∀ ell ≤ r - 1,
        p ^ (L - ell) ≡ p ^ (r - 1 - ell) [MOD m])
    (hNlt : A * p ^ L + c < p ^ (L + 1))
    {k : ℕ} (hk : Admissible (A * p ^ L + c) m k) :
    r ≤ padicValNat p ((A * p ^ L + c).choose k) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hNpos : 0 < A * p ^ L + c :=
    lt_trans hk.1 hk.2.1
  have hlog : Nat.log p (A * p ^ L + c) < L + 1 :=
    (Nat.log_lt_iff_lt_pow hp.one_lt (Nat.ne_of_gt hNpos)).2 hNlt
  rw [padicVal_choose_eq_carryCount hk.2.1.le hlog, carryCount]
  let S := Finset.Icc (L + 1 - r) L
  let C := (Finset.Ico 1 (L + 1)).filter
    fun i ↦ CarryAt p (A * p ^ L + c) k i
  have hstart : 1 ≤ L + 1 - r := by omega
  have hsub : S ⊆ C := by
    intro s hs
    have hsI := Finset.mem_Icc.mp hs
    have hs1 : 1 ≤ s := hstart.trans hsI.1
    have hsL : s ≤ L := hsI.2
    let ell := L - s
    have hell : ell ≤ r - 1 := by
      dsimp [ell]
      omega
    have hsEq : L - ell = s := by
      dsimp [ell]
      omega
    have hcS : c < p ^ (L - ell) := by
      have hsGe : r - 1 ≤ L - ell := by
        rw [hsEq]
        omega
      have hpowLe : p ^ (r - 1) ≤ p ^ (L - ell) :=
        Nat.pow_le_pow_right hp.pos hsGe
      exact hcP.trans_le hpowLe
    have hcarry :
        CarryAt p (A * p ^ L + c) k (L - ell) :=
      forced_extremal_carry hp hm (by omega) hell hcS hmEq
        (hmods ell hell) hk
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · exact Finset.mem_Ico.mpr ⟨hs1, by omega⟩
    · simpa [hsEq] using hcarry
  have hcard := Finset.card_le_card hsub
  change r ≤ C.card
  calc
    r = S.card := by
      dsimp [S]
      simp
      omega
    _ ≤ C.card := hcard
private theorem targetA_attainment_r1
    {p m : ℕ} (hp : p.Prime) (hm2 : 2 ≤ m) (hpm : ¬ p ∣ m)
    (hr : rP p m = 1) :
    padicValNat p (G (m * p) m) = rP p m := by
  have hm : 0 < m := by omega
  have hrow : AdmissibleRow m (m * p) := by
    refine ⟨?_, dvd_mul_right m p⟩
    nlinarith [hp.two_le]
  have hlower :
      ∀ k, Admissible (m * p) m k →
        1 ≤ padicValNat p ((m * p).choose k) := by
    intro k hk
    rcases hk.2.2 with ⟨d, rfl⟩
    have hdPos : 0 < d := by
      have := hk.1
      nlinarith
    have hdLt : d < p :=
      (Nat.mul_lt_mul_left hm).mp hk.2.1
    have hpd : ¬ p ∣ d :=
      Nat.not_dvd_of_pos_of_lt hdPos hdLt
    have hpk : ¬ p ∣ m * d := by
      intro h
      rcases hp.dvd_mul.mp h with h | h
      · exact hpm h
      · exact hpd h
    have hkmodPos : 0 < (m * d) % p := by
      apply Nat.pos_of_ne_zero
      intro hzero
      exact hpk ((Nat.dvd_iff_mod_eq_zero).2 hzero)
    have hcarry : CarryAt p (m * p) (m * d) 1 := by
      apply (carryAt_iff_mod_pow_lt hp.pos hk.2.1.le).2
      rw [pow_one, Nat.mod_eq_zero_of_dvd (by
        exact ⟨m, by rw [Nat.mul_comm]⟩)]
      exact hkmodPos
    exact one_le_padicVal_choose_of_carry hp hk.2.1.le (by omega) hcarry
  obtain ⟨w, hw, hwUpper⟩ :=
    targetA_upper_witness hp hm2 hpm hrow
  have hwUpper1 : padicValNat p ((m * p).choose w) ≤ 1 := by
    simpa [hr] using hwUpper
  have hwEq : padicValNat p ((m * p).choose w) = 1 :=
    Nat.le_antisymm hwUpper1 (hlower w hw)
  have hG :=
    padicVal_G_eq_of_lower_bound_of_witness hm hrow.1 hp
      hlower ⟨w, hw, hwEq⟩
  simpa [hr] using hG
private theorem targetA_attainment_rge2
    {p m : ℕ} (hp : p.Prime) (hm2 : 2 ≤ m) (hpm : ¬ p ∣ m)
    (hr2 : 2 ≤ rP p m) :
    ∃ N, AdmissibleRow m N ∧
      padicValNat p (G N m) = rP p m := by
  let r := rP p m
  let P := p ^ (r - 1)
  let A := m / P
  let c := m % P
  let L := r - 1 + Nat.totient m * r
  let N := A * p ^ L + c
  have hm : 0 < m := by omega
  have hr2' : 2 ≤ r := by simpa [r] using hr2
  have hPpos : 0 < P := by
    dsimp [P]
    exact pow_pos hp.pos _
  have hPLe : P ≤ m := by
    dsimp [P, r]
    exact pow_pred_rP_le (by omega)
  have hPdivp : p ∣ P := by
    dsimp [P]
    exact dvd_pow_self p (by omega)
  have hPLt : P < m := by
    refine lt_of_le_of_ne hPLe ?_
    intro hEq
    apply hpm
    rw [← hEq]
    exact hPdivp
  have hcLt : c < P := by
    dsimp [c]
    exact Nat.mod_lt _ hPpos
  have hcPos : 0 < c := by
    apply Nat.pos_of_ne_zero
    intro hc0
    apply hpm
    apply hPdivp.trans
    apply (Nat.dvd_iff_mod_eq_zero).2
    simpa [c] using hc0
  have hApos : 0 < A := by
    dsimp [A]
    exact Nat.div_pos hPLe hPpos
  have hmDecomp : m = c + P * A := by
    dsimp [c, P, A]
    exact (Nat.mod_add_div m (p ^ (r - 1))).symm
  have hmPow : m < p ^ r := by
    dsimp [r]
    exact lt_pow_rP hp.one_lt
  have hmPP : m < P * p := by
    have hrSucc : r = (r - 1) + 1 := by omega
    rw [hrSucc, pow_succ] at hmPow
    simpa [P] using hmPow
  have hAlt : A < p := by
    dsimp [A]
    rw [Nat.div_lt_iff_lt_mul hPpos]
    simpa [Nat.mul_comm] using hmPP
  have hphiPos : 0 < Nat.totient m := Nat.totient_pos.mpr hm
  have hrL : r ≤ L := by
    dsimp [L]
    have hmul : r ≤ Nat.totient m * r := by
      nlinarith
    omega
  have h2rL : 2 * (r - 1) ≤ L := by
    dsimp [L]
    have hmul : r ≤ Nat.totient m * r := by
      nlinarith
    omega
  have hLgt : r - 1 < L := by omega
  have hcop : Nat.Coprime p m :=
    (hp.coprime_iff_not_dvd).2 hpm
  have heuler : p ^ Nat.totient m ≡ 1 [MOD m] :=
    Nat.ModEq.pow_totient hcop
  have hblock : p ^ (Nat.totient m * r) ≡ 1 [MOD m] := by
    rw [pow_mul]
    simpa using heuler.pow r
  have hmods :
      ∀ ell ≤ r - 1,
        p ^ (L - ell) ≡ p ^ (r - 1 - ell) [MOD m] := by
    intro ell hell
    have hExp :
        L - ell = (r - 1 - ell) + Nat.totient m * r := by
      dsimp [L]
      omega
    rw [hExp, pow_add]
    simpa using
      (Nat.ModEq.refl (p ^ (r - 1 - ell))).mul hblock
  have hmodL : p ^ L ≡ P [MOD m] := by
    simpa [P] using hmods 0 (by omega)
  have hNdiv : m ∣ N := by
    have hcong : N ≡ m [MOD m] := by
      dsimp [N]
      have h := (hmodL.mul_left A).add_right c
      have hrhs : A * P + c = m := by
        simpa [Nat.add_comm, Nat.mul_comm] using hmDecomp.symm
      rw [hrhs] at h
      exact h
    exact Nat.modEq_zero_iff_dvd.mp
      (hcong.trans (dvd_rfl.modEq_zero_nat))
  have hpowLt : P < p ^ L := by
    dsimp [P]
    exact Nat.pow_lt_pow_right hp.one_lt hLgt
  have hmLtN : m < N := by
    dsimp [N]
    rw [hmDecomp]
    have hmul := (Nat.mul_lt_mul_left hApos).2 hpowLt
    nlinarith
  have hcL : c < p ^ L :=
    hcLt.trans_le (Nat.pow_le_pow_right hp.pos (by omega))
  have hNlt : N < p ^ (L + 1) := by
    dsimp [N]
    calc
      A * p ^ L + c < A * p ^ L + p ^ L :=
        Nat.add_lt_add_left hcL _
      _ = (A + 1) * p ^ L := by ring
      _ ≤ p * p ^ L :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hAlt)
      _ = p ^ (L + 1) := by rw [pow_succ, Nat.mul_comm]
  have hlower :
      ∀ k, Admissible N m k →
        r ≤ padicValNat p (N.choose k) := by
    intro k hk
    dsimp [N] at hk ⊢
    apply top_interval_lower_bound hp hm hr2' hrL h2rL
      (by simpa [P] using hcLt)
      (by simpa [P] using hmDecomp)
      hmods
      (by simpa [N] using hNlt)
      hk
  have hrow : AdmissibleRow m N := ⟨hmLtN, hNdiv⟩
  obtain ⟨w, hw, hwUpper⟩ :=
    targetA_upper_witness hp hm2 hpm hrow
  have hwEq : padicValNat p (N.choose w) = r :=
    Nat.le_antisymm hwUpper (hlower w hw)
  have hG :
      padicValNat p (G N m) = r :=
    padicVal_G_eq_of_lower_bound_of_witness hm hmLtN hp
      hlower ⟨w, hw, hwEq⟩
  exact ⟨N, hrow, by simpa [r] using hG⟩
end PascalExtremes
end
end

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p m : ℕ} (hp : p.Prime) (hm2 : 2 ≤ m) (hpm : ¬ p ∣ m) :
    ∃ N, AdmissibleRow m N ∧
      padicValNat p (G N m) = rP p m := by
  by_cases hr : rP p m = 1
  · refine ⟨m * p, ?_, targetA_attainment_r1 hp hm2 hpm hr⟩
    refine ⟨?_, dvd_mul_right m p⟩
    nlinarith [hp.two_le]
  · have hr2 : 2 ≤ rP p m := by
      have := one_le_rP p m
      omega
    exact targetA_attainment_rge2 hp hm2 hpm hr2
end PascalExtremes
