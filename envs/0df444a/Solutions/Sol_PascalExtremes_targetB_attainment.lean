-- Prove2me | solution 1 for PascalExtremes.targetB_attainment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:06:06.606731+00:00
-- url     : https://prove2.me/submissions/42829975-07f6-427b-af79-46fda81ca4f2

module
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetB
public import Theorems.Thm_PascalExtremes_q0_pos
public import Theorems.Thm_PascalExtremes_q0_lt_pow_two_a
public import Theorems.Thm_PascalExtremes_mul_q0_eq_pow_three_add_one
public import Theorems.Thm_PascalExtremes_coprime_pow_two_a_m
public import Theorems.Thm_PascalExtremes_q0_row_admissible
public import Theorems.Thm_PascalExtremes_targetB_attainment_witness
public import Theorems.Thm_PascalExtremes_carryAt_iff_mod_pow_lt
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
public import Theorems.Thm_PascalExtremes_padicVal_G_eq_of_lower_bound_of_witness
public import Theorems.Thm_PascalExtremes_padicVal_choose_eq_carryCount
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff


section
@[expose] public section
namespace PascalExtremes
private lemma selected_multiplier_bounds
    {p a k : ℕ} (hp : p.Prime) (ha : 2 ≤ a)
    (hk : Admissible (p ^ (3 * a) + 1) (p ^ a + 1) k) :
    ∃ d, 0 < d ∧ d < q0 p a ∧ k = (p ^ a + 1) * d := by
  rcases hk.2.2 with ⟨d, hkd⟩
  have hmpos : 0 < p ^ a + 1 := by positivity
  have hid := mul_q0_eq_pow_three_add_one hp (by omega : 1 ≤ a)
  have hdpos : 0 < d := by
    by_contra h
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos h
    rw [hd0, mul_zero] at hkd
    exact (Nat.ne_of_gt hk.1) hkd
  have hdlt : d < q0 p a := by
    rw [← hid] at hk
    rw [hkd] at hk
    exact (Nat.mul_lt_mul_left hmpos).mp hk.2.1
  exact ⟨d, hdpos, hdlt, hkd⟩
private lemma selected_residue_gt_one
    {p a k i : ℕ} (hp : p.Prime) (ha : 2 ≤ a)
    (hk : Admissible (p ^ (3 * a) + 1) (p ^ a + 1) k)
    (hi0 : 2 * a ≤ i) (hi1 : i ≤ 3 * a) :
    1 < k % p ^ i := by
  obtain ⟨d, hdpos, hdlt, hkd⟩ :=
    selected_multiplier_bounds hp ha hk
  let P2 := p ^ (2 * a)
  have hP2pos : 0 < P2 := by
    dsimp [P2]
    exact pow_pos hp.pos _
  have hP2gt1 : 1 < P2 := by
    dsimp [P2]
    have hpa : 1 ≤ 2 * a := by omega
    calc
      1 < p := hp.one_lt
      _ ≤ p ^ (2 * a) := by
        calc
          p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ (2 * a) := Nat.pow_le_pow_right hp.pos hpa
  have hP2divPi : P2 ∣ p ^ i := by
    dsimp [P2]
    exact Nat.pow_dvd_pow p hi0
  have hcop : Nat.Coprime P2 (p ^ a + 1) := by
    dsimp [P2]
    exact coprime_pow_two_a_m hp (by omega)
  have hdltP2 : d < P2 := by
    dsimp [P2]
    exact hdlt.trans (q0_lt_pow_two_a hp (by omega))
  by_contra hnot
  have hle : k % p ^ i ≤ 1 := Nat.le_of_not_gt hnot
  have hz : k % p ^ i = 0 ∨ k % p ^ i = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp hle
  rcases hz with hz | ho
  · have hpidk : p ^ i ∣ k :=
      (Nat.dvd_iff_mod_eq_zero).2 hz
    have hP2k : P2 ∣ k := hP2divPi.trans hpidk
    have hP2md : P2 ∣ d * (p ^ a + 1) := by
      rw [hkd, Nat.mul_comm] at hP2k
      exact hP2k
    have hP2d : P2 ∣ d :=
      Nat.Coprime.dvd_of_dvd_mul_right hcop hP2md
    have hleP2 : P2 ≤ d := Nat.le_of_dvd hdpos hP2d
    omega
  · have hki : k ≡ 1 [MOD p ^ i] := by
      unfold Nat.ModEq
      rw [ho]
      have hpi : 1 < p ^ i := by
        have hiPos : 1 ≤ i := by omega
        calc
          1 < p := hp.one_lt
          _ ≤ p ^ i := by
            calc
              p = p ^ 1 := (pow_one p).symm
              _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos hiPos
      simp [Nat.mod_eq_of_lt hpi]
    have hmd1 : (p ^ a + 1) * d ≡ 1 [MOD P2] := by
      simpa [hkd] using hki.of_dvd hP2divPi
    have hP2div3 : P2 ∣ p ^ (3 * a) := by
      dsimp [P2]
      exact Nat.pow_dvd_pow p (by omega)
    have hmq1 : (p ^ a + 1) * q0 p a ≡ 1 [MOD P2] := by
      rw [mul_q0_eq_pow_three_add_one hp (by omega : 1 ≤ a)]
      simpa using (hP2div3.modEq_zero_nat.add_right 1)
    have hcong :
        (p ^ a + 1) * d ≡ (p ^ a + 1) * q0 p a [MOD P2] :=
      hmd1.trans hmq1.symm
    have hmdLe :
        (p ^ a + 1) * d ≤ (p ^ a + 1) * q0 p a :=
      Nat.mul_le_mul_left _ hdlt.le
    have hdivDiff :
        P2 ∣ (p ^ a + 1) * (q0 p a - d) := by
      have h := (Nat.modEq_iff_dvd' hmdLe).mp hcong
      simpa [Nat.mul_sub_left_distrib] using h
    have hP2diff : P2 ∣ q0 p a - d := by
      exact Nat.Coprime.dvd_of_dvd_mul_right hcop
        (by simpa [Nat.mul_comm] using hdivDiff)
    have hdiffPos : 0 < q0 p a - d := Nat.sub_pos_of_lt hdlt
    have hdiffLt : q0 p a - d < P2 := by
      exact (Nat.sub_lt (q0_pos hp (by omega)) hdpos).trans
        (by
          dsimp [P2]
          exact q0_lt_pow_two_a hp (by omega))
    have hP2le : P2 ≤ q0 p a - d :=
      Nat.le_of_dvd hdiffPos hP2diff
    omega
private theorem targetB_lower_bound_at_target
    {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    ∀ k, Admissible (p ^ (3 * a) + 1) (p ^ a + 1) k →
      a + 1 ≤ padicValNat p ((p ^ (3 * a) + 1).choose k) := by
  intro k hk
  letI : Fact p.Prime := ⟨hp⟩
  have hNpos : 0 < p ^ (3 * a) + 1 := by positivity
  have hNlt : p ^ (3 * a) + 1 < p ^ (3 * a + 1) := by
    have hone : 1 < p ^ (3 * a) := by
      have hExp : 1 ≤ 3 * a := by omega
      calc
        1 < p := hp.one_lt
        _ ≤ p ^ (3 * a) := by
          calc
            p = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ (3 * a) := Nat.pow_le_pow_right hp.pos hExp
    calc
      p ^ (3 * a) + 1 < p ^ (3 * a) + p ^ (3 * a) :=
        Nat.add_lt_add_left hone _
      _ = 2 * p ^ (3 * a) := by omega
      _ ≤ p * p ^ (3 * a) := Nat.mul_le_mul_right _ hp.two_le
      _ = p ^ (3 * a + 1) := by rw [pow_succ, Nat.mul_comm]
  have hlog : Nat.log p (p ^ (3 * a) + 1) < 3 * a + 1 :=
    (Nat.log_lt_iff_lt_pow hp.one_lt (Nat.ne_of_gt hNpos)).2 hNlt
  rw [padicVal_choose_eq_carryCount hk.2.1.le hlog, carryCount]
  let S := Finset.Icc (2 * a) (3 * a)
  let C := (Finset.Ico 1 (3 * a + 1)).filter
    fun i ↦ CarryAt p (p ^ (3 * a) + 1) k i
  have hsub : S ⊆ C := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have hiPos : 1 ≤ i := by omega
    have hpidiv : p ^ i ∣ p ^ (3 * a) :=
      Nat.pow_dvd_pow p hi'.2
    have hNmod : (p ^ (3 * a) + 1) % p ^ i = 1 := by
      rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hpidiv, zero_add]
      have hpi1 : 1 < p ^ i := by
        calc
          1 < p := hp.one_lt
          _ ≤ p ^ i := by
            calc
              p = p ^ 1 := (pow_one p).symm
              _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos hiPos
      simp [Nat.mod_eq_of_lt hpi1]
    have hkres : 1 < k % p ^ i :=
      selected_residue_gt_one hp ha hk hi'.1 hi'.2
    have hcarry : CarryAt p (p ^ (3 * a) + 1) k i :=
      (carryAt_iff_mod_pow_lt hp.pos hk.2.1.le).2 (by
        rw [hNmod]
        exact hkres)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Ico.mpr ⟨hiPos, by omega⟩, hcarry⟩
  have hcard := Finset.card_le_card hsub
  change a + 1 ≤ C.card
  calc
    a + 1 = S.card := by
      dsimp [S]
      simp
      omega
    _ ≤ C.card := hcard
end PascalExtremes
end
end

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    padicValNat p (G (p ^ (3 * a) + 1) (p ^ a + 1)) = a + 1 := by
  have hrow := q0_row_admissible hp ha
  have hlower := targetB_lower_bound_at_target hp ha
  obtain ⟨w, hw, hwEq⟩ := targetB_attainment_witness hp ha
  exact padicVal_G_eq_of_lower_bound_of_witness
    (by positivity) hrow.1 hp hlower ⟨w, hw, hwEq⟩
end PascalExtremes
