-- Prove2me | solution 1 for PascalExtremes.targetB_lower_nonattainment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:05:34.159569+00:00
-- url     : https://prove2.me/submissions/9b6bbce2-e5bd-49ef-92ed-2a1428b17d88

module
public import Definitions.Def_PascalExtremes_TargetB
public import Definitions.Def_PascalExtremes_Scaling
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetBMinimality
public import Theorems.Thm_PascalExtremes_targetB_lower_multiplier_witness
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
public import Theorems.Thm_PascalExtremes_mul_q0_eq_pow_three_add_one
public import Theorems.Thm_PascalExtremes_padicVal_G_le_choose
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff



set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p a N : ℕ} (hp : p.Prime) (ha : 2 ≤ a)
    (hrow : AdmissibleRow (p ^ a + 1) N)
    (hNlt : N < p ^ (3 * a) + 1) :
    padicValNat p (G N (p ^ a + 1)) ≤ a := by
  let m := p ^ a + 1
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  rcases hrow.2 with ⟨q, hN⟩
  have hq2 : 2 ≤ q := by
    have hrowlt : m < m * q := by
      simpa [m, hN] using hrow.1
    by_contra h
    have hqLt : q < 2 := by omega
    interval_cases q <;> simp_all
  have hq0Eq :
      m * q0 p a = p ^ (3 * a) + 1 := by
    dsimp [m]
    exact mul_q0_eq_pow_three_add_one hp (by omega)
  have hqlt : q < q0 p a := by
    have hmul : m * q < m * q0 p a := by
      rw [hq0Eq]
      simpa [m, hN] using hNlt
    exact (Nat.mul_lt_mul_left hmpos).mp hmul
  obtain ⟨d, hdpos, hdlt, hdval⟩ :=
    targetB_lower_multiplier_witness hp ha hq2 hqlt
  let k := m * d
  have hk : Admissible N m k := by
    refine ⟨Nat.mul_pos hmpos hdpos, ?_, dvd_mul_right m d⟩
    rw [hN]
    dsimp [k]
    exact (Nat.mul_lt_mul_left hmpos).2 hdlt
  have hgle :
      padicValNat p (G N m) ≤ padicValNat p (N.choose k) :=
    padicVal_G_le_choose hmpos hrow.1 hp hk
  have hchoose :
      padicValNat p (N.choose k) ≤ a := by
    rw [hN]
    simpa [m, k] using hdval
  simpa [m] using hgle.trans hchoose
end PascalExtremes
