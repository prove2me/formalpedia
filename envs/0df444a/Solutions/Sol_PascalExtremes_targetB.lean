-- Prove2me | solution 1 for PascalExtremes.targetB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:07:41.708395+00:00
-- url     : https://prove2.me/submissions/23e634f2-6b9a-4df9-8136-b81518383a39

module
public import Definitions.Def_PascalExtremes_TargetB
public import Definitions.Def_PascalExtremes_Scaling
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetBMinimality
public import Theorems.Thm_PascalExtremes_targetB_lower_nonattainment
public import Theorems.Thm_PascalExtremes_T_isLeast
public import Theorems.Thm_PascalExtremes_T_mem_extremalRows
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
public import Theorems.Thm_PascalExtremes_not_p_dvd_pow_add_one
public import Theorems.Thm_PascalExtremes_q0_row_admissible
public import Theorems.Thm_PascalExtremes_rP_pow_add_one
public import Theorems.Thm_PascalExtremes_targetB_attainment
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff



set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    T p (p ^ a + 1) = p ^ (3 * a) + 1 := by
  have hm2 : 2 ≤ p ^ a + 1 := by
    have hpow : 0 < p ^ a := pow_pos hp.pos _
    omega
  have hpm : ¬ p ∣ p ^ a + 1 :=
    not_p_dvd_pow_add_one hp (by omega)
  have hr : rP p (p ^ a + 1) = a + 1 :=
    rP_pow_add_one hp.one_lt (by omega)
  have hrow0 := q0_row_admissible hp ha
  have hatt := targetB_attainment hp ha
  have hmem0 :
      p ^ (3 * a) + 1 ∈ extremalRows p (p ^ a + 1) := by
    refine ⟨hrow0, ?_⟩
    simpa [hr] using hatt
  have hTle :
      T p (p ^ a + 1) ≤ p ^ (3 * a) + 1 :=
    (T_isLeast hp hm2 hpm).2 hmem0
  have hTmem :=
    T_mem_extremalRows hp hm2 hpm
  have hN0leT :
      p ^ (3 * a) + 1 ≤ T p (p ^ a + 1) := by
    by_contra hnot
    have hTlt :
        T p (p ^ a + 1) < p ^ (3 * a) + 1 :=
      Nat.lt_of_not_ge hnot
    have hlower :=
      targetB_lower_nonattainment hp ha hTmem.1 hTlt
    have hval :
        padicValNat p (G (T p (p ^ a + 1)) (p ^ a + 1)) = a + 1 := by
      simpa [hr] using hTmem.2
    rw [hval] at hlower
    omega
  exact Nat.le_antisymm hTle hN0leT
end PascalExtremes
