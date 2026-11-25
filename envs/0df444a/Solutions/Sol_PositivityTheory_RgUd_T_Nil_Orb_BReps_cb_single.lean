-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.cb_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:41.897656+00:00
-- url     : https://prove2.me/submissions/f901b57a-b083-4af0-ae48-66b35258749c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_CbIsChainApply
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_CbExistsChainOfGen
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_pow_pow
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_pow_succ
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_pow_zero_of_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
open Module Submodule
variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
theorem _root_.solution (N : W →ₗ[E] W) (L : ℕ) (u : W) (hu : (N ^ L) u = 0) (c : Fin L → E) :
    ∃ s ≤ L, ∃ y : W, (N ^ L) y = 0 ∧ (N ^ s) y = ∑ i, c i • (N ^ (i : ℕ)) u ∧
      u ∈ span E {y} ⊔ LinearMap.range N := by
  classical
  by_cases h : ∃ i, ∃ hi : i < L, c ⟨i, hi⟩ ≠ 0
  · obtain ⟨s, ⟨hsL, hcs⟩, hmin⟩ : ∃ s, (∃ hi : s < L, c ⟨s, hi⟩ ≠ 0) ∧
        ∀ i < s, ∀ hi : i < L, c ⟨i, hi⟩ = 0 :=
      ⟨Nat.find h, Nat.find_spec h, fun i hi hiL => by
        by_contra hne; exact Nat.find_min h hi ⟨hiL, hne⟩⟩
    set y : W := ∑ i : Fin L, if s ≤ (i : ℕ) then c i • (N ^ ((i : ℕ) - s)) u else 0 with hydef
    set z : W := ∑ i : Fin L, if s < (i : ℕ) then c i • (N ^ ((i : ℕ) - s - 1)) u else 0 with hzdef
    refine ⟨s, hsL.le, y, ?_, ?_, ?_⟩
    · rw [hydef, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs
      · rw [map_smul, cb_pow_pow, cb_pow_zero_of_le N hu (by omega), smul_zero]
      · exact map_zero _
    · rw [hydef, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h1
      · rw [map_smul, cb_pow_pow, show s + ((i : ℕ) - s) = i by omega]
      · rw [map_zero, hmin i (by omega) i.2, zero_smul]
    · have hyz : y = c ⟨s, hsL⟩ • u + N z := by
        have hc : c ⟨s, hsL⟩ • u = ∑ i : Fin L, if i = ⟨s, hsL⟩ then c i • u else 0 := by
          rw [Finset.sum_ite_eq']; simp
        rw [hc, hydef, hzdef, map_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rcases lt_trichotomy (i : ℕ) s with h1 | h1 | h1
        · have hne : i ≠ ⟨s, hsL⟩ := fun he => by rw [he] at h1; exact lt_irrefl _ h1
          rw [if_neg (by omega), if_neg hne, if_neg (by omega), map_zero, add_zero]
        · have he : i = ⟨s, hsL⟩ := Fin.ext h1
          rw [if_pos (by omega), if_pos he, if_neg (by omega), map_zero, add_zero, h1, Nat.sub_self,
            pow_zero, Module.End.one_apply]
        · have hne : i ≠ ⟨s, hsL⟩ := fun he => by rw [he] at h1; exact lt_irrefl _ h1
          rw [if_pos (by omega), if_neg hne, if_pos h1, zero_add, map_smul, cb_pow_succ,
            show (i : ℕ) - s - 1 + 1 = (i : ℕ) - s by omega]
      have hu_eq : u = (c ⟨s, hsL⟩)⁻¹ • y - N ((c ⟨s, hsL⟩)⁻¹ • z) := by
        rw [hyz, smul_add, smul_smul, inv_mul_cancel₀ hcs, one_smul, map_smul]; abel
      rw [hu_eq]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self y))) (Submodule.mem_sup_right (LinearMap.mem_range_self N _))
  · push Not at h
    refine ⟨L, le_rfl, u, hu, ?_, Submodule.mem_sup_left (Submodule.mem_span_singleton_self u)⟩
    rw [hu]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show c i = 0 from h i i.2, zero_smul]
end PositivityTheory.RgUd.T.Nil.Orb.BReps
