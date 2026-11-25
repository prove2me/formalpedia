-- Prove2me | solution 1 for PositivityTheory.CW.GradedNormalNilpotent.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:15.407398+00:00
-- url     : https://prove2.me/submissions/aa1050fc-c4e2-415a-b646-ce77551c8612

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CommutatorAdjointHolds
import Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_coe_L
import Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_MR_mul
import Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_MR_pow
import Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_psiL_iff
import Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_L_sub
import Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_trace_MR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.CW.GradedNormalNilpotent.coe_L

set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS Polynomial
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.GradedNormalNilpotent
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
variable {ε E}
variable (h : Hyp ε E)
include h
namespace PositivityTheory.CW.GradedNormalNilpotent
theorem _root_.solution (h2 : ∀ (k : ℕ) c d, E c d * (Mm E ^ k).trace = (Mm E ^ k).trace * E c d)
    (h3 : ∀ T : Module.End ℂ V, (∀ a b, E a b * T = T * E a b) → ∃ c : ℂ, ∀ v, T v = c • v)
    (h4 : A4) (h5 : ∀ a b, (Mm E * Md ε E - Md ε E * Mm E) a b + Z ε E a b ∈ U E 1) :
    ∀ m : ℕ, 1 ≤ m → n ≤ m → ∀ a b, ∃ u ∈ U E (2 * m - 1), ∃ w : Fin n → Fin n → Module.End ℂ V,
      (∀ c d, w c d ∈ U E (2 * m - 2)) ∧ ((Md ε E * Mm E) ^ m) a b = u + ∑ c, ∑ d, w c d * Z ε E c d := by
  intro m hm hnm a b
  have hM : ∀ a b, Mm E a b ∈ U E 1 := fun a b => h.e1 a b
  have hD : ∀ a b, Md ε E a b ∈ U E 1 := fun a b => Submodule.smul_mem _ _ (h.e1 a b)
  set N := (psi h).mapMatrix (MR h (Mm E) 1 hM) with hNdef
  set N' := (psi h).mapMatrix (MR h (Md ε E) 1 hD) with hN'def
  have htr : ∀ k, (N ^ (k + 1)).trace = 0 := by
    intro k
    obtain ⟨hk, e⟩ := MR_pow h (Mm E) 1 hM k
    obtain ⟨c, hc⟩ := h3 _ (fun a b => h2 (k + 1) a b)
    have hT : (Mm E ^ (k + 1)).trace = c • 1 := LinearMap.ext fun v => by simp [hc]
    have hT' : (Mm E ^ (k + 1)).trace ∈ U E (1 * (k + 1)) := by
      rw [hT]; exact h.mono 0 _ (Nat.zero_le _) (Submodule.smul_mem _ c h.one)
    rw [hNdef, ← map_pow, e, trace_MR h _ _ _ hT', psiL_iff, hT, one_mul]
    exact U_le_Jk ε E k (h.mono 0 k (Nat.zero_le _) (Submodule.smul_mem _ c h.one))
  have hN : N ^ n = 0 := h4 (Q ε E h) n N htr
  obtain ⟨h1, e1⟩ := MR_mul h (Mm E) (Md ε E) 1 1 hM hD
  obtain ⟨h1', e1'⟩ := MR_mul h (Md ε E) (Mm E) 1 1 hD hM
  have hcomm : Commute N N' := by
    show N * N' = N' * N
    rw [hNdef, hN'def, ← map_mul, ← map_mul, e1, e1']
    refine Matrix.ext fun a b => ?_
    rw [← sub_eq_zero]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, MR]
    rw [← map_sub, L_sub, psiL_iff]
    show _ ∈ Jk ε E (0 + 2)
    rw [mem_Jk_succ_succ]
    refine ⟨(Mm E * Md ε E - Md ε E * Mm E) a b + Z ε E a b, h5 a b,
      fun c d => if c = a then (if d = b then -1 else 0) else 0, fun c d => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact neg_mem h.one
      · exact zero_mem _
      · exact zero_mem _
    · simp [ite_mul, Finset.sum_ite_eq', Matrix.sub_apply]
  have hNm : N ^ m = 0 := by rw [← Nat.sub_add_cancel hnm, pow_add, hN, mul_zero]
  have hprod : (N' * N) ^ m = 0 := by rw [hcomm.symm.mul_pow, hNm, mul_zero]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨hk, ek⟩ := MR_pow h (Md ε E * Mm E) (1 + 1) h1' k
  have hx : ((Md ε E * Mm E) ^ (k + 1)) a b ∈ Jk ε E ((1 + 1) * (k + 1)) := by
    rw [← psiL_iff h _ _ (hk a b)]
    have := congrFun (congrFun hprod a) b
    rw [hNdef, hN'def, ← map_mul, e1', ← map_pow, ek] at this
    simpa [MR] using this
  rw [show (1 + 1) * (k + 1) = (2 * (k + 1) - 2) + 2 by omega, mem_Jk_succ_succ] at hx
  obtain ⟨u, hu, w, hw, e⟩ := hx
  exact ⟨u, by rwa [show 2 * (k + 1) - 2 + 1 = 2 * (k + 1) - 1 by omega] at hu, w, hw, e⟩
end PositivityTheory.CW.GradedNormalNilpotent
