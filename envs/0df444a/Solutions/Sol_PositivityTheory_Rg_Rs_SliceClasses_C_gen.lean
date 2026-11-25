-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.SliceClasses.C_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:30.901039+00:00
-- url     : https://prove2.me/submissions/45ebdd69-f186-4c26-8ded-4f5ff0898137

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_SliceTensors_PSliceC
import Theorems.Thm_PositivityTheory_Rg_Rs_SliceClasses_C_pow_mem
import Theorems.Thm_PositivityTheory_Rg_Rs_SliceClasses_C_sub_one_mem
import Theorems.Thm_PositivityTheory_Rg_Rs_SliceClasses_C_comm_pow
import Theorems.Thm_PositivityTheory_Rg_Rs_SliceClasses_C_nil
import Theorems.Thm_PositivityTheory_Rg_Rs_SliceClasses_C_restrict_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.SliceClasses
variable {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] {ι : Type*}
namespace PositivityTheory.Rg.Rs.SliceClasses
theorem _root_.solution (M : ι → Module.End ℂ U) (hc : ∀ i j, Commute (M i) (M j)) (Φ : U →ₗ[ℂ] ℂ) :
    ∀ (n : ℕ) (P : Submodule ℂ U), Module.finrank ℂ P = n → (∀ i, ∀ v ∈ P, M i v ∈ P) →
      (∀ i, ∀ v ∈ P, Φ (M i v) = Φ v) → (∃ v ∈ P, Φ v ≠ 0) → ∃ w ∈ P, w ≠ 0 ∧ ∀ i, M i w = w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hst hinv hv
  obtain ⟨v, hv, hΦv⟩ := hv
  by_cases hnil : ∀ i, ∀ u ∈ P, ∃ k : ℕ, ((M i - 1) ^ k) u = 0
  · refine C_nil M hc _ P rfl ?_ hst hnil
    rintro rfl
    rw [Submodule.mem_bot] at hv
    exact hΦv (by rw [hv, map_zero])
  push Not at hnil
  obtain ⟨i, u, hu, hku⟩ := hnil
  have hgP : ∀ x ∈ P, (M i - 1) x ∈ P := C_sub_one_mem (hst i)
  obtain ⟨m, hm, hm1⟩ := ((LinearMap.eventually_isCompl_ker_pow_range_pow ((M i - 1).restrict hgP)).and
    (Filter.eventually_ge_atTop 1)).exists
  set Q : Submodule ℂ U := P ⊓ LinearMap.ker ((M i - 1) ^ m) with hQdef
  obtain ⟨k, hk, r, hr, hkr⟩ := Submodule.mem_sup.1 (hm.sup_eq_top ▸ Submodule.mem_top (x := (⟨v, hv⟩ : P)))
  have hΦr : Φ (r : U) = 0 := by
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 hr
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm1
    rw [← hy, C_restrict_pow hgP, add_comm, pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_sub, hinv i _ (C_pow_mem hgP m' _ y.2), sub_self]
  have hkv : (k : U) + r = v := congrArg Subtype.val hkr
  have hΦk : Φ (k : U) ≠ 0 := by
    intro h0; apply hΦv; rw [← hkv, map_add, h0, hΦr, add_zero]
  have hkQ : (k : U) ∈ Q := by
    refine Submodule.mem_inf.2 ⟨k.2, ?_⟩
    rw [LinearMap.mem_ker, ← C_restrict_pow hgP, LinearMap.mem_ker.1 hk, Submodule.coe_zero]
  have hlt : Q < P := by
    refine lt_of_le_of_ne inf_le_left fun h => hku m ?_
    have h2 : u ∈ Q := h ▸ hu
    exact (Submodule.mem_inf.1 h2).2
  have hstQ : ∀ l, ∀ x ∈ Q, M l x ∈ Q := by
    intro l x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨hst l x hx1, ?_⟩
    rw [LinearMap.mem_ker] at hx2 ⊢
    rw [← C_comm_pow hc i l m x, hx2, map_zero]
  obtain ⟨w, hw, hw0, hfix⟩ := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) Q rfl hstQ
    (fun l x hx => hinv l x (Submodule.mem_inf.1 hx).1) ⟨k, hkQ, hΦk⟩
  exact ⟨w, (Submodule.mem_inf.1 hw).1, hw0, hfix⟩
end PositivityTheory.Rg.Rs.SliceClasses
