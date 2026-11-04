-- Prove2me | solution 1 for ThreeSum.LightTernaryScalarChannel.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:49:30.497848+00:00
-- url     : https://prove2.me/submissions/8685ea20-5c04-4572-9600-714a29d5e1d3

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryScalarChannel
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_ThreeSum_LightArray_source_read
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_compile_safe
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_compile_val
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryWeightChannels_leftMoment_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_powerCircuit_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_rightMoment_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_scalarPower_eval
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryWeightChannels.leftMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.powerCircuit_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.rightMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.scalarPower_eval
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryScalarChannel
open Light LightFixedArithmetic TernaryWeightChannels
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryScalarChannel
theorem _root_.solution (e : Circuit) {p src n dst U : ℕ} (hmain : P[p]? = some (body e)) (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + n ≤ lim.space) (hdst : dst + n ≤ lim.space)
    (hsep : LightArray.SourceSafe src dst n) (hread : ∀ i < n, μ (src + i) = f i) (hf : ∀ i < n, |f i| ≤ (U : ℤ))
    (hword : max (U : ℤ) (e.bound U) ≤ lim.word) :
    Meets lim P p d [src, n, dst] μ (time e n)
      (fun _ ν => (∀ i < n, ν (dst + i) = e.eval (fun _ => f i)) ∧ SameOutside μ ν dst n) :=
  by
  have hU : (U : ℤ) ≤ lim.word := (le_max_left _ _).trans hword
  have he : e.bound U ≤ lim.word := (le_max_right _ _).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.pass (fun i => e.eval (fun _ => f i)) ?round
      ⟨fun i hi => by dsimp only; exact wrote_done hi, by
        ( try refine _root_.Light.SameOn.cell ?_
          intro x_p2m_3206524611924492242 hx_p2m_3206524611924492242
          first
          | ((  repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_810016347422872369);
                    (try have := h_p2m_810016347422872369 x_p2m_3206524611924492242 (by omega));
                    revert h_p2m_810016347422872369)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          |
            (simp [] at hx_p2m_3206524611924492242;
              ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_17131769561751946388);
                    (try have := h_p2m_17131769561751946388 x_p2m_3206524611924492242 (by omega));
                    revert h_p2m_17131769561751946388)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          | ( ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_5149153414676731559);
                    (try have := h_p2m_5149153414676731559 x_p2m_3206524611924492242 (by omega));
                    revert h_p2m_5149153414676731559)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
              fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                          its condition K x does not follow from the hypotheses."))⟩
      hw hdst rfl rfl
  case round =>
    intro j hj
    let σ : State := ⟨Function.update (frame [src, n, dst]) 3 (j : ℤ), wrote μ dst (fun i => e.eval (fun _ => f i)) j⟩
    have hr := LightArray.source_read (μ := μ) (f := fun i => e.eval (fun _ => f i)) hsep hj
    have hv := hread j hj
    have hmem : wrote μ dst (fun i => e.eval (fun _ => f i)) j (src + j) = f j := hr.trans hv
    have hf' := abs_le.mp (hf j hj)
    have hsa : ∀ i, (atoms i).Safe lim σ := by
      intro i
      dsimp [σ, atoms]
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, hv, hmem] <;> omega)
    have hva : ∀ i, (atoms i).val σ = f j := by
      intro i
      dsimp [σ, atoms]
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, hv, hmem] <;> omega)
    have hbounds : ∀ i, |(atoms i).val σ| ≤ (U : ℤ) := by intro i; rw [hva]; exact hf j hj
    refine ⟨Circuit.compile_safe e atoms σ (Int.natCast_nonneg U) hsa hbounds he, ?_⟩
    rw [Circuit.compile_val]
    apply congrArg (fun x : ℕ → ℤ => e.eval x)
    funext i
    exact hva i
end ThreeSum.LightTernaryScalarChannel
