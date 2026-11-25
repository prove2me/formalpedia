-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Nil.Asm.bez2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:09:58.782419+00:00
-- url     : https://prove2.me/submissions/da214b64-fe40-492e-8550-5ede574d61dd

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_NilpotentHypotheses_AevalProdLinearFactors
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_IntegralParts_BezoutHypotheses_Bez2
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Asm_aeval_mem
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Asm_aeval_prod_lin
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Asm_aeval_prod_linear_factors
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Asm_isCoprime_lin
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Asm_isCoprime_list_prod_left
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Asm_isCoprime_list_prod_right
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Asm_pow_mem
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Asm_pow_mul_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial PositivityTheory.RgUd.T.Nil.Asm
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Asm
namespace PositivityTheory.RgUd.TP.Nil.Asm
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] (K : Submodule ℂ M) (R R' : M →ₗ[ℂ] M)
    (hRR : R ∘ₗ R' = LinearMap.id) (hR'R : R' ∘ₗ R = LinearMap.id) (hK : ∀ m ∈ K, R m ∈ K) (c : ℝ) (hc : 1 < c)
    (d : ℝ) (a b : List ℝ) (hab : ∀ x ∈ a, ∀ y ∈ b, y + x ≠ d) (ζ : M)
    (h1 : ((b.map fun y => R - ((c ^ y : ℝ) : ℂ) • LinearMap.id).prod : Module.End ℂ M) ζ ∈ K)
    (h2 : ((a.map fun x => ((c ^ d : ℝ) : ℂ) • R' - ((c ^ x : ℝ) : ℂ) • LinearMap.id).prod : Module.End ℂ M) ζ ∈ K) :
    ζ ∈ K := by
  set β : ℂ := ((c ^ d : ℝ) : ℂ)
  set γ : ℝ → ℂ := fun x => ((c ^ x : ℝ) : ℂ)
  have hRR' : (R : Module.End ℂ M) * R' = 1 := hRR
  have hR'R' : (R' : Module.End ℂ M) * R = 1 := hR'R
  have hQ : ((a.map fun x => β • (1 : Module.End ℂ M) - γ x • R).prod : Module.End ℂ M) ζ ∈ K := by
    rw [← pow_mul_prod R R' hRR' hR'R' β γ a, Module.End.mul_apply]
    exact pow_mem K R hK _ _ h2
  have hc0 : 0 < c := by linarith
  have hcop : IsCoprime ((b.map fun y => X - C (γ y)).prod) ((a.map fun x => C β - C (γ x) * X).prod) := by
    refine isCoprime_list_prod_left _ _ b fun y hy => isCoprime_list_prod_right _ _ a fun x hx => ?_
    refine isCoprime_lin (γ y) β (γ x) ?_
    intro h0
    have h0' : β = γ x * γ y := sub_eq_zero.1 h0
    have : (c ^ d : ℝ) = c ^ x * c ^ y := by
      simp only [β, γ] at h0'
      exact_mod_cast h0'
    rw [← Real.rpow_add hc0] at this
    have hlog := congrArg Real.log this
    rw [Real.log_rpow hc0, Real.log_rpow hc0] at hlog
    have hl : 0 < Real.log c := Real.log_pos hc
    have hd : d = x + y := mul_right_cancel₀ hl.ne' hlog
    exact hab x hx y hy (by linarith)
  obtain ⟨u, v, huv⟩ := hcop
  have key := congrArg (fun p => (aeval (R : Module.End ℂ M) p) ζ) huv
  simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] at key
  rw [← key]
  refine K.add_mem (aeval_mem K R hK u _ ?_) (aeval_mem K R hK v _ ?_)
  · rw [aeval_prod_lin R γ b]; exact h1
  · rw [aeval_prod_linear_factors R β γ a]
    convert hQ using 3
    refine List.map_congr_left fun x _ => ?_
    rfl
end PositivityTheory.RgUd.TP.Nil.Asm
