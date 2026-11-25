-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.fockK_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:45.359376+00:00
-- url     : https://prove2.me/submissions/e517cfa3-fb69-432c-9104-be75303c0133

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivComm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_FK_der_fock
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_FK_op_id
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_FK_kopL_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC.FK
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution (hB : FockBasic) : FockK := by
  intro m n ε c hc
  have hc2 : (2 * c : ℂ) ≠ 0 := by
    have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    exact mul_ne_zero two_ne_zero this
  refine ⟨(2 * c : ℂ)⁻¹ * (c : ℂ) ^ 2, -(2 * c : ℂ)⁻¹, -((2 * c : ℂ)⁻¹ * c), (2 * c : ℂ)⁻¹ * c,
    -((2 * c : ℂ)⁻¹ * ((c : ℂ) * ∑ a, sgn ε a)), fun i j p => ?_⟩
  have hL := (hB m n c hc).1
  have hX := (hB m n c hc).2.2
  let L : PX m n →ₗ[ℂ] PX m n := hL.mk' (fock c)
  have eL : ∀ x, fock c x = L x := fun x => rfl
  have hd : ∀ k (q : PX m n), fock c (pderiv k q) = (2 * c : ℂ)⁻¹ • pderiv (sw k) (fock c q) := by
    intro k q
    rw [der_fock hB c hc, inv_smul_smul₀ hc2]
  have key : fock c (KopL ε i j p) = (2 * c : ℂ)⁻¹ •
      ((∑ a ∈ Finset.univ.filter (fun a => ε a = true), cr c (a, i, false) (pderiv (a, j, true) (fock c p))) -
        ∑ a ∈ Finset.univ.filter (fun a => ε a = false), cr c (a, j, true) (pderiv (a, i, false) (fock c p))) := by
    rw [kopL_apply, eL, map_sub, map_sum, map_sum, smul_sub, Finset.smul_sum, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← eL, hX, hd, map_smul]
      rfl
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← eL, hX, hd, map_smul]
      rfl
  rw [key, op_id]
  by_cases hij : i = j
  · simp only [hij, if_true]
    module
  · simp only [hij, if_false, zero_smul, sub_zero, add_zero]
    module
end PositivityTheory.Rg.Sw.LC
