-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.ker_Phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:39:28.972451+00:00
-- url     : https://prove2.me/submissions/b2381c7f-21f8-46b0-a890-1bdced49c77c

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartB
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_toCot_psi
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_exists_of_psi_mem_sq
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_C
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_add
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_eq_zero_of_mem_sq
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_lin
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_mul
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_sum
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_le_ptIdeal_of_nontrivial
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_psi_mem_max_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt
open MvPolynomial IsLocalRing
noncomputable section
variable {n : ℕ} (p : Fin n → ℂ) (K : Ideal (MvPolynomial (Fin n) ℂ)) [IsLocalRing (locR K p)]
namespace ReciprocityTheory.AnForm.R.JacobianCriterionAlt
theorem _root_.solution : LinearMap.ker (Phi p K) = jacS K p := by
  have hK : K ≤ ptI p := le_ptIdeal_of_nontrivial (K := K) (p := p)
  apply le_antisymm
  · intro c hc
    rw [LinearMap.mem_ker] at hc
    set l : MvPolynomial (Fin n) ℂ := ∑ i, C (c i) * (X i - C (p i)) with hl
    have hl0 : eval p l = 0 := by simp [hl]
    have hlI : l ∈ ptI p := by rw [ptI, RingHom.mem_ker]; exact hl0
    have hgl : gradP p l = c := by
      rw [hl, grad_sum]
      ext j
      simp [grad_mul, grad_C, grad_lin, Pi.single_apply, Finset.sum_apply]
    have hpl : psi p K l ∈ maximalIdeal (locR K p) :=
      (psi_mem_max_iff (K := K) (p := p) hK l).mpr hlI
    have h0 : (maximalIdeal (locR K p)).toCotangent ⟨psi p K l, hpl⟩ = 0 := by
      rw [toCot_psi p K hlI hpl, hgl, hc]
    rw [Ideal.toCotangent_eq_zero] at h0
    obtain ⟨s, hs, hsl⟩ := exists_of_psi_mem_sq (K := K) (p := p) hK h0
    obtain ⟨q, hq, k, hk, hqk⟩ := Submodule.mem_sup.mp hsl
    have hg : gradP p (s * l) = eval p s • c := by
      rw [grad_mul, hgl, hl0, zero_smul, add_zero]
    have hg2 : gradP p (s * l) = gradP p k := by
      rw [← hqk, grad_add, grad_eq_zero_of_mem_sq p hq, zero_add]
    have hs0 : eval p s ≠ 0 := fun h => hs (by rw [ptI, RingHom.mem_ker]; exact h)
    have hmemk : gradP p k ∈ jacS K p := Submodule.subset_span ⟨k, hk, rfl⟩
    have hc' : c = (eval p s)⁻¹ • gradP p k := by
      rw [← hg2, hg, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [hc']
    exact Submodule.smul_mem _ _ hmemk
  · rw [jacS, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hfI := hK hf
    have hpf : psi p K f ∈ maximalIdeal (locR K p) := (psi_mem_max_iff (K := K) (p := p) hK f).mpr hfI
    rw [← toCot_psi p K hfI hpf, Ideal.toCotangent_eq_zero]
    have h0 : psi p K f = 0 := by
      simp only [psi, RingHom.comp_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hf)
    show psi p K f ∈ maximalIdeal (locR K p) ^ 2
    rw [h0]
    exact zero_mem _
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
