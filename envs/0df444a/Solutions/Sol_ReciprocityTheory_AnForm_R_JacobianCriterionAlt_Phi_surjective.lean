-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.Phi_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:39:26.429726+00:00
-- url     : https://prove2.me/submissions/533c7471-2c64-41e8-a5a9-22b7932f5870

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartB
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_algebraMap_eq_psi
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_toCot_psi
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_evRing_psi
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_exists_of_mem_max
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_ker_evRing
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
theorem _root_.solution : Function.Surjective (Phi p K) := by
  have hK : K ≤ ptI p := le_ptIdeal_of_nontrivial (K := K) (p := p)
  intro v
  obtain ⟨⟨x, hx⟩, rfl⟩ := (maximalIdeal (locR K p)).toCotangent_surjective v
  obtain ⟨a, s, ha, hs, hxs⟩ := exists_of_mem_max (K := K) (p := p) hK hx
  have hsu : IsUnit (psi p K s) := by
    by_contra h
    exact hs ((psi_mem_max_iff (K := K) (p := p) hK s).mp ((IsLocalRing.mem_maximalIdeal _).mpr h))
  obtain ⟨u, hu⟩ := hsu
  have hpa : psi p K a ∈ maximalIdeal (locR K p) := (psi_mem_max_iff (K := K) (p := p) hK a).mpr ha
  have hxe : x = (↑u⁻¹ : locR K p) * psi p K a := by
    rw [← hxs, ← hu, mul_comm x, ← mul_assoc, Units.inv_mul, one_mul]
  have hr : (↑u⁻¹ : locR K p) - algebraMap ℂ (locR K p) (evRing K hK (↑u⁻¹ : locR K p)) ∈
      maximalIdeal (locR K p) := by
    rw [← ker_evRing (K := K) (p := p) hK, RingHom.mem_ker, map_sub, algebraMap_eq_psi, evRing_psi,
      eval_C, sub_self]
  refine ⟨(evRing K hK (↑u⁻¹ : locR K p)) • gradP p a, ?_⟩
  rw [map_smul, ← toCot_psi p K ha hpa, ← algebraMap_smul (locR K p), ← map_smul, Ideal.toCotangent_eq]
  simp only [SetLike.val_smul, smul_eq_mul]
  rw [hxe, ← sub_mul, pow_two]
  exact Ideal.mul_mem_mul (by rw [← neg_sub]; exact neg_mem hr) hpa
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
