-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.toCot_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:11.432099+00:00
-- url     : https://prove2.me/submissions/090832f1-880c-4bf5-a2de-dd922d5484d2

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartB
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_algebraMap_eq_psi
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_le_ptIdeal_of_nontrivial
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_psi_mem_sq
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_taylor


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
theorem _root_.solution {a : MvPolynomial (Fin n) ℂ} (ha : a ∈ ptI p)
    (hm : psi p K a ∈ maximalIdeal (locR K p)) :
    (maximalIdeal (locR K p)).toCotangent ⟨psi p K a, hm⟩ = Phi p K (gradP p a) := by
  have hK : K ≤ ptI p := le_ptIdeal_of_nontrivial (K := K) (p := p)
  have ha0 : eval p a = 0 := by rw [ptI, RingHom.mem_ker] at ha; exact ha
  have ht := taylor p a
  rw [ha0, C_0, sub_zero] at ht
  have hsq := psi_mem_sq (K := K) (p := p) hK ht
  have hmem : ∀ i, psi p K (C (gradP p a i)) * psi p K (X i - C (p i)) ∈ maximalIdeal (locR K p) :=
    fun i => (maximalIdeal (locR K p)).mul_mem_left _ (lin_mem_max p K i)
  have e : Phi p K (gradP p a) = (maximalIdeal (locR K p)).toCotangent
      ⟨∑ i, psi p K (C (gradP p a i)) * psi p K (X i - C (p i)),
        (maximalIdeal (locR K p)).sum_mem fun i _ => hmem i⟩ := by
    have e2 : (⟨∑ i, psi p K (C (gradP p a i)) * psi p K (X i - C (p i)),
        (maximalIdeal (locR K p)).sum_mem fun i _ => hmem i⟩ : maximalIdeal (locR K p)) =
        ∑ i, psi p K (C (gradP p a i)) • (⟨psi p K (X i - C (p i)), lin_mem_max p K i⟩ :
          maximalIdeal (locR K p)) := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, smul_eq_mul]
    rw [e2, map_sum]
    simp only [Phi, LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← algebraMap_eq_psi, algebraMap_smul]
  rw [e, Ideal.toCotangent_eq]
  simpa [map_sub, map_sum, map_mul] using hsq
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
