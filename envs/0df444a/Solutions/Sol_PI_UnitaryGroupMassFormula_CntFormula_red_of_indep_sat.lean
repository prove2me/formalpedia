-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.red_of_indep_sat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:44:27.264234+00:00
-- url     : https://prove2.me/submissions/ffdabfbf-87db-412e-a796-96434898ca3a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_DensGSDvr
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_liftF_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_resF_liftF
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_resF_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_resF_sum_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_dvd_of_resF_eq_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_resF_irr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula
open Classical ValuativeRel
variable (F : Type) [Field F] [ValuativeRel F]
variable {F}
namespace PI.UnitaryGroupMassFormula.CntFormula
theorem _root_.solution [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hind : LinearIndependent F X) (hsat : SatF F X) : LinearIndependent 𝓀[F] (redM F X) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  obtain ⟨d, hdm, hres⟩ : ∃ d : ι → F, (∀ i, d i ∈ 𝒪[F]) ∧ ∀ i, resF F (d i) = a i :=
    ⟨fun i => liftF F (a i), fun i => liftF_mem F _, fun i => resF_liftF F _⟩
  have hcomp : ∀ k, (∑ i, d i • X i) k = ∑ i, d i * X i k := fun k => by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hmem : ∀ k, (∑ i, d i • X i) k ∈ 𝒪[F] := fun k => by
    rw [hcomp]
    exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hdm i) (hX i k)
  have hr0 : ∀ k, resF F ((∑ i, d i • X i) k) = 0 := fun k => by
    have h := resF_sum_mul F d (fun i => X i k) hdm (fun i => hX i k)
    rw [hcomp, h]
    simp only [hres]
    have h2 := congrFun ha k
    simpa [Finset.sum_apply, redM] using h2
  choose w hw using fun k => dvd_of_resF_eq_zero F hϖ (hmem k) (hr0 k)
  have hϖ0 : (ϖ : F) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  obtain ⟨c', hc'm, hc'⟩ := hsat (fun k => (w k : F)) (fun k => (w k).2)
    ⟨fun i => d i / ϖ, by
      funext k
      have e := hw k
      rw [hcomp] at e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp_rw [div_mul_eq_mul_div]
      rw [← Finset.sum_div, e]
      field_simp⟩
  have hzero : ∑ i, (d i - ϖ * c' i) • X i = 0 := by
    funext k
    have e1 := congrFun hc' k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e1
    have e2 := hw k
    rw [hcomp] at e2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      Pi.zero_apply]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, e1, e2, sub_self]
  have hdi := (Fintype.linearIndependent_iff.1 hind) _ hzero i
  rw [← hres i, sub_eq_zero.1 hdi, resF_mul F ϖ.2 (hc'm i), resF_irr F hϖ, zero_mul]
end PI.UnitaryGroupMassFormula.CntFormula
