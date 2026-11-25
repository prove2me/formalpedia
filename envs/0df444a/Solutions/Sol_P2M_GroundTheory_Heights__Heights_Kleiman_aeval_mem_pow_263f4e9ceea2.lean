-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_aeval_mem_pow_263f4e9ceea2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:41:52.108843+00:00
-- url     : https://prove2.me/submissions/a31f5315-77bc-493d-8387-69f6001389b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountTopSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDegreeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountTop
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mul_pow_mem_pow_ef4744dee65c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (Q : SubSystem k x Ω) {r : ℕ} {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ Q.secs)
    (I : Chart x) {f : MvPolynomial (Fin (r + 1)) k} {n : ℕ} (hf : f.IsHomogeneous n) :
    aeval h f ∈ (Q.pow n).sub I := by
  have hI : ∀ l, h l ∈ Q.sub I := fun l =>
    (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp (hh l) I)
  have hprod : ∀ (α : Fin (r + 1) →₀ ℕ) (s : Finset (Fin (r + 1))),
      ∏ i ∈ s, h i ^ α i ∈ (Q.pow (∑ i ∈ s, α i)).sub I := by
    intro α s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty]
      exact one_mem_twistMod_zero (S := k) I
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, mul_comm, add_comm]
      exact mul_pow_mem_pow Q I ih (hI j) (α j)
  rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [aeval_monomial]
  have hdeg : ∑ i ∈ α.support, α i = n := by
    have := hf (mem_support_iff.mp hα)
    rw [Finsupp.weight_apply, Finsupp.sum] at this
    simpa using this
  have hmem := hprod α α.support
  rw [hdeg] at hmem
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  exact Submodule.smul_of_tower_mem _ _ hmem
end GroundTheory.Heights₂.Heights.Kleiman
