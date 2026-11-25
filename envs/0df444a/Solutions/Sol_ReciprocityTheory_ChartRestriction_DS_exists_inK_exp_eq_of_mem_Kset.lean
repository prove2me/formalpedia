-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.exists_inK_exp_eq_of_mem_Kset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:42:30.097028+00:00
-- url     : https://prove2.me/submissions/eb4a299c-e4d4-49a3-9677-9753c233a2cf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ExistsExpEqOfMemKset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kExp_Jm_conjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
open scoped Matrix.Norms.L2Operator
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : ∃ Z, inK ε Z ∧ NormedSpace.exp Z = k := by
  obtain ⟨hu, hc⟩ := hk
  have hfin := Matrix.finite_spectrum k
  have hN : IsStarNormal k := ⟨by
    rw [Commute, SemiconjBy, Unitary.star_mul_self_of_mem hu, Unitary.mul_star_self_of_mem hu]⟩
  have hcl : ContinuousOn Complex.log (spectrum ℂ k) := hfin.continuousOn _

  have hcirc : ∀ z ∈ spectrum ℂ k, ‖z‖ = 1 := fun z hz => by
    simpa using spectrum.subset_circle_of_unitary (𝕜 := ℂ) hu hz

  have hJ : Commute k (Jm ε) := hc
  have hJs : Commute (star k) (Jm ε) := by
    have h := congrArg star hc
    simp only [star_mul, Matrix.star_eq_conjTranspose, kExp_Jm_conjTranspose] at h
    exact h.symm
  have hZJ : Commute (cfc Complex.log k) (Jm ε) := Commute.cfc hJ hJs _
  have hstar : star (cfc Complex.log k) = -cfc Complex.log k := by
    rw [← cfc_star, ← cfc_neg]
    refine cfc_congr fun z hz => ?_
    have h1 := hcirc z hz
    apply Complex.ext <;> simp [Complex.log_re, h1]
  refine ⟨cfc Complex.log k, ⟨?_, hZJ.eq⟩, ?_⟩
  · unfold inG
    rw [← Matrix.star_eq_conjTranspose, hstar, neg_mul, hZJ.eq]
    exact neg_add_cancel _
  · rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ) (a := cfc Complex.log k) (cfc_predicate _ _),
      ← cfc_comp NormedSpace.exp Complex.log k hN ((hfin.image _).continuousOn _) hcl]
    conv_rhs => rw [← cfc_id ℂ k hN]
    refine cfc_congr fun z hz => ?_
    have hz0 : z ≠ 0 := by
      intro h
      have h1 := hcirc z hz
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    simp only [Function.comp_apply, id]
    rw [← Complex.exp_eq_exp_ℂ, Complex.exp_log hz0]
end ReciprocityTheory.ChartRestriction.DS
