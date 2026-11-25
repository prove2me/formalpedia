-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.segreGrading_algebraMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:27.711967+00:00
-- url     : https://prove2.me/submissions/b456b803-26f7-4590-b8f5-33db0fa4b618

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable [Nonempty K]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    letI := segreGraded hP
    Function.Surjective (algebraMap ℂ (segreGrading P 0)) := by
  letI := segreGraded hP
  rintro ⟨x, hx⟩
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.1 hx
  have hq' : q.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 q).1 hq
  refine ⟨q.coeff 0, ?_⟩
  apply Subtype.ext
  rw [SetLike.GradeZero.coe_algebraMap]
  by_cases h0 : q = 0
  · subst h0
    simp
  · have hC : q = C (q.coeff 0) := totalDegree_eq_zero_iff_eq_C.1 (hq'.totalDegree h0)
    show _ = (Ideal.Quotient.mkₐ ℂ (segreIdeal P)) q
    nth_rewrite 2 [hC]
    exact ((Ideal.Quotient.mkₐ ℂ _).commutes (q.coeff 0)).symm
end ReciprocityTheory.AnForm.R
