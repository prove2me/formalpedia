-- Prove2me | solution 1 for PI.WGB.fockF_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:05:26.626505+00:00
-- url     : https://prove2.me/submissions/96495354-b850-40bd-a64d-ab20424ccf60

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Theorems.Thm_PI_WGB_fockF_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)
namespace PI.WGB
theorem _root_.solution {σ : Type} (p p' q : MvPolynomial σ ℂ) :
    fockF (p + p') q = fockF p q + fockF p' q := by
  classical
  have hs : ∀ r : MvPolynomial σ ℂ, r.support ⊆ p.support ∪ p'.support →
      fockF r q = ∑ m ∈ p.support ∪ p'.support, r.coeff m * star (q.coeff m) * fct m :=
    fun r hr => fockF_eq_sum r q _ (fun m h1 _ => hr (MvPolynomial.mem_support_iff.mpr h1))
  rw [hs (p + p') MvPolynomial.support_add, hs p Finset.subset_union_left,
    hs p' Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring
end PI.WGB
