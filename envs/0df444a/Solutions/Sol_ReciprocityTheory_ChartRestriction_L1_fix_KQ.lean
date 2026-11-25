-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.fix_KQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:36:54.617701+00:00
-- url     : https://prove2.me/submissions/afcfe3a9-5c85-4bed-bc24-72b22da64bc1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane Pointwise
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {d l : ℕ} [Fact l.Prime] (e : Om d →+* PadicAlgCl l)
    (ρ : PadicAlgCl l ≃ₐ[IntermediateField.adjoin ℚ_[l] {e (algebraMap (KQ d) (Om d) (sqK d))}] PadicAlgCl l)
    (k : KQ d) : ρ (e (algebraMap (KQ d) (Om d) k)) = e (algebraMap (KQ d) (Om d) k) := by
  let φ₁ : KQ d →ₐ[ℚ] PadicAlgCl l := (e.comp (algebraMap (KQ d) (Om d))).toRatAlgHom
  let φ₂ : KQ d →ₐ[ℚ] PadicAlgCl l :=
    ((ρ : PadicAlgCl l →+* PadicAlgCl l).comp (e.comp (algebraMap (KQ d) (Om d)))).toRatAlgHom
  have h : φ₂ = φ₁ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (s := {sqD d}) rfl ?_
    intro x hx
    have hx' : x = sqD d := hx
    subst hx'
    have hm : e (algebraMap (KQ d) (Om d) (sqK d)) ∈
        IntermediateField.adjoin ℚ_[l] {e (algebraMap (KQ d) (Om d) (sqK d))} :=
      IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
    exact ρ.commutes ⟨_, hm⟩
  exact DFunLike.congr_fun h k
end ReciprocityTheory.ChartRestriction.L1
