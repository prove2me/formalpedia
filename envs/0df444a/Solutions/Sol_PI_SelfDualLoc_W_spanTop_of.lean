-- Prove2me | solution 1 for PI.SelfDualLoc.W.spanTop_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:33:16.3228+00:00
-- url     : https://prove2.me/submissions/902b5ae3-db17-4a64-861c-b438bf77f5a0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HformSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HvecApply
import Theorems.Thm_PI_SelfDualLoc_W_hvec_apply
import Theorems.Thm_PI_SelfDualLoc_W_hform_smul_left
import Theorems.Thm_PI_SelfDualLoc_W_hform_sum_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
open PI.SelfDualLoc
namespace PI.SelfDualLoc.W
theorem _root_.solution (hN : Nondeg) : SpanTop := by
  intro F E _ _ _ _ _ n σ J Lb T hfin hdual hT
  by_contra hne
  have hlt : Module.finrank E (Submodule.span E (Lb : Set (Fin n → E))) < n := by
    have h := Submodule.finrank_lt hne
    rwa [Module.finrank_fin_fun] at h
  let b := Module.finBasis E (Submodule.span E (Lb : Set (Fin n → E)))
  let x : Fin (Module.finrank E (Submodule.span E (Lb : Set (Fin n → E)))) → Fin n → E :=
    fun i => (b i : Fin n → E)
  have hker : LinearMap.ker (hvec (σ : E →+* E) J x) ≠ ⊥ := by
    intro hbot
    have h1 := LinearMap.finrank_range_add_finrank_ker (hvec (σ : E →+* E) J x)
    rw [hbot, finrank_bot, add_zero, Module.finrank_fin_fun] at h1
    have h2 := Submodule.finrank_le (LinearMap.range (hvec (σ : E →+* E) J x))
    rw [Module.finrank_fin_fun] at h2
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  apply hy0
  refine hN F E n σ J Lb T hfin hdual hT y fun z hz => ?_
  have hzV : z ∈ Submodule.span E (Lb : Set (Fin n → E)) := Submodule.subset_span hz
  have hz' : z = ∑ i, (b.repr ⟨z, hzV⟩ i) • x i := by
    have h := congrArg Subtype.val (b.sum_repr ⟨z, hzV⟩)
    rw [Submodule.coe_sum] at h
    exact h.symm
  rw [hz', hform_sum_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hform_smul_left]
  have hi : hform (σ : E →+* E) J (x i) y = 0 := by
    rw [← hvec_apply]
    exact congrFun (LinearMap.mem_ker.mp hy) i
  rw [hi, mul_zero]
end PI.SelfDualLoc.W
