-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.actionKernelUnitaryRepresentation_kerFun_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/60387f51-f038-41f2-afb3-1086438eb6f7

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_ofKernel_kerFun_one_eq_coe_single

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) (i : I) :
    actionKernelUnitaryRepresentation K ρ hinv a
      (RKHS.kerFun (RKHS.OfKernel (scalarOperatorKernel K)) i
        (1 : ℂ)) =
      RKHS.kerFun (RKHS.OfKernel (scalarOperatorKernel K))
        (ρ a i) (1 : ℂ) := by
  rw [ofKernel_kerFun_one_eq_coe_single
    (scalarOperatorKernel K) i,
    ofKernel_kerFun_one_eq_coe_single
      (scalarOperatorKernel K) (ρ a i)]
  change
    actionKernelTranslationMap K ρ hinv a
      ((Finsupp.single (i, (1 : ℂ)) (1 : ℂ) :
        RKHS.H₀ (scalarOperatorKernel K)) :
          RKHS.OfKernel (scalarOperatorKernel K)) = _
  rw [actionKernelTranslationMap_coe]
  simp [actionPreKernelTranslation]
end SoficGroups.KunRootedIndicatorCrossing
