-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.irreducible_theta_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:43:49.22973+00:00
-- url     : https://prove2.me/submissions/829ae788-5a18-4e4c-9af0-05ebcce06124

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffPsiPNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_EvalOneBilinearSubstitution
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LinearSubstitution_iota_injective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
open MvPolynomial
variable {K : Type} [Field K] {D N : ℕ}
private theorem irreducible_rename_of_injective_height {α β : Type} [Fintype α] {f : α → β}
    (hf : Function.Injective f) {F : MvPolynomial α K} (hF : Irreducible F) :
    Irreducible (rename f F) := by
  have hP : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hF
  have h1 : rename f F = rename ((↑) : Set.range f → β) (renameEquiv K (Equiv.ofInjective f hf) F) := by
    rw [renameEquiv_apply, rename_rename]
    congr 1
  have h2 : Prime (renameEquiv K (Equiv.ofInjective f hf) F) := (MulEquiv.prime_iff _).mpr hP
  rw [h1]
  exact ((prime_rename_iff (Set.range f)).mpr h2).irreducible
end ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
open MvPolynomial
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
theorem _root_.solution (F : KTp K D N) (hF : Irreducible F) :
    Irreducible (theta (rename (iota (D := D) (N := N)) F)) :=
  (MulEquiv.irreducible_iff (theta (K := K) (D := D) (N := N))).mpr
    (irreducible_rename_of_injective_height iota_injective hF)
end ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
