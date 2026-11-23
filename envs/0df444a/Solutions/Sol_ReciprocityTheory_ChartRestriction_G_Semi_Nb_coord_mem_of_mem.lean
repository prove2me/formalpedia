-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Nb.coord_mem_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:15.118811+00:00
-- url     : https://prove2.me/submissions/23b91b6b-6521-45f1-bdf2-0135810970ce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableCompleteSplit
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Tower
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open IsLocalRing Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Semi.Nb
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.Semi.Nb
theorem _root_.solution (b : Module.Basis ι R M) (J : Ideal R) {x : M}
    (hx : x ∈ (J • ⊤ : Submodule R M)) (i : ι) : b.repr x i ∈ J := by
  have key : (J • ⊤ : Submodule R M) ≤ Submodule.comap (b.coord i) J := by
    rw [Submodule.smul_le]
    intro r hr m _
    rw [Submodule.mem_comap, map_smul, smul_eq_mul]
    exact J.mul_mem_right _ hr
  simpa using key hx
end ReciprocityTheory.ChartRestriction.G.Semi.Nb
