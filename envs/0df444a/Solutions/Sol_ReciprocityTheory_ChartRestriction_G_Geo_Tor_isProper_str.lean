-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:22.752634+00:00
-- url     : https://prove2.me/submissions/5bf5bfe2-15a2-41be-a08c-3295a69227bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] MvPolynomial.gradedAlgebra
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (R : Type) [CommRing R] (N : ℕ) : IsProper (PSpace.str R N) := by
  haveI : IsScalarTower R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
      (MvPolynomial (Fin (N + 1)) R) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hf : Algebra.FiniteType ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
      (MvPolynomial (Fin (N + 1)) R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  have hP : IsProper (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) := by
    infer_instance

  have hbij : Function.Bijective
      (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)) := by
    constructor
    · intro a b hab
      have := congrArg Subtype.val hab
      exact MvPolynomial.C_injective _ _ this
    · rintro ⟨p, hp⟩
      rw [MvPolynomial.mem_homogeneousSubmodule] at hp
      have ht : p.totalDegree = 0 := Nat.le_zero.mp hp.totalDegree_le
      refine ⟨MvPolynomial.coeff 0 p, Subtype.ext ?_⟩
      exact ((MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp ht).symm
  haveI : IsIso (CommRingCat.ofHom
      (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0))) :=
    (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom
  unfold PSpace.str
  infer_instance
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
