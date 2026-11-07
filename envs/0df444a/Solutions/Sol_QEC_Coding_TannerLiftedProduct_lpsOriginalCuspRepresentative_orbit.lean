-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspRepresentative_orbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:36:34.093193+00:00
-- url     : https://prove2.me/submissions/d9e3a7f2-5feb-49d7-a0e3-4745822c68f7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    lpsOriginalCuspOrbit N (lpsOriginalCuspRepresentative N c)=c :=
  Classical.choose_spec (lpsOriginalCuspOrbit_surjective N c)
end QEC.Coding.TannerLiftedProduct
