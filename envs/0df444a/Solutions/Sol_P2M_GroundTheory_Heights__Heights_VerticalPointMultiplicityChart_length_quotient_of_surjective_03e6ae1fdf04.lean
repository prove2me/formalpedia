-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPointMultiplicityChart_length_quotient_of_surjective_03e6ae1fdf04
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:29:44.406794+00:00
-- url     : https://prove2.me/submissions/56d14abf-86d6-4eee-827a-b441b74ee011

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointResidue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointMultChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.VerticalPointMultiplicityChart
namespace GroundTheory.Heights₂.Heights.VerticalPointMultiplicityChart
theorem _root_.solution {A N : Type*} [CommRing A] [CommRing N] (Φ : A →+* N)
    (hΦ : Function.Surjective Φ) (J : Ideal A) (hJ : RingHom.ker Φ ≤ J) :
    Module.length A (A ⧸ J) = Module.length N (N ⧸ J.map Φ) := by
  let _ := Φ.toAlgebra
  have hs : Function.Surjective (algebraMap A (N ⧸ J.map Φ)) :=
    (Ideal.Quotient.mk_surjective).comp hΦ
  have hker : RingHom.ker (Algebra.ofId A (N ⧸ J.map Φ)) = J := by
    ext x
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (Φ x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hΦ,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hJ]
  let e := (Ideal.quotientEquivAlgOfEq A hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A (N ⧸ J.map Φ)) hs)
  rw [e.toLinearEquiv.length_eq]
  exact Module.length_eq_of_surjective hΦ
end GroundTheory.Heights₂.Heights.VerticalPointMultiplicityChart
