-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ringKrullDim_le_of_forall_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:58.690723+00:00
-- url     : https://prove2.me/submissions/5e28efe7-f2de-4abf-90d5-69929aed7391

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial Algebra
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {A : Type*} [CommRing A] (d : WithBot ℕ∞)
    (h : ∀ P : Ideal A, P.IsPrime → ringKrullDim (A ⧸ P) ≤ d) : ringKrullDim A ≤ d := by
  refine iSup_le fun p => ?_
  let P : Ideal A := (p.toFun 0).asIdeal
  have hP : P.IsPrime := (p.toFun 0).isPrime
  have hmem : ∀ i, p.toFun i ∈ PrimeSpectrum.zeroLocus (P : Set A) := fun i =>
    (PrimeSpectrum.mem_zeroLocus _ _).2
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 (p.monotone (Fin.zero_le i)))
  let q : LTSeries (PrimeSpectrum.zeroLocus (P : Set A)) :=
    { length := p.length, toFun := fun i => ⟨p.toFun i, hmem i⟩, step := fun i => p.step i }
  exact (Order.LTSeries.length_le_krullDim q).trans
    ((ringKrullDim_quotient P).symm.le.trans (h P hP))
end ReciprocityTheory.AnForm.R
