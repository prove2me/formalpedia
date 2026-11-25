-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_injective_projHom_of_finite_5201a3ac092b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:53.617881+00:00
-- url     : https://prove2.me/submissions/a0467a37-6c1e-491a-b6fb-ee70a53b2b8b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial MeasureTheory Filter Topology Matrix
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hJ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety J d)
    (hfin : (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom.Finite) :
    Function.Injective (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A) := by
  have := hJ.isPrime
  let f := (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom
  let P := RingHom.ker f
  let g : MvPolynomial (Fin d) ℂ ⧸ P →+* MvPolynomial (Fin n) ℂ ⧸ J := RingHom.kerLift f
  have hgf : g.comp (Ideal.Quotient.mk P) = f :=
    RingHom.ext fun a => RingHom.kerLift_mk f a
  have hg_fin : g.Finite :=
    RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk P) (by rw [hgf]; exact hfin)
  let := g.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ ⧸ P) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ⟨hg_fin.to_isIntegral⟩
  have h1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤
      ringKrullDim (MvPolynomial (Fin d) ℂ ⧸ P) :=
    Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap _ _)) fun _ _ hpq =>
      Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin d) ℂ ⧸ P) hpq
  rw [hJ.dim] at h1
  have hd : ringKrullDim (MvPolynomial (Fin d) ℂ) = (d : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have haP : a ∈ P := ha
  have h2 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk P)
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero ha0)
    (Ideal.Quotient.eq_zero_iff_mem.mpr haP)
  rw [hd] at h2
  have h3 := (add_le_add_left h1 1).trans h2
  have h4 : d + 1 ≤ d := by exact_mod_cast h3
  omega
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
