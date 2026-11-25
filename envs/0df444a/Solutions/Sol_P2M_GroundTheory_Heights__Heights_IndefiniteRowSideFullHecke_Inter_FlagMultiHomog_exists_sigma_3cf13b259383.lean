-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_exists_sigma_3cf13b259383
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:42:11.762478+00:00
-- url     : https://prove2.me/submissions/d85917d6-b84d-480d-b498-7f8cefefbecf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_ker_zScale_4fc9ec0352a7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {N1 n : ℕ}
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
theorem _root_.solution (P : Ideal (MRing ι)) [P.IsPrime] (hP : IsMultiHomogIdeal P) (n : ℕ) :
    ∃ σ : FnField P →+* OmegaF P n, ∀ p : Σ k, ι k,
      σ (genPt P p) = iota P n (genPt P p) * lam P n (Sum.inl p.1) := by
  have hker := ker_zScale P hP n
  let g : MRing ι ⧸ P →+* LRing P n := Ideal.Quotient.lift P (zScale P n) fun f hf => by
    rw [← RingHom.mem_ker, hker]; exact hf
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hker, RingHom.mem_ker]
    simpa [g] using ha
  have hg' : Function.Injective ((algebraMap (LRing P n) (OmegaF P n)).comp g) := by
    rw [RingHom.coe_comp]
    exact (IsFractionRing.injective (LRing P n) (OmegaF P n)).comp hg
  refine ⟨IsFractionRing.lift hg', fun p => ?_⟩
  rw [genPt, IsFractionRing.lift_algebraMap]
  simp [g, zScale, iota, lam, genPt]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
