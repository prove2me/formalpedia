-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_exists_theta_3e01e951f8e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:53.206164+00:00
-- url     : https://prove2.me/submissions/6e801454-1e1d-4bc4-852a-d389c7b4ca17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_exists_sigma_3cf13b259383
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_exists_h_89290dbb5ca9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_minor_scale_7155d677fa78
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_prod_diagE_3155faff335d

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
theorem _root_.solution (P : Ideal (MRing ι)) [P.IsPrime] {t : ℕ} (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (hP : IsMultiHomogIdeal P)
    (hc : ∀ a j, IsMultiHomog (c a j) m) (hB : IsKerBasis P c B) :
    ∃ θ : TRing P n →+* OmegaF P n, θ.comp (flagMap P B) =
      (algebraMap (LRing P n) (OmegaF P n)).comp (scaleHom (flagMap P B)) := by
  obtain ⟨σ, hσ⟩ := exists_sigma P hP n
  obtain ⟨h, hh⟩ := exists_h P c m B hc hB σ hσ
  let TΩ : Matrix (Fin n) (Fin n) (OmegaF P n) :=
    (genMat (FnField P) n).map ((algebraMap (LRing P n) (OmegaF P n)).comp C)
  let D : Matrix (Fin n) (Fin n) (OmegaF P n) := Matrix.diagonal fun a => diagE P n a.1
  let θ : TRing P n →+* OmegaF P n := eval₂Hom σ fun ab => (D * TΩ * h) ab.1 ab.2
  refine ⟨θ, MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) ?_⟩
  rintro ⟨k | j, i⟩
  · simp [θ, flagMap, scaleHom, hσ, iota, lam]
  · have e1 : (genMat (FnField P) n).map θ = D * TΩ * h := by
      ext a b
      simp [θ, genMat]
    have e2 : (B.map C).map θ = B.map σ := by
      ext a b
      simp [θ]
    have e3 : (B.map C).map ((algebraMap (LRing P n) (OmegaF P n)).comp C) = B.map (iota P n) := by
      ext a b
      simp [iota]
    have e4 : ∏ a : Fin (j.1 + 1), diagE P n a.1 = lam P n (Sum.inr j) := by
      rw [Fin.prod_univ_eq_prod_range (fun i => diagE P n i), prod_diagE, lamN, dif_pos (by omega)]
    simp only [RingHom.comp_apply, scaleHom, coe_eval₂Hom, eval₂_X, map_mul, flagMap]
    refine (minor_scale θ ((algebraMap (LRing P n) (OmegaF P n)).comp C) (genMat (FnField P) n) (B.map C)
      (fun a => diagE P n a.1) h (B.map σ) e1 e2 (hh.trans e3.symm) j i).trans ?_
    rw [mul_comm]
    congr 1
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
