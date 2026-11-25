-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_component_mem_ae9ca3608469
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:22:46.556719+00:00
-- url     : https://prove2.me/submissions/dcbd7d9c-5b46-409b-9773-b856bab5b1c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_eval_one_scaleHom_ff58bea7d832
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_scaleHom_component_a5be03e42ee5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_exists_theta_3e01e951f8e3

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
theorem _root_.solution (P : Ideal (MRing ι)) [P.IsPrime] {t : ℕ} (c : Fin t → Fin N1 → MRing ι)
    (m : K → ℕ) (B : Matrix (Fin n) (Fin N1) (FnField P)) (hP : IsMultiHomogIdeal P)
    (hc : ∀ a j, IsMultiHomog (c a j) m) (hB : IsKerBasis P c B) (f : MRing (FlagBundleBlocks ι N1 n))
    (hf : f ∈ flagIdeal P B) (b : K ⊕ Fin (n - 1) → ℕ) :
    weightedHomogeneousComponent (NumbersDVR.blockWeight (FlagBundleBlocks ι N1 n)) b f ∈ flagIdeal P B := by
  obtain ⟨θ, hθ⟩ := exists_theta P c m B hP hc hB
  have h0 : scaleHom (L := K ⊕ Fin (n - 1)) (flagMap P B) f = 0 := by
    apply IsFractionRing.injective (LRing P n) (OmegaF P n)
    rw [map_zero, ← RingHom.comp_apply, ← hθ, RingHom.comp_apply, RingHom.mem_ker.1 hf, map_zero]
  rw [flagIdeal, RingHom.mem_ker, ← eval_one_scaleHom (L := K ⊕ Fin (n - 1)) (flagMap P B),
    scaleHom_component, h0, map_zero, map_zero]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
