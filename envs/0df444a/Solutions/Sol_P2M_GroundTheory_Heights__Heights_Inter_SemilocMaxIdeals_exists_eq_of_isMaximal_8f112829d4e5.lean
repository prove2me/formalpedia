-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_exists_eq_of_isMaximal_8f112829d4e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:14:28.66899+00:00
-- url     : https://prove2.me/submissions/885c90a8-07c9-4c2a-a2fb-3c4910e94136

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFibreOverFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocMaxIdeals
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_exists_frac_7b843acc1ee2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_mem_semiMaxIdeal_iff_9811936ba746
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_isUnit_of_83bfca58eca3

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
open regularityLocalFlat_holds
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (P : Ideal (MRing ι)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι)))
variable {P 𝒲}
namespace GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
theorem _root_.solution (hfin : 𝒲.Finite) (h𝒲 : ∀ W ∈ 𝒲, IsMultiProjPrime W ∧ P ≤ W)
    (hne : 𝒲.Nonempty) (M : Ideal (semiLocRing P 𝒲)) (hM : M.IsMaximal) :
    ∃ (W' : Ideal (MRing ι)) (hW' : W' ∈ 𝒲), ∀ [IsLocalRing (locRing P W')], M = semiMaxIdeal P 𝒲 W' hW' := by
  classical
  have : Fintype 𝒲 := hfin.fintype
  obtain ⟨W0, hW0⟩ := hne
  let f : 𝒲 → Ideal (semiLocRing P 𝒲) := fun W =>
    have := (h𝒲 W W.2).1.1
    have := isLocalRing (h𝒲 W W.2).2
    semiMaxIdeal P 𝒲 W W.2
  have hcov : (M : Set (semiLocRing P 𝒲)) ⊆ ⋃ i ∈ ((Finset.univ : Finset 𝒲) : Set 𝒲), (f i : Set _) := by
    intro b hbM
    obtain ⟨u, w, a, hu, hw, hwP, hwW, hb⟩ := exists_frac P 𝒲 (fun W hW => (h𝒲 W hW).1.1) b
    by_contra hnot
    have huW : ∀ W ∈ 𝒲, u ∉ W := by
      intro W hW huW
      have := (h𝒲 W hW).1.1
      have := isLocalRing (h𝒲 W hW).2
      refine hnot (Set.mem_biUnion (x := (⟨W, hW⟩ : 𝒲)) (Finset.mem_coe.mpr (Finset.mem_univ _)) ?_)
      exact (mem_semiMaxIdeal_iff P 𝒲 hW (h𝒲 W hW).2 b hu hw (hwW W hW) hb).mpr huW
    have huP : u ∉ P := fun h => huW W0 hW0 ((h𝒲 W0 hW0).2 h)
    exact hM.ne_top (Ideal.eq_top_of_isUnit_mem _ hbM (isUnit_of P 𝒲 b hu hw huP huW hb))
  obtain ⟨⟨W', hW'⟩, -, hle⟩ := (Ideal.subset_union_prime (⟨W0, hW0⟩ : 𝒲) (⟨W0, hW0⟩ : 𝒲)
    (fun i _ _ _ => by dsimp only [f]; infer_instance)).mp hcov
  refine ⟨W', hW', ?_⟩
  intro _
  have := (h𝒲 W' hW').1.1
  exact hM.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
end GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
