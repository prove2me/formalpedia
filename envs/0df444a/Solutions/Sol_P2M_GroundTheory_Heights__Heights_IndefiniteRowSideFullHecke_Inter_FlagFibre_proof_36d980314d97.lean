-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagFibre_proof_36d980314d97
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:03:53.02851+00:00
-- url     : https://prove2.me/submissions/9be9b59a-783e-49ba-8d62-5c83eaf73aac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RelBaseChangeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreDeg_flag_5a65a79bb332
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagCompound_injective_3a567feaef6e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreIdeal_flag_0a699e7696d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_charZero_fnField_2bb6fd8394c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagIdealOver_map_6cb9b06c5951
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagIdealOver_isPrime_1a971e341cc7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagIdealQ_eq_9f0d0547a8e4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_multAt_self


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace FlagFibre
theorem _root_.solution
    (hEU : ∀ (K : Type) [Fintype K] (F : Type) [Field F] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hBC : ∀ (K : Type) [Fintype K] (F F' : Type) [Field F] [Field F'] [Algebra F F'] (ι : K → Type)
      [∀ k, Fintype (ι k)], BaseChangeStatement F F' ι)
    (hLin : LinEmbed.Statement) (hDim : FlagDim.Statement) (hRel : RelBaseChange.Statement) :
    FlagFibre.Statement := by
  intro K _ ι _ N1 t n P d c m B hP _ hB J₀ hJ₀
  have : P.IsPrime := hP.2.1.1
  have : CharZero (FnField P) := charZero_fnField P hP.2.2.1
  obtain ⟨J, hJ, -⟩ := hEU _ (FnField P) (fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl)
  obtain ⟨J₁, hJ₁, -⟩ := hEU _ (FnField P) (PluckerBlocks n n)
  refine ⟨J, hJ, fun a => ?_⟩
  have hfib : fibreIdeal Sum.inl (flagGenFibre P hP.2.1.1 B) =
      (flagIdealOver (FnField P) n).comap
        (blockLinSubst (flagFibreBlocksEquiv (K := K)) (flagCompound (ι := ι) B)).toRingHom :=
    fibreIdeal_flag P B
  have hdeg : (fun j => fibreDeg Sum.inl (a j)) =
      fun j => (fun j' => a j (Sum.inr j')) ∘ (flagFibreBlocksEquiv (K := K) (n := n)) :=
    funext fun j => fibreDeg_flag (a j)
  have h1 : J (fibreIdeal Sum.inl (flagGenFibre P hP.2.1.1 B)) (flagDim n) (fun j => fibreDeg Sum.inl (a j)) =
      J₁ (flagIdealOver (FnField P) n) (flagDim n) (fun j j' => a j (Sum.inr j')) := by
    rw [hfib, hdeg]
    exact hLin (FnField P) (Fin (n - 1)) _ (PluckerBlocks n n) _ flagFibreBlocksEquiv (flagCompound B)
      (flagCompound_injective B hB.1) J₁ J hJ₁ hJ _ _ _ (hDim _ n)
  rw [h1]
  have h2 := hBC _ ℚ (FnField P) (PluckerBlocks n n) J₀ J₁ hJ₀ hJ₁ (flagIdealQ n) (flagDim n)
    (fun j j' => a j (Sum.inr j')) (hDim ℚ n)
  have := flagIdealOver_isPrime (FnField P) n
  rw [h2, flagIdealQ_eq, flagIdealOver_map hRel, Ideal.minimalPrimes_eq_subsingleton_self,
    finsum_mem_singleton, inh_multAt_self]
  simp
end FlagFibre
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
