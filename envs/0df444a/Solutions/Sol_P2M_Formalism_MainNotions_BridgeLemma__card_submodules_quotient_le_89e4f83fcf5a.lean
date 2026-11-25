-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__card_submodules_quotient_le_89e4f83fcf5a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:53:02.495285+00:00
-- url     : https://prove2.me/submissions/dba1f9d3-77fa-4c7b-8faa-e944226e3eb2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_Final_LatticeSumBounds_c2b
import Theorems.Thm_Formalism_HermitianLatticeCounting_Final_LatticeSumBounds_projQuotCard


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Formalism.HermitianLatticesTheory Module
variable (K : Type) [Field K] [NumberField K]
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (d : 𝓞 K) (hd : d ≠ 0) :
    Finite (Submodule (𝓞 K) ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K d)) ∧
    Nat.card (Submodule (𝓞 K) ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K d)) ≤ ((Algebra.norm ℤ d).natAbs ^ 2) ^ 2 := by
  have hI : Ideal.span {d} ≠ (⊥ : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hd
  have hc := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.projQuotCard K (Fin 2 → 𝓞 K) (Ideal.span {d}) hI
  rw [Module.finrank_fin_fun, Ideal.absNorm_span_singleton] at hc
  have h0 : Algebra.norm ℤ d ≠ 0 := by
    rw [Ne, Algebra.norm_eq_zero_iff]; exact hd
  have hpos : Nat.card ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K d) ≠ 0 := by
    rw [hc]; exact pow_ne_zero _ (Int.natAbs_ne_zero.2 h0)
  have : Finite ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K d) := Nat.finite_of_card_ne_zero hpos
  refine ⟨inferInstance, ?_⟩
  have h1 : Submodule.span (𝓞 K) (Set.range (fun i : Fin 2 => (Pi.single i 1 : Fin 2 → 𝓞 K))) = ⊤ := by
    have h2 := (Pi.basisFun (𝓞 K) (Fin 2)).span_eq
    have h3 : (⇑(Pi.basisFun (𝓞 K) (Fin 2))) = fun i : Fin 2 => (Pi.single i 1 : Fin 2 → 𝓞 K) := by
      funext i; exact Pi.basisFun_apply _ _ i
    rwa [h3] at h2
  have h4 : Submodule.span (𝓞 K) (Set.range (fun i : Fin 2 =>
      (scaledFreeModule K d).mkQ (Pi.single i 1 : Fin 2 → 𝓞 K))) = ⊤ := by
    have h5 : Set.range (fun i : Fin 2 => (scaledFreeModule K d).mkQ (Pi.single i 1 : Fin 2 → 𝓞 K)) =
        (scaledFreeModule K d).mkQ '' Set.range (fun i : Fin 2 => (Pi.single i 1 : Fin 2 → 𝓞 K)) := by
      rw [← Set.range_comp]; rfl
    rw [h5, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_mkQ]
  have h6 := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.c2b.1 (𝓞 K) ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K d) 2 _ h4
  rwa [hc] at h6
end Formalism.MainNotions.BridgeLemma₂
