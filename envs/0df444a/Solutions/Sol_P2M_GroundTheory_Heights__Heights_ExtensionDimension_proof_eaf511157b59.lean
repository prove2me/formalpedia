-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ExtensionDimension_proof_eaf511157b59
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:55:41.386723+00:00
-- url     : https://prove2.me/submissions/80594f1e-cba7-490c-97c8-157db407dd20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicNew
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_ker_plusMap_c2ff32dcee6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_plusMap_X_old_c1a40a519d86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_plusMap_X_new_a2cdbbbaf1b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_oldMap_X_e33851c6039e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_ker_oldMap_e83711f0f9ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_isAlgebraic_new_68223d104856
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_exists_rename_of_mem_adjoin_5004780db5b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_ringKrullDim_quotient_ker_39672f46aed5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_transcendental_C_mul_X_none_2119f80dd465
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_trdeg_adjoin_eq_add_one_2eedbc69cbae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e


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
open MvPolynomial
noncomputable section
open AddBlockDimension
namespace GroundTheory.Heights₂.Heights
namespace ExtensionDimension
theorem _root_.solution : ExtensionDimension.Statement := by
  intro ι _ _ n P D
  have : CharZero P.FunField :=
    charZero_of_injective_ringHom (IsFractionRing.injective P.CoordRing P.FunField)
  obtain ⟨s₀, htr₀, hdim₀⟩ := TrdegAdjoin.ringKrullDim_quotient_ker (oldMap D)
  obtain ⟨s₁, htr₁, hdim₁⟩ := TrdegAdjoin.ringKrullDim_quotient_ker (plusMap D)
  rw [ker_oldMap] at hdim₀
  rw [ker_plusMap] at hdim₁

  obtain ⟨j, hj⟩ : ∃ j, D.elt j ≠ 0 := by
    obtain ⟨c, hc⟩ := P.exists_chart
    obtain ⟨u, -, hu⟩ := D.generating c hc
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    simp [h] at hu
  have hYZ : (Set.range fun v ↦ oldMap D (X v)) ⊆ Set.range fun w ↦ plusMap D (X w) := by
    rintro _ ⟨v, rfl⟩
    exact ⟨D.oldCoord v, (oldMap_X D v).symm⟩
  have hC : ∀ r ∈ Algebra.adjoin ℚ (Set.range fun v ↦ oldMap D (X v)), ∃ a, r = rename some a :=
    fun r hr ↦ TrdegAdjoin.exists_rename_of_mem_adjoin (by
      rintro _ ⟨v, rfl⟩
      refine ⟨C (P.mkF (X v)) * X v.1, ?_⟩
      show oldMap D (X v) = _
      rw [oldMap_X, plusMap_X_old, map_mul, rename_C, rename_X]) hr
  have he : Transcendental (Algebra.adjoin ℚ (Set.range fun v ↦ oldMap D (X v)))
      (plusMap D (X (D.newCoord j))) := by
    rw [plusMap_X_new]
    exact TrdegAdjoin.transcendental_C_mul_X_none _ hC hj
  have halg : ∀ z ∈ Set.range fun w ↦ plusMap D (X w),
      IsAlgebraic (Algebra.adjoin ℚ (insert (plusMap D (X (D.newCoord j)))
        (Set.range fun v ↦ oldMap D (X v)))) z := by
    rintro _ ⟨⟨_ | k, i⟩, rfl⟩
    · exact isAlgebraic_new D hj i
    · have hmem : plusMap D (X ⟨some k, i⟩) ∈ Algebra.adjoin ℚ (insert (plusMap D (X (D.newCoord j)))
          (Set.range fun v ↦ oldMap D (X v))) :=
        Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨⟨k, i⟩, oldMap_X D _⟩)
      exact isAlgebraic_algebraMap (⟨_, hmem⟩ : Algebra.adjoin ℚ _)
  have htr := TrdegAdjoin.trdeg_adjoin_eq_add_one hYZ ⟨D.newCoord j, rfl⟩ he halg htr₀
  rw [htr₁] at htr
  have hs : s₁ = s₀ + 1 := by exact_mod_cast htr
  rw [hdim₁]
  change _ = ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ P.ideal) + 1
  rw [hdim₀, hs]
  push_cast
  rfl
end ExtensionDimension
end GroundTheory.Heights₂.Heights
