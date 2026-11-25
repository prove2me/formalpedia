-- Prove2me | solution 1 for P2M_GlobalTheory_DegCnt_FixDisc_idx_gmap__5fad5dddc642
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:36:52.358911+00:00
-- url     : https://prove2.me/submissions/2fb0d279-a7ac-4df3-97e0-fd064fc8fd4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DiscriminantOrderCommonFixedLatticeEmbeddedData
import Theorems.Thm_GlobalTheory_DegCnt_FixDisc_idx_gmap
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_mul
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FixDisc
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.FixDisc
theorem _root_.solution [FiniteDimensional K V] {A B C D : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A)
    (hB : Submodule.IsLattice K B) (hC : Submodule.IsLattice K C) (F : V ≃ₗ[K] V) (hBC : B ≤ C)
    (hDC : D ≤ C) (hi : idxN C B = idxN C D) (hDA : D ≤ A) (h2 : gmap F B ≤ A) :
    (idxN A (gmap F B) : ℚ) = |Algebra.norm ℚ (LinearMap.det (F : V →ₗ[K] V))| * idxN A D := by
  have hE : Submodule.IsLattice K (A ⊔ C) := Submodule.IsLattice.sup K A C
  have e := idx_gmap hE hB F (hBC.trans le_sup_right) (h2.trans le_sup_left)
  rw [← idxN_mul h2 (le_sup_left : A ≤ A ⊔ C), ← idxN_mul hBC (le_sup_right : C ≤ A ⊔ C), hi,
    idxN_mul hDC (le_sup_right : C ≤ A ⊔ C), ← idxN_mul hDA (le_sup_left : A ≤ A ⊔ C)] at e
  have h0 : ((idxN (A ⊔ C) A : ℕ) : ℚ) ≠ 0 := by exact_mod_cast idxN_ne_zero hA hE.fg
  push_cast at e
  rw [← mul_assoc] at e
  exact mul_right_cancel₀ h0 e
end GlobalTheory.DegCnt.FixDisc
