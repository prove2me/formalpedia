-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormOfDividedForm_adjoin_range_eq_top_642ff4789c14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:37:24.093822+00:00
-- url     : https://prove2.me/submissions/221e0166-91f3-4019-a0ed-2fd37a77cf0d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormOfDividedForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PNormOfDividedForm

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
open scoped nonZeroDivisors
noncomputable section
open GroundTheory.Heights₂.Heights.NormOfDividedForm
variable {O B K L : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B] [Field K] [Field L] [Algebra O K]
  [IsFractionRing O K] [Algebra B L] [Algebra K L] [Algebra O L] [IsScalarTower O K L] [IsScalarTower O B L]
  [IsLocalization (Algebra.algebraMapSubmonoid B O⁰) L]
namespace GroundTheory.Heights₂.Heights.NormOfDividedForm
theorem _root_.solution {n : ℕ} (η : Fin n → B) (hgen : Algebra.adjoin O (Set.range η) = ⊤) :
    Algebra.adjoin K (Set.range fun m => algebraMap B L (η m)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid B O⁰) x
  obtain ⟨a, ha, has⟩ := s.2
  have hle : (Algebra.adjoin O (Set.range η)).map (IsScalarTower.toAlgHom O B L) ≤
      (Algebra.adjoin K (Set.range fun m => algebraMap B L (η m))).restrictScalars O := by
    rw [AlgHom.map_adjoin, Algebra.adjoin_le_iff]
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars, IsScalarTower.coe_toAlgHom']
    exact Algebra.subset_adjoin ⟨m, rfl⟩
  have hb : algebraMap B L b ∈ Algebra.adjoin K (Set.range fun m => algebraMap B L (η m)) :=
    hle (Subalgebra.mem_map.2 ⟨b, by rw [hgen]; trivial, IsScalarTower.toAlgHom_apply O B L b⟩)
  have ha0 : algebraMap O K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (nonZeroDivisors.ne_zero ha)
  have hs : IsLocalization.mk' L b s = (algebraMap O K a)⁻¹ • algebraMap B L b := by
    rw [eq_inv_smul_iff₀ ha0, Algebra.smul_def, ← IsScalarTower.algebraMap_apply O K L,
      IsScalarTower.algebraMap_apply O B L, has]
    exact IsLocalization.mk'_spec' L b s
  change IsLocalization.mk' L b s ∈ _
  rw [hs]
  exact Subalgebra.smul_mem _ hb _
end GroundTheory.Heights₂.Heights.NormOfDividedForm
