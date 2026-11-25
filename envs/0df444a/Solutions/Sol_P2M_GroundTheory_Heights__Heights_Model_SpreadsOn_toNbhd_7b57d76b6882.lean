-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadsOn_toNbhd_7b57d76b6882
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:12:01.892669+00:00
-- url     : https://prove2.me/submissions/3b7899f0-3a5a-4e63-b187-16661e044fe2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadNbhd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadBundleNbhd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_toOpen___7122ee2325b0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {X : Scheme.{0}}
namespace GroundTheory.Heights₂.Heights.Model
namespace SpreadsOn
theorem _root_.solution (f : X ⟶ SpecZ) (R : Type) [CommRing R] {E : (baseChange f R).Modules}
    {W : X.Opens} (hE : SpreadsOn f R E W) (htop : ⊤ ≤ baseChangeMap f R ⁻¹ᵁ W) :
    ∃ (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι) (E' : (W : Scheme.{0}).Modules),
      IsVectorBundle E' ∧ Nonempty ((Scheme.Modules.pullback (toOpen f R W hW)).obj E' ≅ E) := by
  obtain ⟨E', hE', ⟨α⟩⟩ := hE
  have hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact htop (Set.mem_univ y)
  let U := baseChangeMap f R ⁻¹ᵁ W
  let u : baseChange f R ⟶ U := IsOpenImmersion.lift U.ι (𝟙 _) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact htop (Set.mem_univ y))
  have hu : u ≫ U.ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  have hcomp : u ≫ (baseChangeMap f R ∣_ W) = toOpen f R W hW := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hu,
      Category.id_comp, toOpen_ι]
  exact ⟨hW, E', hE', ⟨pullbackCompIso hcomp α ≪≫ (Scheme.Modules.pullbackComp u U.ι).app E ≪≫
    (Scheme.Modules.pullbackCongr hu).app E ≪≫ (Scheme.Modules.pullbackId _).app E⟩⟩
end SpreadsOn
end GroundTheory.Heights₂.Heights.Model
