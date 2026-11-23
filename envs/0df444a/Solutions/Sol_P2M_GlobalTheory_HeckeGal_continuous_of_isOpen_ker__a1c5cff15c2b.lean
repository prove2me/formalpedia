-- Prove2me | solution 1 for P2M_GlobalTheory_HeckeGal_continuous_of_isOpen_ker__a1c5cff15c2b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:46.56575+00:00
-- url     : https://prove2.me/submissions/e753e5e3-d6cc-4595-9390-04ccaa923c04

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory GlobalTheory.HeckeGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.HeckeGal
theorem _root_.solution {Γ B : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group B]
    [TopologicalSpace B] [IsTopologicalGroup B] (φ : Γ →* B) (h : IsOpen (φ.ker : Set Γ)) : Continuous φ := by
  refine continuous_of_continuousAt_one φ ?_
  refine (continuousAt_const (y := (1 : B))).congr ?_
  filter_upwards [h.mem_nhds φ.ker.one_mem] with g hg
  exact (MonoidHom.mem_ker.mp hg).symm
end GlobalTheory.HeckeGal
