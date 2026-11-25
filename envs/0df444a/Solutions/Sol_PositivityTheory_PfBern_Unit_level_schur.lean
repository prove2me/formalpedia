-- Prove2me | solution 1 for PositivityTheory.PfBern.Unit.level_schur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:48:57.578419+00:00
-- url     : https://prove2.me/submissions/f6e244eb-b09a-49fc-adab-95337a5ae036

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_UnitaryKirillovModel_LevelSmulSmul
import Theorems.Thm_PositivityTheory_PfBern_Unit_level_smul_smul
import Theorems.Thm_PositivityTheory_PfBern_Unit_level_smul_comm
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_isSimpleModule_fixedVectors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Unit
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
variable {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
namespace PositivityTheory.PfBern.Unit
theorem _root_.solution (hρ : IsSmooth ρ) [ρ.IsIrreducible] [FiniteDimensional ℂ (fixedVectors ρ K)]
    (hK : fixedVectors ρ K ≠ ⊥) (φ : Module.End (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K)) :
    ∃ c : ℂ, ∀ w, φ w = c • w := by
  have hs := isSimpleModule_fixedVectors (μ := μ) hKc hKo hρ hK
  let φℂ : Module.End ℂ (fixedVectors ρ K) :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun c w => by
        have e : c • w = (c • (1 : HeckeAlgebraLevel μ K hKc hKo)) • w := by
          rw [level_smul_smul, one_smul]
        rw [RingHom.id_apply, e, φ.map_smul, level_smul_smul, one_smul] }
  have hnt : Nontrivial (fixedVectors ρ K) := Submodule.nontrivial_iff_ne_bot.2 hK
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue φℂ
  obtain ⟨w₀, hw₀⟩ := hc.exists_hasEigenvector
  let ψ : Module.End (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K) :=
    { toFun := fun w => φ w - c • w
      map_add' := fun a b => by rw [map_add, smul_add]; abel
      map_smul' := fun h w => by rw [RingHom.id_apply, φ.map_smul, smul_sub, level_smul_comm] }
  have hw₀ker : w₀ ∈ LinearMap.ker ψ := by
    rw [LinearMap.mem_ker]
    show φ w₀ - c • w₀ = 0
    rw [sub_eq_zero]
    exact Module.End.mem_eigenspace_iff.1 hw₀.1
  have hker : LinearMap.ker ψ ≠ ⊥ := fun hb => hw₀.2 (by rw [hb] at hw₀ker; exact (Submodule.mem_bot _).1 hw₀ker)
  have htop := (eq_bot_or_eq_top (LinearMap.ker ψ)).resolve_left hker
  refine ⟨c, fun w => ?_⟩
  have hw : w ∈ LinearMap.ker ψ := by rw [htop]; exact Submodule.mem_top
  exact sub_eq_zero.1 hw
end PositivityTheory.PfBern.Unit
