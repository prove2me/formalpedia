-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MAComparison_of_manifold_da1a27d2d4cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:00:07.480378+00:00
-- url     : https://prove2.me/submissions/022f04b1-9406-4c79-a933-d9a899d8f323

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OpenAtlasSymmEventuallyEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_mass_b3b259448c07
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_smooth_587fcd39e6cc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_isPsh_bba4d872c2eb
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_ofFun
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
namespace MAComparison
theorem _root_.solution :
    GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison.Statement → MAComparison.Statement := by
  intro hA D Ω φ a b hyp
  obtain ⟨hΩo, hφ, ha, hb, hpa, hpb, hK⟩ := hyp
  rcases Set.eq_empty_or_nonempty Ω with h0 | hne
  · simp [h0]
  let U : TopologicalSpace.Opens (Fin D → ℂ) := ⟨Ω, hΩo⟩
  have hU : Nonempty U := hne.to_subtype
  let P : LocPot U := LocPot.ofFun fun x => φ x / 2
  have hsum : ∀ c : (Fin D → ℂ) → ℝ, ∀ x z,
      (P + LocPot.ofFun fun x : U => c x / 2).φ x z = (φ + c) z / 2 := by
    intro c x z
    change φ z / 2 + c z / 2 = _
    rw [Pi.add_apply, add_div]
  have key := hA (openAtlas U hU) P (fun x => a x / 2) (fun x => b x / 2)
    ⟨isPotential_ofFun _ _ (openAtlas_smooth U hU (fun z => φ z / 2) (hφ.div_const 2)),
     openAtlas_smooth U hU (fun z => a z / 2) (ha.div_const 2),
     openAtlas_smooth U hU (fun z => b z / 2) (hb.div_const 2),
     openAtlas_isPsh U hU _ (φ + a) (hsum a) (hφ.add ha) hpa,
     openAtlas_isPsh U hU _ (φ + b) (hsum b) (hφ.add hb) hpb, fun k => ?_⟩
  · rw [openAtlas_mass U hU _ _ (hsum b), openAtlas_mass U hU _ _ (hsum a)] at key
    exact key
  · rw [Subtype.isCompact_iff]
    convert hK (2 * k) using 1
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Set.mem_ofPred_eq] at hx
      exact ⟨x.2, by linarith⟩
    · rintro ⟨hz, h⟩
      exact ⟨⟨z, hz⟩, by simp only [Set.mem_ofPred_eq]; linarith, rfl⟩
end MAComparison
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
