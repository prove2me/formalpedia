-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_radial_decomposition_of_parts__2101ea3571b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:11.853402+00:00
-- url     : https://prove2.me/submissions/f467e97f-0f4b-4ab6-a3f4-36040a1a4f16

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_ExistsFrameOfPositiveVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_TopLevelPointwiseIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SpecAbstract
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBLie
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_Vanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_RadialDecompositionOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_frame_sub
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_J_smoothVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_Pp_OK
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_capRep_linear
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_comb_match
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_exists_sep
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ff_GGinv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ff_add
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ff_smul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ff_zero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_geom_package
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_left_ad
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_spec_abstract
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_top_level_pointwise_identity
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_vanish_match


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution : RadialDecompositionOfParts := by
  intro _hC2 _hCC hCap hRTA hBr hTP
  intro Wp Wq _ _ _ _ _ _ P z z' π π' D hPl hD hGGD J hJ
  obtain ⟨hP, hz, hz', hTz, hTz', hπ, hπ'⟩ := hPl
  have hT : 0 < Tz P.k P.r z := by rw [hTz]; exact hP.T_pos
  have hT' : 0 < Tz P.k P.r z' := by rw [hTz']; exact hP.T'_pos
  obtain ⟨Y₀, hY₀⟩ := exists_sep hP
  obtain ⟨f, hfi, hfx, hfr⟩ := comb_match hP
  have hloc : ∀ g : Mx P.k P.r, ∃ (Bs : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ)
      (e : Fin (2 * P.r + P.k + 1) → ℂ) (S : M.Ty (Pp P) → Submodule ℂ Wq),
      g ∈ Glev P.k P.r (Fin.last P.r) ∩ D →
      IsFrameOf P.k P.r [g⁻¹ *ᵥ z, z'] Bs ∧ inWb P.k P.r e ∧ herm (Hpk P.k P.r) e z = 0 ∧
      herm (Hpk P.k P.r) e e = 1 ∧ IsFrameOf P.k P.r [z, e] (fun a => g *ᵥ Bs a) ∧ DirectSum.IsInternal S ∧
      ∀ σ, ∀ v ∈ S σ, ∀ w : ℂ, capRep P.k P.r π' Bs w v = M.xC (Pp P) σ (w - ((P.k : ℂ) - 2) / 2) • v := by
    intro g
    by_cases hg : g ∈ Glev P.k P.r (Fin.last P.r) ∩ D
    · obtain ⟨Bs, e', e, hB1, he', he'z, he'e, hB2, he, hez, hee, hB3⟩ :=
        geom_package hz hz' hT hT' hg.1 (hGGD g hg.2)
      obtain ⟨S, hSi, -, hSe⟩ := hBr Wq (Pp P) (Pp_OK hP) rfl z' e' π' hz' hT' hπ' he' he'z he'e
      exact ⟨Bs, e, S, fun _ => ⟨hB1, he, hez, hee, hB3, hSi, fun σ v hv w => hSe Bs hB2 σ w v hv⟩⟩
    · exact ⟨fun _ _ => 0, 0, fun _ => ⊥, fun h => absurd h hg⟩
  choose Bs e S hBS using hloc
  obtain ⟨dec, hdecF, hsum, heigd, hcomp⟩ := spec_abstract (FFl P.k P.r z z' π π' (Fin.last P.r) D)
    (Glev P.k P.r (Fin.last P.r) ∩ D) ff_zero (fun F₁ h₁ F₂ h₂ => ff_add h₁ h₂) (fun F h c => ff_smul h c)
    (fun Y F => tL P.k P.r z z' (Fin.last P.r) Y 1 1 F) (fun x => (GGl P.k P.r z z' x : ℂ))
    (fun g hg => by exact_mod_cast hGGD g hg.2) Y₀
    (fun F hF => ff_GGinv hz hz' hD hGGD (hTP Wp Wq P.k P.r z z' π π' (Fin.last P.r) D Y₀ 1 1 hz hz' hD F hF))
    (fun σ Y => M.xC (Pp P) σ Y) hY₀ S (fun g hg => (hBS g hg).2.2.2.2.2.1)
    (by
      intro F hF g hg σ v hv Y
      have hc : Y + ((P.k : ℂ) - 2) / 2 - ((P.k : ℂ) - 2) / 2 = Y := by ring
      rw [top_level_pointwise_identity hCap hRTA hz hz' hD hπ'.2.1 hπ'.2.2.1 hF hg (hGGD g hg.2) (Bs g) (hBS g hg).1 Y v,
        (hBS g hg).2.2.2.2.2.2 σ v hv _, hc, ContinuousLinearMap.map_smul, smul_smul])
    J hJ
  have hvan : ∀ σ, σ ∉ Set.range f → ∀ g ∈ Glev P.k P.r (Fin.last P.r) ∩ D, dec σ g = 0 := by
    intro σ hσ g hg
    ext v
    obtain ⟨w, hw, hdw⟩ := hcomp g hg σ v
    rw [hdw, _root_.zero_apply]
    by_contra hne
    obtain ⟨hB1, he, hez, hee, hB3, -, hSe⟩ := hBS g hg
    have hsm := J_smoothVec hz hz' hD hπ'.2.1.1 hJ hg w
    have hlin : ∀ W : ℂ, IsLinearMap ℂ (capRep P.k P.r π (fun a => g *ᵥ Bs g a) W) := fun W =>
      capRep_linear hπ hne hsm (fun a => g *ᵥ Bs g a) (frame_sub hB3 (by simp)) W
    have hμ : ∀ W : ℂ, capRep P.k P.r π (fun a => g *ᵥ Bs g a) W (J g w) =
        M.xC (Pp P) σ (W - ((P.k : ℂ) - 2) / 2) • J g w := by
      intro W
      rw [← left_ad hz hz' hD hπ'.2.1.1 hJ hg (Bs g) (frame_sub hB1 (by simp)) W w,
        hRTA Wp Wq P.k P.r (P.k - 1) z z' π π' D hz hz' hD hπ'.2.1 hπ'.2.2.1 J hJ g hg (Bs g)
          (frame_sub hB1 (by simp)) W w,
        hSe σ w hw W, ContinuousLinearMap.map_smul]
    obtain ⟨ρ, hρ⟩ := vanish_match hBr hP hz hT hπ he hez hee _ hB3 hlin hne _ hμ
    exact hσ (hfr σ ρ hρ)
  refine ⟨fun ρ => dec (f ρ), fun ρ => hdecF (f ρ), ?_, ?_⟩
  · intro g hg
    have h1 : ∑ σ ∈ Finset.univ.image f, dec σ g = ∑ σ, dec σ g :=
      Finset.sum_subset (Finset.subset_univ _) (fun σ _ hσ => hvan σ
        (fun ⟨ρ, hρ⟩ => hσ (hρ ▸ Finset.mem_image_of_mem f (Finset.mem_univ ρ))) g hg)
    rw [hsum g hg, ← h1, Finset.sum_image (fun a _ b _ h => hfi h)]
  · intro ρ Y g hg
    have h := heigd (f ρ) Y g hg
    rw [h, hfx ρ Y]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
