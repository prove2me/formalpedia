-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_proof_a526fc3225e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:09:59.873322+00:00
-- url     : https://prove2.me/submissions/1c0a247c-5160-4bb2-9d13-ecca254b6692

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimUpperZariski
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLocalDimUpperZariski
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_localDim_le_04a08154f7b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_quotient_dim_le_one_99e9070a5a50
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_ConeAvoidsExists_proof_791d6fddc3f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_ConeAvoidsFinite_proof_1e0c84911ab6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_ConeAvoidsOpen_proof_265a021d820f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjHomInjective_proof_a56a3c2f38d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionsContainOpen_proof_15145ee0a27d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_HomogDimZeroPow_proof_57ceec37771d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_LeadIdealDim_proof_02c6e2a8e310
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_LinearFormCut_proof_0748af3de968
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_zeroSet_sliceIdeal_81bd9c1d3ddc


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
open MvPolynomial Matrix ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SliceLocalDimUpperZariski
theorem _root_.solution : SliceLocalDimUpperZariski.Statement := by
  intro n d J q hJ hdim hq
  obtain ⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hWfin⟩ :=
    ComplexSets.FiniteProjectionsContainOpen.proof ComplexSets.ConeAvoidsFinite.proof
      ComplexSets.FiniteProjHomInjective.proof ComplexSets.ConeAvoidsOpen.proof
      (ComplexSets.ConeAvoidsExists.proof ComplexSets.LeadIdealDim.proof
        ComplexSets.LinearFormCut.proof ComplexSets.HomogDimZeroPow.proof) n (d + 1) J hJ hdim
  rw [hS] at hA₀
  obtain ⟨G, hGS, hG⟩ := hA₀
  let ext : Matrix (Fin d) (Fin n) ℂ → Matrix (Fin (d + 1)) (Fin n) ℂ :=
    fun L i j => if h : (i : ℕ) < d then L ⟨i, h⟩ j else A₀ i j
  let F : MvPolynomial (Fin d × Fin n) ℂ :=
    bind₁ (fun ij : Fin (d + 1) × Fin n =>
      if h : (ij.1 : ℕ) < d then X (⟨ij.1, h⟩, ij.2) else C (A₀ ij.1 ij.2)) G
  have hevF : ∀ L : Matrix (Fin d) (Fin n) ℂ,
      eval (fun ij : Fin d × Fin n => L ij.1 ij.2) F =
        eval (fun ij : Fin (d + 1) × Fin n => ext L ij.1 ij.2) G := by
    intro L
    change eval₂Hom (RingHom.id ℂ) _ (bind₁ _ G) = _
    rw [eval₂Hom_bind₁]
    change eval _ G = _
    refine congrArg (fun f => eval f G) (funext fun ij => ?_)
    simp only [ext]
    split_ifs <;> simp
  have hext0 : ext (fun i j => A₀ i.castSucc j) = A₀ := by
    funext i j
    simp only [ext]
    split_ifs with h
    · rfl
    · rfl
  refine ⟨F, fun h0 => hG ?_, fun L hL => ?_⟩
  · have h1 := hevF (fun i j => A₀ i.castSucc j)
    rw [hext0, h0, map_zero] at h1
    exact h1.symm
  · have hmem : ext L ∈ W := by
      rw [hS]
      exact ⟨G, hGS, (hevF L) ▸ hL⟩
    have hfp : IsFiniteProjection J (ext L) := hWfin hmem
    have hq' : q ∈ zeroSet (sliceIdeal J L q) := by
      rw [zeroSet_sliceIdeal]
      exact ⟨hq, rfl⟩
    refine (SliceLocalDimUpperZariski.localDim_le _ q hq').trans
      (SliceLocalDimUpperZariski.quotient_dim_le_one J L q (ext L) (fun i j => ?_) hfp.finite)
    simp [ext, i.isLt]
end SliceLocalDimUpperZariski
end GroundTheory.Heights₂.Heights
