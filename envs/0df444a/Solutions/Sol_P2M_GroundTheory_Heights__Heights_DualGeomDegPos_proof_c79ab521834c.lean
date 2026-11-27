-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualGeomDegPos_proof_c79ab521834c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:54:45.376203+00:00
-- url     : https://prove2.me/submissions/6fe39483-d71e-4a00-9405-a4d68f7568fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegPos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_logNorm_oneLine_0f01f43a533f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_isGoodProj_9122b7c98d31

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
open scoped ComplexOrder
noncomputable section
open DualGeometricDegreePositive
namespace GroundTheory.Heights₂.Heights
namespace DualGeomDegPos
theorem _root_.solution (hDeg : DegreeStatement) (hInd : PtsIndepStatement)
    (hArith : DualArithVar.Statement) (hSemi : DualLineSemipositive.Statement)
    (hOn : DualPtsOnPlane.Statement) (hMass : DualStdMassAt.Statement) :
    DualGeomDegPos.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨D, rfl⟩ : ∃ D, i = D + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hV : IsArithVar (dualIdeal b) (D + 1) := hArith K (D + 1) F T b hi
  have hS1 : IsSmoothHerm (dualLine (stdLattice F) b hb) := (hSemi K (D + 1) (stdLattice F) T b hb).1
  have e0 := hDeg Unit (dualBlocks T) (dualIdeal b) D (fun _ => dualLine F b hb) 2 hV
    (fun _ => (hSemi K (D + 1) F T b hb).1) Nat.prime_two
  have e1 := hDeg Unit (dualBlocks T) (dualIdeal b) D (fun _ => dualLine (stdLattice F) b hb) 2 hV
    (fun _ => hS1) Nat.prime_two
  have hswap : geomDeg (dualIdeal b) (dualLine F b hb) D =
      geomDeg (dualIdeal b) (dualLine (stdLattice F) b hb) D := by
    change ptsIntegral (dualIdeal b) (pot fun _ => dualLine F b hb) (fun _ => 1) =
      ptsIntegral (dualIdeal b) (pot fun _ => dualLine (stdLattice F) b hb) (fun _ => 1)
    rw [e0, e1]
    rfl
  have hgood := isGoodProj hOn b hb
  have hΨ : ∃ Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (dualIdeal b) Ψ := ⟨_, hgood⟩
  have hsec : IsSectionOn (dualIdeal b) (oneLine (T := T)) 1 := by
    refine ⟨fun _ => 0, fun _ => rfl, ?_, ?_⟩
    · intro d hd k
      rw [support_one] at hd
      simp only [Finset.mem_singleton] at hd
      simp [hd]
    · exact (Ideal.ne_top_iff_one _).1 hV.2.1.1.ne_top
  have h := hInd Unit (dualBlocks T) (dualIdeal b) D hΨ.choose (dualProj b hb)
    (fun _ => dualLine (stdLattice F) b hb) oneLine 1 hV hΨ.choose_spec hgood (fun _ => hS1)
    contDiffOn_const hsec
  rw [logNorm_oneLine] at h
  have hm := hMass K D (stdLattice F) T b hb fun _ => rfl
  have hval : geomDeg (dualIdeal b) (dualLine (stdLattice F) b hb) D = Fintype.card (K →+* ℂ) := by
    unfold geomDeg ptsIntegral
    rw [dif_pos hΨ]
    exact h.trans hm
  rw [hswap, hval]
  exact_mod_cast Fintype.card_pos
end DualGeomDegPos
end GroundTheory.Heights₂.Heights
