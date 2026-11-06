-- Prove2me | solution 2 for QEC.QLDPC.chainComplexCSSRowChecks_qubitCheckDegree_le_incidence
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:12:18.288041+00:00
-- url     : https://prove2.me/submissions/c0c36493-26d3-48e0-b4d2-8c80abcd2165

-- ID: 55270100-c31a-4b7a-b780-ec4ce185c1bd | NAME: QEC.QLDPC.chainComplexCSSRowChecks_qubitCheckDegree_le_incidence | 未本地编译验证
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem solution
    {ι κ lambda : Type v} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda)) (q : ι) :
    qubitCheckDegree (chainComplexCSSRowChecks K) q ≤
      ((chainComplexBoundaryIncidence K).variableSupport q).card := by
  classical
  have hiff : ∀ c : Sum κ lambda,
      q ∈ Coding.PauliSymplectic.support (chainComplexCSSRowCheck K c) ↔
        (chainComplexBoundaryIncidence K).incident c q := by
    intro c
    rcases c with k | l
    · simp [chainComplexCSSRowCheck, chainComplexBoundaryIncidence,
        QEC.Coding.hammingSupport]
    · simp [chainComplexCSSRowCheck, chainComplexBoundaryIncidence,
        QEC.Coding.hammingSupport]
  calc
    qubitCheckDegree (chainComplexCSSRowChecks K) q =
        ((Finset.univ.image (chainComplexCSSRowCheck K)).filter
          (fun g => q ∈ Coding.PauliSymplectic.support g)).card := by
            simp [qubitCheckDegree, chainComplexCSSRowChecks]
    _ ≤ ((Finset.univ.filter (fun c : Sum κ lambda =>
          (chainComplexBoundaryIncidence K).incident c q)).image
          (chainComplexCSSRowCheck K)).card := by
            apply Finset.card_le_card
            intro g hg
            simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
              true_and] at hg ⊢
            rcases hg with ⟨hg_img, hq⟩
            rcases hg_img with ⟨c, rfl⟩
            exact ⟨c, (hiff c).1 hq, rfl⟩
    _ ≤ (Finset.univ.filter (fun c : Sum κ lambda =>
          (chainComplexBoundaryIncidence K).incident c q)).card :=
            Finset.card_image_le
    _ = ((chainComplexBoundaryIncidence K).variableSupport q).card := by
            simp [CheckIncidence.variableSupport]
