-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Fr.exists_gamma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:25.297335+00:00
-- url     : https://prove2.me/submissions/3830e275-c527-42ee-9c48-9567407095e6

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAlg
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_DoublingGramFromBlocks
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Fr_emb_i
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Fr_embeddingAtLocalFactor
import Theorems.Thm_PositivityTheory_ThKF0_Chr_eta_sq
import Theorems.Thm_PositivityTheory_ThKF0_Chr_exists_gamma0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM PositivityTheory.ThK.SiegelT
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {β β₁ μ ν : Type} [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁] [Fintype μ] [DecidableEq μ]
  [Fintype ν] [DecidableEq ν]
variable {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {H : Matrix μ μ E} {ι : Matrix β β₁ E} {Z : Matrix β μ E}
  {π : Matrix β₁ β E} {ρ : Matrix μ β E}
namespace PositivityTheory.ThKF0.Chr
namespace Fr
theorem _root_.solution {η : ℤˣ} {X Y : Matrix β ν E} {ρ : Matrix (ν ⊕ ν) β E}
    (h : Fr c J J₁ (hyp ν η) ι (fromCols X Y) π ρ) :
    ∃ (γ : UG c (GlobalTheory.WeilM.dbl J)) (s : Matrix (β₁ ⊕ (ν ⊕ ν)) β E) (s' : Matrix β (β₁ ⊕ (ν ⊕ ν)) E), s * s' = 1 ∧ s' * s = 1 ∧
      γ.1.1 * (diagCols β : Matrix _ _ E) = fromCols (dd2 ι * diagCols (E := E) β₁) (dd2 X) * s := by
  obtain ⟨γ₀, hγ⟩ := exists_gamma0 (c := c) (ν := ν) η
  set s₀ : Matrix (ν ⊕ ν) (ν ⊕ ν) E := fromBlocks 1 0 0 (((η : ℤ) : E) • 1)
  have hs : s₀ * s₀ = 1 := by simp [s₀, fromBlocks_multiply, smul_smul, eta_sq]
  set Z := fromCols X Y
  refine ⟨h.dbl.emb (1, γ₀), fromRows π (s₀ * ρ), fromCols ι (Z * s₀), ?_, ?_, ?_⟩
  · rw [fromRows_mul_fromCols, ← Matrix.mul_assoc π, Matrix.mul_assoc s₀, Matrix.mul_assoc s₀, ← Matrix.mul_assoc ρ,
      h.pi, h.pz, h.ri, h.rz, Matrix.one_mul, hs]
    simp
  · rw [fromCols_mul_fromRows, Matrix.mul_assoc, ← Matrix.mul_assoc s₀, hs, Matrix.one_mul, h.one]
  · have e : (diagCols β : Matrix _ _ E) = dd2 ι * (diagCols (E := E) β₁ * π) + dd2 Z * (diagCols (E := E) (ν ⊕ ν) * ρ) := by
      simp only [diagCols, fromRows_mul, fromBlocks_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
      rw [← h.one]
      ext (i | i) j <;> rfl
    have e2 : dd2 Z * dd2 (fromRows (1 : Matrix ν ν E) (0 : Matrix ν ν E)) = dd2 X := by
      rw [fromBlocks_multiply]
      simp [Z, fromCols_mul_fromRows]
    rw [e, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc _ (dd2 Z), Fr.emb_i, Fr.embeddingAtLocalFactor, fromCols_mul_fromRows,
      Matrix.mul_assoc (dd2 Z), ← Matrix.mul_assoc γ₀.1.1, hγ, ← e2]
    simp only [Matrix.mul_assoc]
    simp
end Fr
end PositivityTheory.ThKF0.Chr
