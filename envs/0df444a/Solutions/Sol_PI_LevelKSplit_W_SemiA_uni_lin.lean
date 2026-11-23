-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiA.uni_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:36:40.075802+00:00
-- url     : https://prove2.me/submissions/432890a7-276f-491d-854d-c937cc35872b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
variable {R σ J P T}
namespace PI.LevelKSplit.W.SemiA
theorem _root_.solution (g : HA R σ J) : (datR R σ J P T).Uni (lin R σ J g) := by
  open Matrix in (
  intro x y
  have hmem : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
      JR R J * ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := g.2
  show Formalism.UG.hform (sigR R σ) (JR R J)
      (((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
      (((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y) =
    Formalism.UG.hform (sigR R σ) (JR R J) x y
  generalize ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = N at hmem ⊢
  have hmem' : (N.map (sigR R σ))ᵀ * JR R J * N = JR R J := hmem
  have hf : ∀ u v : Fin M → R ⊗[F] E, Formalism.UG.hform (sigR R σ) (JR R J) u v =
      (fun i => sigR R σ (u i)) ⬝ᵥ (JR R J *ᵥ v) := by
    intro u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [hf, hf]
  have hs : (fun i => sigR R σ ((N *ᵥ x) i)) = (N.map (sigR R σ)) *ᵥ (fun i => sigR R σ (x i)) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  rw [hs, ← vecMul_transpose (N.map (sigR R σ)), ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← Matrix.mul_assoc]
  rw [hmem'])
end PI.LevelKSplit.W.SemiA
