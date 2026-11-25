-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeLinesIndep_proof_57688b9c57e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:18.465364+00:00
-- url     : https://prove2.me/submissions/51d22c1b-601d-466a-b6f7-edb4bc9d6574

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairConeLinesIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeLinesIndep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeLinesIndep_formMatrix_isUnit_7170a1850900
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeLinesIndep_linearChange_indep_964b7f140ee7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace PairConeLinesIndep
theorem _root_.solution : PairConeLinesIndep.Statement := by
  intro Ω _ Φ _ _ K N E _ _ e ψ hψ t ht g hg
  have hw : AlgebraicIndependent Ω (fun i => ∑ j, t j * algebraMap Ω Φ (ψ i (e j))) :=
    PairConeLinesIndep.linearChange_indep (Matrix.of fun i j => ψ i (e j))
      (PairConeLinesIndep.formMatrix_isUnit e ψ hψ) t ht
  let T : K → MvPolynomial (Option (Option K)) Φ := fun k => X (some (some k))
  let idx : Unit ⊕ K → Option (Option K) := Sum.elim (fun _ => none) (fun k => some (some k))
  have hidx : Function.Injective idx := by
    rintro (_ | a) (_ | b) h <;> simp_all [idx]
  have hvars : AlgebraicIndependent Φ (X ∘ idx : Unit ⊕ K → MvPolynomial (Option (Option K)) Φ) :=
    (algebraicIndependent_X _ _).comp idx hidx
  have hA := AlgebraicIndependent.sumElim_comp hw hvars
  have hB : AlgebraicIndependent Ω
      (Sum.elim (Sum.elim (fun i => C (∑ j, t j * algebraMap Ω Φ (ψ i (e j))))
        (fun _ : Unit => (X none : MvPolynomial (Option (Option K)) Φ))) T) := by
    have h := hA.comp ((Equiv.sumAssoc _ _ _).trans (Equiv.sumComm _ _)) (Equiv.injective _)
    convert h using 1
    funext x
    rcases x with ((i | u) | k) <;> simp [idx, T, MvPolynomial.algebraMap_eq]
  have hC := (AlgebraicIndependent.sumElim_iff.mp hB).2
  let σ : MvPolynomial (Option (Option K)) Φ →ₐ[Φ] MvPolynomial (Option (Option K)) Φ :=
    aeval fun o => Option.elim o (C g⁻¹ * X none) (fun o' => Option.elim o' 1 (fun k => X (some (some k))))
  have hfix : Algebra.adjoin Ω (Set.range T) ≤ AlgHom.equalizer (σ.restrictScalars Ω) (AlgHom.id Ω _) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨k, rfl⟩
    simp [σ, T]
  let f : MvPolynomial (Option (Option K)) Φ →ₐ[Algebra.adjoin Ω (Set.range T)]
      MvPolynomial (Option (Option K)) Φ :=
    { σ.toRingHom with commutes' := fun r => hfix r.2 }
  apply AlgebraicIndependent.of_comp f
  convert hC using 1
  funext x
  rcases x with i | u
  · simp [f, σ]
  · change σ (C g * X none) = X none
    simp only [σ, map_mul, aeval_C, aeval_X, Option.elim, MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hg, C_1, one_mul]
end PairConeLinesIndep
end GroundTheory.Heights₂.Heights.NumbersDVR
