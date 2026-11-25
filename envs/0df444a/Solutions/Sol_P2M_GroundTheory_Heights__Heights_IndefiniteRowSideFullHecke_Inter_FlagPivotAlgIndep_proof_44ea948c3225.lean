-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotAlgIndep_proof_44ea948c3225
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:24:55.526257+00:00
-- url     : https://prove2.me/submissions/000d2324-5400-48b8-adfa-b56c685f1912

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagPivotAlgIndep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotAlgIndep_spec_pivotMinor_77a5abbbeb58

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotAlgIndep
variable (F : Type) [Field F] (n : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotAlgIndep
theorem _root_.solution : FlagPivotAlgIndep.Statement := by
  intro F _ n
  refine AlgebraicIndependent.of_comp (aeval (spec F n)) ?_
  have hfun : ⇑(aeval (spec F n)) ∘
        (fun q : Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b} => pivotMinor (genMat F n) q.1 q.2.1) =
      ⇑(IsScalarTower.toAlgHom F (MvPolynomial (Fin n × Fin n) F) (FractionRing (MvPolynomial (Fin n × Fin n) F))) ∘
        ((X : Fin n × Fin n → MvPolynomial (Fin n × Fin n) F) ∘
          fun q : Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b} => (Fin.castLE (Nat.sub_le n 1) q.1, q.2.1)) := by
    funext q
    exact spec_pivotMinor F n q.1 q.2.1 q.2.2
  rw [hfun]
  refine AlgebraicIndependent.map' ?_ (IsFractionRing.injective _ _)
  refine (algebraicIndependent_X (Fin n × Fin n) F).comp _ ?_
  rintro ⟨a, b, hb⟩ ⟨a', b', hb'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : a = a' := Fin.ext (by simpa using congrArg Fin.val h1)
  subst h1' h2
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotAlgIndep
