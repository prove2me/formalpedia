-- Prove2me | solution 1 for OAI.UniversalTensorSquare.kronecker_pos_transpose
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:49:10.921241+00:00
-- url     : https://prove2.me/submissions/feee6f10-a2d2-4f27-8811-aa31284612ad

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_Saxl_specht_sign_transpose_uts

section
-- module Solutions.OAIQ259_US.Saxl_Basic
attribute [-instance] _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV uW

namespace Saxl

/- The genuine finite-dimensional Hom criterion; no simplicity hypothesis. -/
theorem intertwining_finrank_pos_iff {G : Type uG} {V : Type uV} {W : Type uW} [Group G]
    [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W]
    [Module.Finite ℂ V] [Module.Finite ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    0 < Module.finrank ℂ (Representation.IntertwiningMap ρ σ) ↔
      ∃ f : Representation.IntertwiningMap ρ σ, f ≠ 0 :=
  Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := Representation.IntertwiningMap ρ σ)

theorem kronecker_pos_iff {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ) :
    0 < kronecker a b t ↔
      ∃ f : Representation.IntertwiningMap (spechtRep t)
        ((spechtRep a).tprod (spechtRep b)), f ≠ 0 := by
  exact @intertwining_finrank_pos_iff (Equiv.Perm (Fin n)) (Specht t)
    (Specht a ⊗[ℂ] Specht b) _ _ _ _ _ _ _
    (spechtRep t) ((spechtRep a).tprod (spechtRep b))

/- Column permutations cannot also fix the row word unless they are identity. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_TransposeSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transpose Support. -/

section

noncomputable section
open scoped TensorProduct

namespace UniversalTensorSquare

lemma canonical_sign_transpose {n : ℕ} (μ : YoungDiagram) (hμ : μ.card = n) :
    Nonempty ((Saxl.spechtRep (Saxl.canonicalTableau μ hμ)).Equiv
      (Saxl.signTwist (Saxl.spechtRep
        (Saxl.canonicalTableau μ.transpose ((Saxl.transpose_card μ).trans hμ))))) := by
  obtain ⟨e⟩ := Saxl.specht_sign_transpose_uts (Saxl.canonicalTableau μ hμ)
  let e' := Saxl.equivOfSubrepEq
    (Saxl.spechtSub (Saxl.transposeTableau (Saxl.canonicalTableau μ hμ)))
    (Saxl.spechtSub
      (Saxl.canonicalTableau μ.transpose ((Saxl.transpose_card μ).trans hμ)))
    (Saxl.spechtSub_tableau_independent _ _)
  exact ⟨e.trans (signTwistEquiv e')⟩

lemma canonical_self_sign {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) :
    Nonempty ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).Equiv
      (Saxl.signTwist (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)))) := by
  obtain ⟨e⟩ := canonical_sign_transpose lam hlam
  let e' := spechtShapeEquiv hself
    (Saxl.canonicalTableau lam.transpose ((Saxl.transpose_card lam).trans hlam))
    (Saxl.canonicalTableau lam hlam)
  exact ⟨e.trans (signTwistEquiv e')⟩

lemma tensorAnti_injective {n : ℕ} {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    {σ : Representation ℂ (Equiv.Perm (Fin n)) Y}
    {τ : Representation ℂ (Equiv.Perm (Fin n)) Z}
    (e : σ.Equiv (Saxl.signTwist τ)) :
    Function.Injective (Saxl.tensorAnti ρ e.toIntertwiningMap) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ X) e.toLinearEquiv).injective

lemma kronecker_pos_transpose_oai {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) (ν : YoungDiagram) (hν : ν.card = n)
    (hpos : 0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) :
    0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau ν.transpose ((Saxl.transpose_card ν).trans hν)) := by
  obtain ⟨eL⟩ := canonical_self_sign lam hlam hself
  obtain ⟨eν⟩ := canonical_sign_transpose ν hν
  obtain ⟨f, hf⟩ := (Saxl.kronecker_pos_iff _ _ _).mp hpos
  let A := Saxl.tensorAnti (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))
    eL.toIntertwiningMap
  let B := (Saxl.signTwistMap
    (Y := Saxl.Specht (Saxl.canonicalTableau lam hlam) ⊗[ℂ]
      Saxl.Specht (Saxl.canonicalTableau lam hlam)) f).comp (Saxl.signCancelMap eν.symm.toIntertwiningMap)
  apply (Saxl.kronecker_pos_iff _ _ _).mpr
  refine ⟨A.comp B, ?_⟩
  intro hz
  apply hf
  ext x
  have h := congrArg (fun F => F (eν x)) hz
  have hi : Function.Injective A := tensorAnti_injective _ eL
  apply hi
  change A (f x) = A 0
  change A (f (eν.symm (eν x))) = 0 at h
  simpa only [eν.symm_apply_apply, map_zero] using h

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.kronecker_pos_transpose_oai := @OAI.UniversalTensorSquare.kronecker_pos_transpose_oai
