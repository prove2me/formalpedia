-- Prove2me | solution 1 for WeierstrassCurve.natCard_variableChange_smul_eq_subtype_eq_natCard_rationalAut_subtype
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6dbfaa44-1ef7-55c1-91b5-26cce2cb3a21

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_RationalEnd
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq
import Theorems.Thm_WeierstrassCurve_exists_variableChange_forall_eq_equivOfVariableChangeEq_of_comp_eq_id
import Theorems.Thm_WeierstrassCurve_Affine_variableChange_eq_of_forall_equivOfVariableChangeEq_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_variableChange_smul_eq_subtype_eq_natCard_rationalAut_subtype

set_option autoImplicit false
set_option maxHeartbeats 6400000

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (W : WeierstrassCurve κ) [W.IsElliptic]
    (Q : (W.toAffine.Point → W.toAffine.Point) → Prop) :
    Nat.card {C : WeierstrassCurve.VariableChange κ //
        ∃ hC : C • W = W, Q (fun P => WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hC P)} =
      Nat.card {ι : W.toAffine.Point →+ W.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet κ W W ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet κ W W, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        Q ι} := by
  classical

  have hex : ∀ C : WeierstrassCurve.VariableChange κ, ∀ hC : C • W = W,
      ∃ ι ∈ WeierstrassCurve.rationalHomSet κ W W, ∃ ι' ∈ WeierstrassCurve.rationalHomSet κ W W,
        (∀ P : W.toAffine.Point, ι P = WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hC P) ∧
          ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _ :=
    fun C hC => WeierstrassCurve.exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq W C hC

  let F : {C : WeierstrassCurve.VariableChange κ //
        ∃ hC : C • W = W, Q (fun P => WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hC P)} →
      {ι : W.toAffine.Point →+ W.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet κ W W ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet κ W W, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        Q ι} := fun C =>
    ⟨Classical.choose (hex C.1 (Classical.choose C.2)), by
      obtain ⟨hι, ι', hι', hιeq, h1, h2⟩ := Classical.choose_spec (hex C.1 (Classical.choose C.2))
      refine ⟨hι, ⟨ι', hι', h1, h2⟩, ?_⟩
      exact Eq.mpr (congrArg Q (funext hιeq)) (Classical.choose_spec C.2)⟩
  have hFval : ∀ C, ∀ P : W.toAffine.Point,
      (F C).1 P = WeierstrassCurve.Affine.Point.equivOfVariableChangeEq (Classical.choose C.2) P := by
    intro C P
    obtain ⟨-, -, -, hιeq, -, -⟩ := Classical.choose_spec (hex C.1 (Classical.choose C.2))
    exact hιeq P
  apply Nat.card_congr
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  ·
    intro C C' hCC'
    apply Subtype.ext
    apply WeierstrassCurve.Affine.variableChange_eq_of_forall_equivOfVariableChangeEq_eq
      (Classical.choose C.2) (Classical.choose C'.2)
    intro P
    rw [← hFval C P, ← hFval C' P, hCC']
  ·
    intro ι
    obtain ⟨hι, ⟨ι', hι', h1, h2⟩, hQ⟩ := ι.2
    obtain ⟨γ, hγ, hγeq⟩ :=
      WeierstrassCurve.exists_variableChange_forall_eq_equivOfVariableChangeEq_of_comp_eq_id W W ι.1 hι ι' hι' h1 h2
    refine ⟨⟨γ, hγ, Eq.mp (congrArg Q (funext hγeq)) hQ⟩, ?_⟩
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro P
    rw [hFval, hγeq]

end S_WeierstrassCurve_natCard_variableChange_smul_eq_subtype_eq_natCard_rationalAut_subtype
end P2MW
export P2MW.S_WeierstrassCurve_natCard_variableChange_smul_eq_subtype_eq_natCard_rationalAut_subtype (solution)
