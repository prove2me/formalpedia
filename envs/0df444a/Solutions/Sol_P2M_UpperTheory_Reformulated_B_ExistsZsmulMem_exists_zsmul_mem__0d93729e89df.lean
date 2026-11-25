-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_ExistsZsmulMem_exists_zsmul_mem__0d93729e89df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:56.663063+00:00
-- url     : https://prove2.me/submissions/d4fc5dbe-e6dc-432f-b9c7-6e99acad0a48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsZsmulMem
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false

namespace UpperTheory.Reformulated.B.ExistsZsmulMem.exists_zsmul_mem
theorem _root_.solution.{u_1, u_2} :
    ∀ {E : Type u_1} [inst : Field E] [NumberField E] {W : Type u_2} [inst_2 : AddCommGroup W]
    [inst_3 : _root_.Module E W] {La : AddSubgroup W},
    GroundTheory.Heights₂.Heights.FiniteCovolume.IsLattice E La →
      ∀ (x : W),
        ∃ (d : ℤ),
          d ≠ (0 : ℤ) ∧
            d • x ∈ La := by
  intro E _ _ W _ _ La h x
  refine Submodule.span_induction (p := fun x _ => ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ La)
    (fun y hy => ⟨1, one_ne_zero, by simpa using hy⟩) ⟨1, one_ne_zero, by simp⟩ ?_ ?_
    (h.span_eq_top ▸ Submodule.mem_top : x ∈ Submodule.span E (La : Set W))
  · rintro y z - - ⟨d, hd, hy⟩ ⟨e, he, hz⟩
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add, mul_smul d e z, mul_comm d e, mul_smul e d y]
    exact add_mem (La.zsmul_mem hy e) (La.zsmul_mem hz d)
  · rintro a y - ⟨d, hd, hy⟩
    obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple
    refine ⟨m * d, mul_ne_zero hm hd, ?_⟩
    rw [mul_smul, smul_comm d a y, ← smul_assoc]
    exact h.smul_mem ⟨m • a, hi⟩ _ hy
end UpperTheory.Reformulated.B.ExistsZsmulMem.exists_zsmul_mem
