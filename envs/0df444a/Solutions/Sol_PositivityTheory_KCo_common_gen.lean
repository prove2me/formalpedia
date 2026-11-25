-- Prove2me | solution 1 for PositivityTheory.KCo.common_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:36:18.662312+00:00
-- url     : https://prove2.me/submissions/9269cd6e-5522-496f-9063-869681f47acd

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_LocConstChar
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_continuous_rAct_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_common_generator
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_gl_eq_mul_of_rank
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.KCo
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen GlobalTheory.CompanionTheory.ThetaGLLen.FullRank Matrix Topology
  MeasureTheory
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a : Type} [Fintype a] [DecidableEq a] {κ : ℕ}
namespace PositivityTheory.KCo
theorem _root_.solution (hκ : κ = Fintype.card a) (w w' : SB (RankIn k a a {κ})) :
    ∃ t, w ∈ Submodule.span ℂ (Set.range fun g : GL a k => rightRep (k := k) a a κ g t) ∧
      w' ∈ Submodule.span ℂ (Set.range fun g : GL a k => rightRep (k := k) a a κ g t) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  have : TotallyDisconnectedSpace k := inferInstance
  have : TotallyDisconnectedSpace (Matrix a a k) := inferInstanceAs (TotallyDisconnectedSpace (a → a → k))
  have : LocallyCompactSpace (Matrix a a k) := inferInstanceAs (LocallyCompactSpace (a → a → k))
  have : TotallyDisconnectedSpace (GL a k) :=
    ⟨(isTotallyDisconnected_of_image (f := fun g : GL a k => g.val) GlobalTheory.SplitFlip.isEmbedding_val_GL.continuous.continuousOn
      GlobalTheory.SplitFlip.isEmbedding_val_GL.injective (isTotallyDisconnected_of_totallyDisconnectedSpace _))⟩
  let := rMul (k := k) (a := a) (c := a) κ
  have hsm : ∀ (g : GL a k) (x : RankIn k a a {κ}), g • x = rAct {κ} x g⁻¹ := fun _ _ => rfl
  have : ContinuousSMul (GL a k) (RankIn k a a {κ}) := ⟨continuous_rAct_inv κ⟩
  have : MulAction.IsPretransitive (GL a k) (RankIn k a a {κ}) := ⟨fun x y => by
    obtain ⟨g, hg⟩ := exists_gl_eq_mul_of_rank k a a x.1 y.1 (x.2.trans hκ) (y.2.trans hκ)
    refine ⟨g⁻¹, Subtype.ext ?_⟩
    rw [hsm, inv_inv, rAct_val, hg]⟩
  have hXo : IsOpen {x : Matrix a a k | x.rank ∈ ({κ} : Set ℕ)} := by
    convert isOpen_le_rank (k := k) (a := a) (b := a) κ using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => h.ge, fun h => le_antisymm ((Matrix.rank_le_card_height x).trans hκ.ge) h⟩
  have : LocallyCompactSpace (RankIn k a a {κ}) := hXo.locallyCompactSpace
  have hop : ∀ x : RankIn k a a {κ}, IsOpenMap fun g : GL a k => g • x :=
    fun x => isOpenMap_smul_of_sigmaCompact x
  have hρ : ∀ (g : GL a k) (f : SB (RankIn k a a {κ})) (x : RankIn k a a {κ}),
      (rightRep (k := k) a a κ g f).1 x = f.1 (g⁻¹ • x) := by
    intro g f x
    show _ = f.1 (rAct {κ} x g⁻¹⁻¹)
    rw [inv_inv]
    rfl
  exact exists_common_generator (rightRep (k := k) a a κ) hρ hop GlobalTheory.SplitFlip.isCompact_KO GlobalTheory.SplitFlip.isOpen_KO w w'
end PositivityTheory.KCo
