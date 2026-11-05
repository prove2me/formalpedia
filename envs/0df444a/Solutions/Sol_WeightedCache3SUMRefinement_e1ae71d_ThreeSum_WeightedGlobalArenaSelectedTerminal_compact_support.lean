-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedTerminal.compact_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:07:17.383235+00:00
-- url     : https://prove2.me/submissions/b93e66c5-5e50-4fff-a294-1b8ee74028e7

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCompactSupport
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedBudgetCollision
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSelectedTerminal_native_zero
import Theorems.Thm_ThreeSum_TernaryTaggedMinorSupport_support
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaCompactSupport_support
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCompactPairedSupport_support


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedTerminal
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData
open WeightedGlobalArenaBudgetExistence WeightedGlobalArenaSelectedBudgets
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (K n U0 : ℕ) (L R O : ℕ→ℕ→ℤ) (r : ℕ) (s : State (p := p) A)
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedTerminal
theorem _root_.solution (M C0 : ℕ) (B C : ℕ→ℤ) (a b : Fin (A.J+2))
    (hbudget : Budget maps τ cap Q I A K n U0 L R O r s)
    (hb : 0<9*pairFactor m F K)
    (hdrift : (9*pairFactor m F K)^4*M^(4*K+3)≤(p^(2*K))^4)
    (hcover : n^2≤M^r) (hinit : U0^4≤C0*n^(8*K+5)) (hn : C0<n)
    (hLtag : ∀j<I.nB, L j a.val=1 ∧ L j b.val=0)
    (hRtag : ∀j<I.nC, R j a.val=0 ∧ R j b.val=1)
    (hraw : ∀u<I.nB, ∀v<I.nC, ∀u'<I.nB, ∀v'<I.nC,
      (fun t : Fin (A.J+2) => (L u t.val : ZMod p))+(fun t => (R v t.val : ZMod p))=
      (fun t : Fin (A.J+2) => (L u' t.val : ZMod p))+(fun t => (R v' t.val : ZMod p))→
        C v-B u=C v'-B u') :
    let I₀ := input I A s L R O r
    let keysB := fun i => TernaryExtensionEncoding.coefficientCode (hashMap A s r (fun t => (L i t.val : ZMod p)))
    let keysC := fun i => TernaryExtensionEncoding.coefficientCode (hashMap A s r (fun t => (R i t.val : ZMod p)))
    let fB := LightOriginalSurvivors.index keysB I.nB
    let fC := LightOriginalSurvivors.index keysC I.nC
    let I' := WeightedGlobalArenaPairRestriction.restrict I₀ (LightOriginalSurvivors.indices keysB I.nB).length
      (LightOriginalSurvivors.indices keysC I.nC).length fB fC
    ∀i<(setup (r := r) maps τ cap Q I').front.count,
      (TernaryPairedSupport.physicalSupport (WeightedGlobalNativePairMoments.mode
        (fun j => B (fB j)) (fun j => C (fC j)) (S := setup (r := r) maps τ cap Q I') (i := i))).card≤2*p^K := by
  have hz := native_zero maps τ cap Q I A K n U0 L R O r s M C0 hbudget hb hdrift hcover hinit hn
  exact WeightedGlobalArenaCompactSupport.support maps τ cap Q (input I A s L R O r) L R B C
    (hashMap A s r) (fun i => hashMap A s r (fun t => (O i t.val : ZMod p)))
    (fun i => TernaryExtensionEncoding.coefficientCode (hashMap A s r (fun t => (L i t.val : ZMod p))))
    (fun i => TernaryExtensionEncoding.coefficientCode (hashMap A s r (fun t => (R i t.val : ZMod p))))
    a b (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
    hLtag hRtag hraw hz
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedTerminal
