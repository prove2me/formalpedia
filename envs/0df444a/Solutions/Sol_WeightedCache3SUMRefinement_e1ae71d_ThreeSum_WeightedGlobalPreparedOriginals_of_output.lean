-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPreparedOriginals.of_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:04:02.311577+00:00
-- url     : https://prove2.me/submissions/1596659b-0272-4ffa-88b4-a6ce67bcdfeb

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaOriginalInputs
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPreparedOriginals
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPreparedOriginals_of_matrices
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPreparedOriginals_metadata
import Theorems.Thm_ThreeSum_LightExtensionBackendLayout_end_le
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalComputedExtensionMenu_coefficient_read


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPreparedOriginals
open Light LightWeightedGlobalColorPreparation LightWeightedGlobalColorPreparationProof
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaLayout
open WeightedGlobalArenaSeedData TernarySignedReduction TernarySignedLayout
open WeightedGlobalArenaSelectedSigned TernaryExtensionEncoding
set_option maxHeartbeats 6000000
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable {d c : ℕ} [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus p d c))]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPreparedOriginals
theorem _root_.solution {n free U R J backend radix C0 weightCap queryTime : ℕ}
    (hd : 0<d) (μ ν : ℕ→ℤ) (color : Coloring.Parameter (LightColorParametersCosts.width n))
    (x : Fin n→ℤ) (ret : ℤ)
    (H : LightWeightedGlobalColorPreparationProof.Output μ ν free U R J (p^d)
      (LightExtensionBackendLayout.physical backend d (p^d) J) radix color x ret)
    (hret : ret≠0) (hx : ∀i,|x i|≤(U:ℤ)) (hb : 1<radix) (hp : radix<p)
    (hbackend : backend+LightExtensionBackendLayout.reserve d p (p^d) J≤free)
    (hMenu : LightWeightedGlobalGlobalPreludeProof.Menu μ backend d p (p^d) J c) :
    ∃A B C : List ℤ,
      Metadata n U A B C ∧ A≠[] ∧ B≠[] ∧ C≠[] ∧
      LightTernaryColorPrelude.Normalized ν (LightTernaryColorPrelude.av free n) n
        (ColorClassLists.classList color x 0 1) A ∧
      LightTernaryColorPrelude.Normalized ν (LightTernaryColorPrelude.bv free n) n
        (ColorClassLists.classList color x 1 1) B ∧
      LightTernaryColorPrelude.Normalized ν (LightTernaryColorPrelude.cv free n) n
        (ColorClassLists.classList color x 2 (-1)) C ∧
      Seg ν (headerAt free n (LightColorParametersCosts.width n))
        (header free n U R J (p^d) (LightExtensionBackendLayout.physical backend d (p^d) J) A B C) ∧
      WeightedGlobalArenaPrefixInputs.Originals (input free n U J C0 weightCap queryTime A B C)
        (inputs free n J (LightExtensionBackendLayout.physical backend d (p^d) J) A B C)
        ((p^d)*(p^d)) radix radix n (WeightedGlobalComputedExtensionMenu.functional (p:=p) (c:=c) hd)
        (WeightedGlobalArenaFamilyBudget.seedAt (WeightedGlobalComputedExtensionMenu.seeds (p:=p) (d:=d) (c:=c)))
        (left U radix J (fun i => B.getD i 0)) (right U radix J (fun i => C.getD i 0))
        (requester U radix J (fun i => A.getD i 0)) ν := by
  obtain ⟨hkept,A,B,C,hA,hB,hC,hcase⟩ := H
  rcases hcase with hz|hpos
  · exact (hret hz.1).elim
  rcases hpos with ⟨hr,hneA,hneB,hneC,hheader,hmat⟩
  have hend : LightExtensionBackendLayout.physical backend d (p^d) J+(p^d)*(p^d)*(J+2)≤free := by
    have he := LightExtensionBackendLayout.end_le backend d p (p^d) J
    have hle : LightExtensionBackendLayout.physical backend d (p^d) J+(p^d)*(p^d)*(J+2)≤
        LightExtensionBackendLayout.sum backend d (p^d) J+2*d := by
      unfold LightExtensionBackendLayout.sum LightExtensionBackendLayout.prod LightExtensionBackendLayout.r
        LightExtensionBackendLayout.h LightExtensionBackendLayout.b LightExtensionBackendLayout.a
      omega
    exact hle.trans (he.trans hbackend)
  refine ⟨A,B,C,metadata color x A B C ν hA hB hC hx,hneA,hneB,hneC,hA,hB,hC,hheader,?_⟩
  apply of_matrices free n U J radix C0 weightCap queryTime _ _ A B C ν hmat hA.length hb hp
    (WeightedGlobalComputedExtensionMenu.functional (p:=p) (c:=c) hd)
    (WeightedGlobalArenaFamilyBudget.seedAt (WeightedGlobalComputedExtensionMenu.seeds (p:=p) (d:=d) (c:=c))) hend
  intro ordinal ho k hk
  have hx : LightExtensionBackendLayout.physical backend d (p^d) J+ordinal*(J+2)+k<free := by
    have hh := Nat.mul_le_mul_right (J+2) (show ordinal+1≤(p^d)*(p^d) by omega)
    nlinarith
  exact (hkept _ hx).trans (WeightedGlobalComputedExtensionMenu.coefficient_read hd μ hMenu ordinal ho k hk)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPreparedOriginals
