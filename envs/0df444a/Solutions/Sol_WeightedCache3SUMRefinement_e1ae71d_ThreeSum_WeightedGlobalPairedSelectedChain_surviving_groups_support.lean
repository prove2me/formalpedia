-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedSelectedChain.surviving_groups_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:34:49.224195+00:00
-- url     : https://prove2.me/submissions/0fe2c7e8-22d2-4f40-b4bf-851eb9085da4

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedSelectedChain
import Theorems.Thm_ThreeSum_TernaryOriginalCollisions_surviving_hash_injective
import Theorems.Thm_ThreeSum_TernaryPairedSupportConcrete_mode_eq_of_singleton_source_hashes
import Theorems.Thm_ThreeSum_TernaryPairedSupportConcrete_physical_support_cap_of_zero_minors


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedSelectedChain
open Filter Real Finset TernaryPairedRecurrence TernaryPairedInitial WeightedGlobalPairedNativeDrift
open WeightedGlobalOversizePrime WeightedGlobalOversizeOverhead WeightedGlobalCoverScale WeightedGlobalLocalParameters TernaryCoverLocal
open WeightedGlobalEntropyRates
open WeightedGlobalSignedPadding TernaryPairedPotential TernaryPairedSupportConcrete
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedSelectedChain
theorem _root_.solution {F W B C G D : Type*}
    [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Fintype W]
    [Fintype B] [Fintype C] [Fintype G] [DecidableEq B] [DecidableEq C]
    [DecidableEq W] [DecidableEq D]
    (J K total : ℕ) (L : B→Fin J→ℤ) (R : C→Fin J→ℤ)
    (H : (Fin J→F)→ₗ[F] W)
    (P : G→Type*) [∀ g, Fintype (P g)]
    (left : ∀ g, P g→{b : B // b∉TernaryOriginalCollisions.deleted (fun b => H (fun j => (L b j : F)))})
    (right : ∀ g, P g→{c : C // c∉TernaryOriginalCollisions.deleted (fun c => H (fun j => (R c j : F)))})
    (root : G→W) (mode : ∀ g, P g→D)
    (hroot : ∀ g a, H ((fun j => (L (left g a).val j : F))+(fun j => (R (right g a).val j : F)))=root g)
    (hraw : ∀ g a b, (fun j => (L (left g a).val j : F))+(fun j => (R (right g a).val j : F))=
      (fun j => (L (left g b).val j : F))+(fun j => (R (right g b).val j : F))→mode g a=mode g b)
    (hsource : ∀ g a b, left g a=left g b → right g a=right g b → mode g a=mode g b)
    (hpotential : (∑ g : G, ∑ e : Fin K→P g,
      rowWeight (tupleMatrix (fun a => L (left g a).val) (fun a => R (right g a).val) e))≤total)
    (hzero : total=0) :
    ∀ g, (TernaryPairedSupport.physicalSupport (mode g)).card≤2*Fintype.card F^K := by
  classical
  intro g
  have hsum : (∑ e : Fin K→P g,
      rowWeight (tupleMatrix (fun a => L (left g a).val) (fun a => R (right g a).val) e))=0 := by
    have hh : (∑ e : Fin K→P g, rowWeight (tupleMatrix (fun a => L (left g a).val) (fun a => R (right g a).val) e))≤
        (∑ g : G, ∑ e : Fin K→P g, rowWeight (tupleMatrix (fun a => L (left g a).val) (fun a => R (right g a).val) e)) :=
      Finset.single_le_sum (f := fun g : G => ∑ e : Fin K→P g,
        rowWeight (tupleMatrix (fun a => L (left g a).val) (fun a => R (right g a).val) e))
        (fun i hi => Nat.zero_le _) (Finset.mem_univ g)
    exact Nat.eq_zero_of_le_zero ((hh.trans hpotential).trans_eq hzero)
  apply physical_support_cap_of_zero_minors
    (fun a => L (left g a).val) (fun a => R (right g a).val) H (root g) (mode g) K
    (hroot g) (hraw g) ?_ hsum
  exact mode_eq_of_singleton_source_hashes (left g) (right g)
    (fun b j => (L b.val j : F)) (fun c j => (R c.val j : F)) H (root g) (mode g)
    (TernaryOriginalCollisions.surviving_hash_injective _) (TernaryOriginalCollisions.surviving_hash_injective _)
    (hroot g) (hsource g)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedSelectedChain
