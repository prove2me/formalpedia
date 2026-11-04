-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCompactPairedSupport.support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:41:15.929797+00:00
-- url     : https://prove2.me/submissions/e451ae4a-13cc-4da8-8d51-45c8f6a0a50f

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
import Definitions.Def_Submission_Weighted_Global_TernaryPairedSelectedChain
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryCompactPairedSupport
import Theorems.Thm_ThreeSum_WeightedGlobalCompactPairedSupport_index_not_deleted
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_index_lt
import Theorems.Thm_ThreeSum_WeightedGlobalPairedSelectedChain_surviving_groups_support


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCompactPairedSupport
open LightOriginalSurvivors LightOriginalCollisionCleanup LightOriginalBucketFilter
open TernaryPairedSupportConcrete TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ThreeSum.WeightedGlobalCompactPairedSupport
theorem _root_.solution {F W G : Type*} [Field F] [Fintype F]
    [AddCommGroup W] [Module F W] [Fintype W] [Fintype G] [DecidableEq W]
    {nB nC J K total : ℕ} (keysB keysC : ℕ → ℕ) (B C : ℕ → ℤ)
    (L : Fin nB → Fin J → ℤ) (R : Fin nC → Fin J → ℤ)
    (H : (Fin J → F) →ₗ[F] W) (P : G → Type*) [∀ g, Fintype (P g)]
    (left : ∀ g, P g → Fin (indices keysB nB).length)
    (right : ∀ g, P g → Fin (indices keysC nC).length)
    (root : G → W)
    (hhashB : ∀ a b : Fin nB,
      H (fun j => (L a j : F)) = H (fun j => (L b j : F)) → keysB a.val = keysB b.val)
    (hhashC : ∀ a b : Fin nC,
      H (fun j => (R a j : F)) = H (fun j => (R b j : F)) → keysC a.val = keysC b.val)
    (hroot : ∀ g a,
      H ((fun j => (L ⟨index keysB nB (left g a).val,index_lt (left g a).isLt⟩ j : F))+
         (fun j => (R ⟨index keysC nC (right g a).val,index_lt (right g a).isLt⟩ j : F))) = root g)
    (hraw : ∀ g a b,
      (fun j => (L ⟨index keysB nB (left g a).val,index_lt (left g a).isLt⟩ j : F))+
        (fun j => (R ⟨index keysC nC (right g a).val,index_lt (right g a).isLt⟩ j : F)) =
      (fun j => (L ⟨index keysB nB (left g b).val,index_lt (left g b).isLt⟩ j : F))+
        (fun j => (R ⟨index keysC nC (right g b).val,index_lt (right g b).isLt⟩ j : F)) →
      C (index keysC nC (right g a).val)-B (index keysB nB (left g a).val) =
      C (index keysC nC (right g b).val)-B (index keysB nB (left g b).val))
    (hpotential : (∑ g : G, ∑ e : Fin K → P g,
      rowWeight (tupleMatrix
        (fun a => L ⟨index keysB nB (left g a).val,index_lt (left g a).isLt⟩)
        (fun a => R ⟨index keysC nC (right g a).val,index_lt (right g a).isLt⟩) e)) ≤ total)
    (hzero : total = 0) :
    ∀ g, (TernaryPairedSupport.physicalSupport (fun a : P g =>
      C (index keysC nC (right g a).val)-B (index keysB nB (left g a).val))).card ≤
        2*Fintype.card F^K := by
  let left' (g : G) (a : P g) :
      {b : Fin nB // b ∉ TernaryOriginalCollisions.deleted (fun b => H (fun j => (L b j : F)))} :=
    ⟨⟨index keysB nB (left g a).val,index_lt (left g a).isLt⟩,
      index_not_deleted _ (left g a).isLt hhashB⟩
  let right' (g : G) (a : P g) :
      {c : Fin nC // c ∉ TernaryOriginalCollisions.deleted (fun c => H (fun j => (R c j : F)))} :=
    ⟨⟨index keysC nC (right g a).val,index_lt (right g a).isLt⟩,
      index_not_deleted _ (right g a).isLt hhashC⟩
  apply WeightedGlobalPairedSelectedChain.surviving_groups_support J K total L R H P left' right' root
    (fun g a => C (index keysC nC (right g a).val)-B (index keysB nB (left g a).val))
    hroot hraw ?_ hpotential hzero
  intro g a b hl hr
  have hl' : index keysB nB (left g a).val = index keysB nB (left g b).val :=
    congrArg (fun x => x.val.val) hl
  have hr' : index keysC nC (right g a).val = index keysC nC (right g b).val :=
    congrArg (fun x => x.val.val) hr
  rw [hl',hr']
end ThreeSum.WeightedGlobalCompactPairedSupport
