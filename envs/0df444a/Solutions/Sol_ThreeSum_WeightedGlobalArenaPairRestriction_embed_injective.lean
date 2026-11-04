-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPairRestriction.embed_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:59:24.586195+00:00
-- url     : https://prove2.me/submissions/67111752-dc34-4a24-bbac-27eb17403766

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairRestriction
import Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_mem_records
attribute [local simp] ThreeSum.TernarySourceHostModel.mem_records
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.mem_records



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPairRestriction
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open WeightedGlobalNativePairMoments WeightedGlobalNativeTensorScore
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (nB nC : ℕ) (fB fC : ℕ→ℕ)
    (hB : ∀ i<nB, fB i<I.nB) (hC : ∀ i<nC, fC i<I.nC)
include hB hC
namespace ThreeSum.WeightedGlobalArenaPairRestriction
theorem _root_.solution
    (hfB : ∀ a<nB, ∀ b<nB, fB a=fB b→a=b)
    (hfC : ∀ a<nC, ∀ b<nC, fC a=fC b→a=b) (i : ℕ) :
    Function.Injective (embed (r := r) maps τ cap Q I nB nC fB fC hB hC (i := i)) := by
  intro x y he
  apply Subtype.ext
  have hxy := congrArg Subtype.val he
  change ((fB x.val.1.1,x.val.1.2),(fC x.val.2.1,x.val.2.2))=
    ((fB y.val.1.1,y.val.1.2),(fC y.val.2.1,y.val.2.2)) at hxy
  have xL := ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp
    (mem_filter.mp (mem_product.mp (mem_filter.mp x.property).1).1).1).1
  have yL := ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp
    (mem_filter.mp (mem_product.mp (mem_filter.mp y.property).1).1).1).1
  have xR := ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp
    (mem_filter.mp (mem_product.mp (mem_filter.mp x.property).1).2).1).1
  have yR := ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp
    (mem_filter.mp (mem_product.mp (mem_filter.mp y.property).1).2).1).1
  have hL2 := congrArg (fun z : (ℕ×ℕ)×(ℕ×ℕ) => z.1.2) hxy
  have hR2 := congrArg (fun z : (ℕ×ℕ)×(ℕ×ℕ) => z.2.2) hxy
  change x.val.1.2=y.val.1.2 at hL2
  change x.val.2.2=y.val.2.2 at hR2
  apply Prod.ext
  · exact Prod.ext (hfB _ xL _ yL (congrArg (fun z : (ℕ×ℕ)×(ℕ×ℕ) => z.1.1) hxy))
      hL2
  · exact Prod.ext (hfC _ xR _ yR (congrArg (fun z : (ℕ×ℕ)×(ℕ×ℕ) => z.2.1) hxy))
      hR2
end ThreeSum.WeightedGlobalArenaPairRestriction
