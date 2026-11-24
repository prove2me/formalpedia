-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_mk_mem_locPart_8ee0fd2ff896
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:10.506097+00:00
-- url     : https://prove2.me/submissions/84eef7b9-128b-463d-ae6d-81d692fbbf58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGenSESStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
variable {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
theorem _root_.solution {T : Submonoid (MRingOver S ι)} {c : K → ℤ} (m : M) (t : T) (a : K → ℕ)
    (ht : IsMultiHomog (t : MRingOver S ι) a) (hm : m ∈ 𝓜 (c + fun k => (a k : ℤ))) :
    LocalizedModule.mk m t ∈ KH.locPart ι 𝓜 T c :=
  Submodule.subset_span ⟨m, t, a, ht, hm, rfl⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
