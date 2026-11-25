-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_smul_mem_locPart_91dd9ddd0d34
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:54.936298+00:00
-- url     : https://prove2.me/submissions/c9ff5c1d-d06c-4d2e-bc8a-8b15488c288d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGenSESStep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_mk_mem_locPart_8ee0fd2ff896
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_locPart_normal_f08e45df3bf5

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
theorem _root_.solution (h𝓜 : KH.IsMGraded S ι 𝓜) {T : Submonoid (MRingOver S ι)} {c : K → ℤ}
    {p : MRingOver S ι} {a : K → ℕ} (hp : IsMultiHomog p a) {x : LocalizedModule T M}
    (hx : x ∈ KH.locPart ι 𝓜 T c) : p • x ∈ KH.locPart ι 𝓜 T (c + fun k => (a k : ℤ)) := by
  obtain ⟨m, t, b, ht, hm, rfl⟩ := locPart_normal h𝓜 hx
  rw [LocalizedModule.smul'_mk]
  refine mk_mem_locPart _ t b ht ?_
  have e : ((c + fun k => (a k : ℤ)) + fun k => (b k : ℤ)) =
      (c + fun k => (b k : ℤ)) + fun k => (a k : ℤ) := by
    funext k
    simp only [Pi.add_apply]
    ring
  rw [e]
  exact h𝓜.2 _ _ _ _ hp hm
end GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
