-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_generatedMod_of_subsingleton_6bce206c756e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:30:56.923394+00:00
-- url     : https://prove2.me/submissions/d59fdf24-acd3-4685-8b16-c6e1ee6fb6fd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsKleimanScheme
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GeneratedModOfSubsingleton
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_cell_zero_subsingleton_fd8caf63e24d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_cell_succ_isEmpty_c7809aa49cfb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMultiHomog_one_zero_4334cb17c577

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [∀ k, Subsingleton (ι k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) :
    GeneratedMod S ι 𝓜 d := by
  have := cell_zero_subsingleton (K := K) (ι := ι)
  have := cell_succ_isEmpty (K := K) (ι := ι) 0
  intro I x hx
  let z : KH.CechC S ι M 0 := fun J => (Subsingleton.elim I J ▸ x : LocalizedModule (KH.cellMon S J.1) M)
  refine ⟨1, 0, 1, fun _ => 1, fun _ => z, Submonoid.one_mem _, isMultiHomog_one_zero,
    fun _ => isMultiHomog_one_zero, fun _ => ⟨?_, ?_⟩, ?_⟩
  · intro J _
    obtain rfl : I = J := Subsingleton.elim _ _
    exact hx
  · show KH.cechD S ι M 0 z = 0
    exact funext fun J => (IsEmpty.false J).elim
  · simp only [one_smul, Finset.univ_unique, Finset.sum_singleton]
    rfl
end GroundTheory.Heights₂.Heights.HilbertSamuel
