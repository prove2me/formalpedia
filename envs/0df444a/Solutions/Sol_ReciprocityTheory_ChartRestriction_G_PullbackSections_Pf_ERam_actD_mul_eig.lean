-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.actD_mul_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:25.486589+00:00
-- url     : https://prove2.me/submissions/0ffd350e-2bdd-46df-b537-4038897b2c35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_eig_actD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_M_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {O k : Type} [CommRing O] [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution (M : O →+* Matrix (Fin d) (Fin d) k) (χ : O →+* k) {n n' : ℕ} (b : Fin n → O) (c : Fin n → k)
    (h : IsEqv χ b c) (b' : Fin n' → O) (c' : Fin n' → k) :
    actD M b c * actD M b' c' = evD χ b' c' • actD M b c := by
  have hc : ∀ x, actD M b c * M x = M x * actD M b c := by
    intro x
    unfold actD
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, M_comm]
  show actD M b c * ∑ j, c' j • M (b' j) = _
  rw [Finset.mul_sum, evD, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_smul, hc, eig_actD M χ b c h, smul_smul]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
