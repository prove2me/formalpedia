-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.good_SU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:17:48.024075+00:00
-- url     : https://prove2.me/submissions/4cf520ac-da93-40be-b756-ff10ea91d5df

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_closure_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_mem_closure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {δ : K} (hδ : IsUnit δ) (hσδ : σ δ = -δ) {g : Matrix ι ι K}
    (hg : g ∈ Good σ J e f) (hdet : g.det = 1) : g ∈ Submonoid.closure (eichSet σ J e f) := by
  obtain ⟨n, hn, l, m, hml, rfl⟩ := hg
  have hn1 : n.det = 1 := (closure_sub hσ hJ he hff hn).1
  rw [det_mul, hn1, one_mul, tor_det hσ hJ he hff hef] at hdet
  have hl : σ l = l := by
    calc σ l = (l * m) * σ l := by rw [hdet, one_mul]
      _ = l * (m * σ l) := by ring
      _ = l := by rw [hml, mul_one]
  obtain ⟨di, hdi⟩ := hδ.exists_right_inv
  exact Submonoid.mul_mem _ hn (tor_mem_closure hσ hJ he hff hef hσδ hdi hl hdet)
end ReciprocityTheory.ChartRestriction.G.SA
