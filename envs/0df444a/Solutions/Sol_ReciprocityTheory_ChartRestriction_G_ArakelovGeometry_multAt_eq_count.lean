-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.multAt_eq_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:09:30.24763+00:00
-- url     : https://prove2.me/submissions/737d8d95-5730-475c-81c2-b6ee10499db4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DimOfMinimal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_MultAtEqCount
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_le_colon_chain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_length_loc_chain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {J : Ideal (MRing ι)} {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)}
    {f : Fin N → MRing ι} {q : Fin N → Ideal (MRing ι)} (h0 : F 0 = J) (hlast : F (Fin.last N) = ⊤)
    (hj : ∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧ (q j).IsPrime ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc)
    {W' : Ideal (MRing ι)} (hW' : W' ∈ J.minimalPrimes) :
    multAt J W' = ∑ j, if q j = W' then 1 else 0 := by
  classical
  have hp : W'.IsPrime := hW'.1.1
  have hJq : ∀ j, J ≤ q j := le_colon_chain h0 fun j => ⟨(hj j).1, (hj j).2.2⟩
  have hmin : ∀ j, q j ≤ W' → q j = W' := fun j h => le_antisymm h (hW'.2 ⟨(hj j).2.1, hJq j⟩ h)
  have := length_loc_chain W' N F f q hlast hj hmin
  rw [h0] at this
  unfold multAt
  rw [dif_pos hp, this]
  simp
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
