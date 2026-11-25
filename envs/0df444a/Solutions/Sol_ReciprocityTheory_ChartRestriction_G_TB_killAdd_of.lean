-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.killAdd_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:05:49.880285+00:00
-- url     : https://prove2.me/submissions/a11acd4b-1957-4c30-b8ff-1fc1599a44d8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateEqTG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_exp_factor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_dAdd_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_dAdd_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_dAdd_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_Gen_kill_gen


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {d n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB
theorem _root_.solution (hQ : QuadColDerivSt) : KillAddSt := by
  intro k _ _ d n ι _ u β P hP m g
  obtain ⟨h0, h1, h2⟩ := hQ k d n β
  obtain ⟨Y, hY⟩ := exp_factor (m • quadCol (n := n) β) (by simp [h0])
  have key := Gen.kill_gen (D := fun p : ι × Fin n => dAdd (u p.1) p.2) (κ := (C : k →+* PS k n d))
    (fun l f g => dAdd_add (u l.1) l.2 f g) (fun l a => dAdd_C (u l.1) l.2 a)
    (fun l f g => dAdd_mul (u l.1) l.2 f g) constantCoeff (fun a => by simp)
    (fun p p' : ι × Fin n => if p.2 = p'.2 then
      dotProduct (u p.1) (β.mulVec (u p'.1)) + dotProduct (u p'.1) (β.mulVec (u p.1)) else 0)
    (quadCol (n := n) β)
    (fun l l' => by
      by_cases h : l.2 = l'.2
      · rw [if_pos h, if_pos h.symm, add_comm]
      · rw [if_neg h, if_neg (Ne.symm h)])
    h0 (fun l => h1 (u l.1) l.2) (fun l l' => h2 (u l.1) (u l'.1) l.2 l'.2) P hP g (m • Y)
  have e : FB.expS k (m • quadCol (n := n) β) * g = g * (1 + quadCol (n := n) β * (m • Y)) := by
    rw [FB.expS, hY, mul_comm, smul_mul_assoc, mul_smul_comm]
  rw [e]
  exact key
end ReciprocityTheory.ChartRestriction.G.TB
