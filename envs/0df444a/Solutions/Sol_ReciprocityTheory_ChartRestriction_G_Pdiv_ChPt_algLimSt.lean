-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt.algLimSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:24:51.832433+00:00
-- url     : https://prove2.me/submissions/4a4d1daa-5346-4b19-986f-e173453f7aff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_InChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_EqOfMod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_ChPt_smod_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_ChPt_eq_of_mod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext


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
open IsLocalRing MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.Chart (jetLift jetLift_zR jet_ext)
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
theorem _root_.solution : AlgLimSt := by
  intro T A O _ _ _ _ _ p hC a hc
  have hdown : ∀ z : A, ∀ m n : ℕ, m ≤ n → ∀ y : O,
      Ideal.Quotient.mk (Ideal.span {p ^ n}) y = a n z →
        Ideal.Quotient.mk (Ideal.span {p ^ m}) y = a m z := by
    intro z m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact fun y hy => hy
    | succ n _ ih => exact fun y hy => ih y (hc n z y hy)
  have hlim : ∀ z : A, ∃ L : O, ∀ n, Ideal.Quotient.mk (Ideal.span {p ^ n}) L = a n z := by
    intro z
    have hs : ∀ n, ∃ y : O, Ideal.Quotient.mk (Ideal.span {p ^ n}) y = a n z :=
      fun n => Ideal.Quotient.mk_surjective (a n z)
    choose y hy using hs
    obtain ⟨L, hL⟩ := hC.toIsPrecomplete.prec' y (fun {m n} hmn =>
      (smod_iff p m (y m) (y n)).mpr (by rw [hy m, hdown z m n hmn (y n) (hy n)]))
    exact ⟨L, fun n => by rw [← (smod_iff p n (y n) L).mp (hL n), hy n]⟩
  choose L hL using hlim
  have huniq : ∀ x y : O, (∀ n : ℕ, Ideal.Quotient.mk (Ideal.span {p ^ n}) x =
      Ideal.Quotient.mk (Ideal.span {p ^ n}) y) → x = y :=
    fun x y H => eq_of_mod p hC.toIsHausdorff x y H
  refine ⟨
    { toFun := L
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_
      commutes' := ?_ }, ?_⟩
  · exact huniq _ _ fun n => by simp only [hL, map_one]
  · intro x y
    exact huniq _ _ fun n => by simp only [hL, map_mul]
  · exact huniq _ _ fun n => by simp only [hL, map_zero]
  · intro x y
    exact huniq _ _ fun n => by simp only [hL, map_add]
  · intro t
    refine huniq _ _ fun n => ?_
    rw [hL, AlgHom.commutes]
    exact ((Ideal.Quotient.mkₐ T (Ideal.span {p ^ n})).commutes t).symm
  · intro n
    ext z
    exact hL z n
end ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
