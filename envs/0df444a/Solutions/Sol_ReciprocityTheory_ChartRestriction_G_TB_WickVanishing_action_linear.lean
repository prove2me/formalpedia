-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.action_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:47:27.837702+00:00
-- url     : https://prove2.me/submissions/391d4b81-774e-4998-bdc1-51f1dd608cf2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_hom_at
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_dLin_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_add_at
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_addition_linear
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_cc_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_dLin_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_germComp1_germComp1_eq_substitute


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
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]
open Formalism.FG.SolveVAux
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution : ActLinSt := by
  have single_of_degree : ∀ {σ : Type} (n : σ →₀ ℕ), n.degree = 1 → ∃ p, n = Finsupp.single p 1 := by
    intro σ n h
    classical
    have hc : Multiset.card (Finsupp.toMultiset n) = 1 := by
      rw [Finsupp.card_toMultiset, ← h]
      rfl
    obtain ⟨p, hp⟩ := Multiset.card_eq_one.mp hc
    refine ⟨p, ?_⟩
    have h2 := congrArg Multiset.toFinsupp hp
    rw [Finsupp.toMultiset_toFinsupp, Multiset.toFinsupp_singleton] at h2
    exact h2
  intro k _ _ d O _ _ B ℓ ε hℓ0 hℓ1 hadd hinv a i
  obtain ⟨hε0, -, hεℓ, hℓε⟩ := hinv
  have hA0 : ∀ i, constantCoeff (B.A.act a i) = 0 := B.A.const a
  have hcc1 : ∀ {n : ℕ} (φ : Pt k 1 d) (w : Pt k n d), (∀ i, constantCoeff (φ i) = 0) →
      (∀ i, constantCoeff (w i) = 0) → ∀ i, constantCoeff (comp1 φ w i) = 0 := fun φ w hφ hw i =>
    cc_ev _ (fun j l => by fin_cases j; exact hw l) (hφ i)
  have hccA : ∀ {n : ℕ} (u v : Pt k n d), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      ∀ i, constantCoeff (addOf B.G.F u v i) = 0 := fun u v hu hv i =>
    cc_ev _ (fun j l => by
      fin_cases j
      · exact hu l
      · exact hv l) (B.G.const i)
  have hpt : ∀ {n : ℕ} (w : Pt k n d), (∀ i, constantCoeff (w i) = 0) → comp1 (pt k (n := 1) d 0) w = w := by
    intro n w hw
    funext i
    exact ev_X _ (fun j l => by fin_cases j; exact hw l) 0 i
  have hx : ∀ i, constantCoeff (pt k (n := 2) d 0 i) = 0 := fun i => MvPowerSeries.constantCoeff_X _
  have hy : ∀ i, constantCoeff (pt k (n := 2) d 1 i) = 0 := fun i => MvPowerSeries.constantCoeff_X _
  have hxy : ∀ i, constantCoeff ((pt k (n := 2) d 0 + pt k (n := 2) d 1) i) = 0 := fun i => by
    simp [pt]
  have hεx := hcc1 ε _ hε0 hx
  have hεy := hcc1 ε _ hε0 hy
  have hAε : ∀ i, constantCoeff (comp1 (B.A.act a) ε i) = 0 := hcc1 _ _ hA0 hε0
  have S1 : comp1 ℓ (addOf B.G.F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1))) =
      pt k (n := 2) d 0 + pt k (n := 2) d 1 := by
    rw [add_at B.G ℓ hadd _ _ hεx hεy, germComp1_germComp1_eq_substitute ℓ ε _ hε0 hx, germComp1_germComp1_eq_substitute ℓ ε _ hε0 hy, hℓε, hpt _ hx, hpt _ hy]
  have S2 : comp1 ε (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      addOf B.G.F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1)) := by
    rw [← S1, germComp1_germComp1_eq_substitute ε ℓ _ hℓ0 (hccA _ _ hεx hεy), hεℓ, hpt _ (hccA _ _ hεx hεy)]
  have S4 : comp1 ℓ (comp1 (B.A.act a) (comp1 ε (pt k (n := 2) d 0 + pt k (n := 2) d 1))) =
      comp1 ℓ (comp1 (B.A.act a) (comp1 ε (pt k (n := 2) d 0))) +
        comp1 ℓ (comp1 (B.A.act a) (comp1 ε (pt k (n := 2) d 1))) := by
    rw [S2, hom_at B.G B.A a _ _ hεx hεy, add_at B.G ℓ hadd _ _ (hcc1 _ _ hA0 hεx) (hcc1 _ _ hA0 hεy)]
  have hF : ∀ w : Pt k 2 d, (∀ i, constantCoeff (w i) = 0) →
      comp1 (comp1 ℓ (comp1 (B.A.act a) ε)) w = comp1 ℓ (comp1 (B.A.act a) (comp1 ε w)) := by
    intro w hw
    rw [← germComp1_germComp1_eq_substitute _ _ _ hAε hw, ← germComp1_germComp1_eq_substitute _ _ _ hε0 hw]
  have hfadd : comp1 (comp1 ℓ (comp1 (B.A.act a) ε)) (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      comp1 (comp1 ℓ (comp1 (B.A.act a) ε)) (pt k (n := 2) d 0) +
        comp1 (comp1 ℓ (comp1 (B.A.act a) ε)) (pt k (n := 2) d 1) := by
    rw [hF _ hxy, hF _ hx, hF _ hy]
    exact S4
  have hlin := addition_linear k d (comp1 ℓ (comp1 (B.A.act a) ε) i) (congrFun hfadd i)
  have hdε : dLin ε = 1 := by
    have h := dLin_comp1 ε ℓ hℓ0
    rw [hεℓ, dLin_pt, hℓ1, mul_one] at h
    exact h.symm
  have hdf : dLin (comp1 ℓ (comp1 (B.A.act a) ε)) = dLin (B.A.act a) := by
    rw [dLin_comp1 ℓ _ hAε, dLin_comp1 _ ε hε0, hℓ1, hdε, one_mul, mul_one]
  ext n
  rw [map_sum]
  simp only [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  by_cases hn : n.degree = 1
  · obtain ⟨p, rfl⟩ := single_of_degree n hn
    obtain ⟨z, j0⟩ := p
    obtain rfl : z = 0 := Subsingleton.elim _ _
    have h1 : MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j0) 1) (comp1 ℓ (comp1 (B.A.act a) ε) i) =
        dLin (B.A.act a) i j0 := by
      rw [← hdf]
      rfl
    rw [h1, Finset.sum_eq_single j0]
    · simp
    · intro j _ hj
      rw [if_neg, mul_zero]
      intro h
      apply hj
      have h2 := (Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)).mp h
      exact (Prod.mk.inj h2).2.symm
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [hlin n hn]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg, mul_zero]
    rintro rfl
    exact hn (Finsupp.degree_single _ _)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
