-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_isParam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:01:04.457424+00:00
-- url     : https://prove2.me/submissions/0c359afb-78a7-4483-a156-070b4eecfd92

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_analyticAt_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_cut
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_indep_grads
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_param_of_cut
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_smul_mem_pts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_surj_of_li


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {z₀ : Ix κ → ℂ} (hz₀ : z₀ ∈ pts (coordIdeal ℤ x)) :
    ∃ (ρ₀ : ℝ) (γ : (Fin D → ℂ) → Ix κ → ℂ), 0 < ρ₀ ∧
      IsParam (coordIdeal ℤ x) (Metric.ball 0 ρ₀) γ ∧ γ 0 = z₀ := by
  classical
  set P := coordIdeal ℤ x with hPdef
  obtain ⟨T, hT, hTd⟩ := hg.smooth z₀ hz₀
  obtain ⟨-, ⟨hprime, -, -⟩, hhor, hdim⟩ := hg.arith
  haveI : P.IsPrime := hprime
  have hTle : D + 1 ≤ Fintype.card (Ix κ) := by
    rw [← hTd, ← Module.finrank_fintype_fun_eq_card ℂ]
    exact Submodule.finrank_le T
  set c := Fintype.card (Ix κ) - (D + 1) with hc
  let e : Ix κ ≃ Fin (D + 1 + c) := Fintype.equivFinOfCardEq (by omega)
  have hhor' : ∀ m : ℤ, (C m : MvPolynomial (Ix κ) ℤ) ∈ P → m = 0 := by
    intro m hm
    have : m ∈ P.comap (C : ℤ →+* MvPolynomial (Ix κ) ℤ) := hm
    rw [hhor] at this
    exact (Submodule.mem_bot ℤ).1 this
  have hdim' : ringKrullDim (MvPolynomial (Ix κ) ℤ ⧸ P) = ((D + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    convert hdim using 3
    simp
  obtain ⟨f, hfP, hli⟩ := gbap_indep_grads e P z₀ T hT hTd
  obtain ⟨F, h, hFli, hph, hiff⟩ := gbap_cut e P hhor' hdim' z₀ hz₀.2 f hfP hli
  set p' : Fin (D + 1 + c) → ℂ := fun j => z₀ (e.symm j) with hp'
  set Z' : Set (Fin (D + 1 + c) → ℂ) := {w | (fun j => w (e j)) ∈ pts P} with hZ'
  have hψ0 : ∀ w : Fin (D + 1 + c) → ℂ, w ≠ 0 → (fun j => w (e j)) ≠ 0 := by
    intro w hw h0
    apply hw
    funext i
    have := congrFun h0 (e.symm i)
    simpa using this
  have hZc : ∀ w ∈ Z', ∀ t : ℂ, t ≠ 0 → t • w ∈ Z' := by
    intro w hw t ht
    exact gbap_smul_mem_pts x hw ht
  have hZ : ∀ w, w ≠ 0 → eval w h ≠ 0 → (w ∈ Z' ↔ ∀ i, eval w (F i) = 0) := by
    intro w hw hwh
    rw [hiff w hwh]
    exact ⟨fun H => H.2, fun H => ⟨hψ0 w hw, H⟩⟩
  have hp'e : (fun j => p' (e j)) = z₀ := by
    funext j
    simp [hp']
  have hp'Z : p' ∈ Z' := by
    show (fun j => p' (e j)) ∈ pts P
    rw [hp'e]
    exact hz₀
  have hp'0 : p' ≠ 0 := by
    intro h0
    apply hz₀.1
    rw [← hp'e, h0]
    rfl
  obtain ⟨ρ₀, γ', hρ₀, hγan, hγZ, ⟨O', q', hO', hq', hOeq, hOc, hqγ⟩, hγ0⟩ :=
    gbap_param_of_cut Z' hZc F h hZ p' hp'Z hp'0 hph (gbap_surj_of_li F p' hFli)
  refine ⟨ρ₀, fun y j => γ' y (e j), hρ₀, ⟨Metric.isOpen_ball, ?_, fun y hy => hγZ y hy,
    {z | (fun i => z (e.symm i)) ∈ O'}, fun z => q' (fun i => z (e.symm i)), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y hy
    exact analyticAt_pi_iff.2 fun j => (gbap_analyticAt_apply (e j) _).comp (hγan y hy)
  · exact hO'.preimage (continuous_pi fun i => continuous_apply _)
  · intro z hz
    exact (hq' _ hz).comp (analyticAt_pi_iff.2 fun i => gbap_analyticAt_apply (e.symm i) z)
  · ext z
    have hzz : (fun j => (fun i => z (e.symm i)) (e j)) = z := by
      funext j
      simp
    constructor
    · rintro ⟨hzO, hzP⟩
      have : (fun i => z (e.symm i)) ∈ O' ∩ Z' := ⟨hzO, by
        show _ ∈ pts P
        rw [hzz]
        exact hzP⟩
      rw [hOeq] at this
      obtain ⟨y, hy, t, ht, hte⟩ := this
      refine ⟨y, hy, t, ht, ?_⟩
      funext j
      have := congrFun hte (e j)
      simpa using this
    · rintro ⟨y, hy, t, ht, rfl⟩
      have hmem : t • γ' y ∈ O' ∩ Z' := by
        rw [hOeq]
        exact ⟨y, hy, t, ht, rfl⟩
      have heq : (fun i => (t • fun j => γ' y (e j)) (e.symm i)) = t • γ' y := by
        funext i
        simp
      refine ⟨?_, ?_⟩
      · show (fun i => (t • fun j => γ' y (e j)) (e.symm i)) ∈ O'
        rw [heq]
        exact hmem.1
      · exact hmem.2
  · intro z hz t ht
    exact hOc _ hz t ht
  · intro y hy
    have : (fun i => γ' y (e (e.symm i))) = γ' y := by
      funext i
      simp
    show q' (fun i => γ' y (e (e.symm i))) = y
    rw [this]
    exact hqγ y hy
  · funext j
    show γ' 0 (e j) = z₀ j
    rw [hγ0]
    simp [hp']
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
