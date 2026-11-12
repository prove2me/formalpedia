-- Prove2me | solution 1 for RamseyDisambig.Spherical.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:03:10.366208+00:00
-- url     : https://prove2.me/submissions/34f0bc7e-66be-4739-89cc-845782db5ad5

import Mathlib
import Definitions.Def_RamseyDisambig_Spherical_GapColoring
import Definitions.Def_NatureSLT_GrowthFunction_vcDim

section
set_option autoImplicit false

namespace RamseyDisambig.Dev.Basics

open RamseyDisambig.Spherical NatureSLT.GrowthFunction

/-- If `q ≤ vcDim Q` then some `q` points are shattered. -/
theorem exists_shattered_of_le_vcDim {Z Λ : Type*} (Q : Λ → Z → Bool) (q : ℕ) (hq1 : 1 ≤ q)
    (h : (q : ℕ∞) ≤ vcDim Q) : ∃ z : Fin q → Z, Shatters Q z := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ (h' : ℕ), (∃ z : Fin h' → Z, Shatters Q z) → h' < q := by
    intro h' ⟨z, hz⟩
    by_contra hlt
    push_neg at hlt
    apply hcon (fun i => z (Fin.castLE hlt i))
    intro δ
    obtain ⟨α, hα⟩ := hz (fun j => if hj : (j : ℕ) < q then δ ⟨j, hj⟩ else false)
    refine ⟨α, fun i => ?_⟩
    have := hα (Fin.castLE hlt i)
    simpa using this
  have hle : vcDim Q ≤ ((q - 1 : ℕ) : ℕ∞) := by
    unfold vcDim
    refine iSup₂_le fun h' hh' => ?_
    have := key h' hh'
    exact_mod_cast Nat.le_sub_one_of_lt this
  have hq : (q : ℕ∞) ≤ ((q - 1 : ℕ) : ℕ∞) := h.trans hle
  have hq' : q ≤ q - 1 := by exact_mod_cast hq
  omega

/-- Shattered family gives vcDim ≥ its size. -/
theorem le_vcDim_of_shatters {Z Λ : Type*} (Q : Λ → Z → Bool) {h : ℕ} (z : Fin h → Z)
    (hz : Shatters Q z) : (h : ℕ∞) ≤ vcDim Q := by
  unfold vcDim
  exact le_iSup₂_of_le h ⟨z, hz⟩ le_rfl

end RamseyDisambig.Dev.Basics
end

section
set_option autoImplicit false

namespace RamseyDisambig.Dev.L10

open NatureSLT.GrowthFunction

/-- Pullback form usable with `q = 0`-free hypothesis. -/
theorem vcDim_pullback {X Y : Type*} (ι₁ ι₂ : Y → X) (c : X → X → Bool)
    (q : ℕ) (hq : 1 ≤ q)
    (hvc : (q : ℕ∞) ≤ vcDim (fun y y' => c (ι₁ y) (ι₂ y'))) :
    (q : ℕ∞) ≤ vcDim c := by
  obtain ⟨z, hz⟩ := Basics.exists_shattered_of_le_vcDim _ q hq hvc
  refine Basics.le_vcDim_of_shatters c (fun i => ι₂ (z i)) ?_
  intro δ
  obtain ⟨α, hα⟩ := hz δ
  exact ⟨ι₁ α, hα⟩

end RamseyDisambig.Dev.L10

namespace RamseyDisambig.Spherical

theorem chk_lemma_10 {X Y : Type*} (ι₁ ι₂ : Y → X) (c : X → X → Bool)
    (q : ℕ) (hq : 1 ≤ q)
    (hvc : (q : ℕ∞) ≤ NatureSLT.GrowthFunction.vcDim (fun y y' => c (ι₁ y) (ι₂ y'))) :
    (q : ℕ∞) ≤ NatureSLT.GrowthFunction.vcDim c :=
  RamseyDisambig.Dev.L10.vcDim_pullback ι₁ ι₂ c q hq hvc

end RamseyDisambig.Spherical
end

theorem solution : type_of% @RamseyDisambig.Spherical.chk_lemma_10 := @RamseyDisambig.Spherical.chk_lemma_10
