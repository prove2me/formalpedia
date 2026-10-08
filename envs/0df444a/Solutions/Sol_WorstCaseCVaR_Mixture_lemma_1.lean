-- Prove2me | solution 1 for WorstCaseCVaR.Mixture.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T04:31:21.337062+00:00
-- url     : https://prove2.me/submissions/fb0c25a9-0f49-478a-aa28-9015e71c7627

import Definitions.Def_WorstCaseCVaR_Mixture_Setting

section
set_option autoImplicit false
open MeasureTheory
namespace MixtureCodex

theorem lemma_1 {m n : ℕ} (X : Set (Fin n → ℝ)) (Y : Set (Fin m → ℝ))
    (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (hYne : Y.Nonempty) (hYc : IsCompact Y) (hYcv : Convex ℝ Y)
    (φ : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hconv : ∀ y ∈ Y, ConvexOn ℝ X (fun x => φ x y))
    (hconc : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => φ x y))
    (hlsc : ∀ y ∈ Y, LowerSemicontinuousOn (fun x => φ x y) X)
    (husc : ∀ x ∈ X, UpperSemicontinuousOn (fun y => φ x y) Y) :
    ∃ x₀ ∈ X, ∃ y₀ ∈ Y,
      IsLeast ((fun x => sSup ((fun y => φ x y) '' Y)) '' X) (φ x₀ y₀) ∧
        IsGreatest ((fun y => sInf ((fun x => φ x y) '' X)) '' Y) (φ x₀ y₀) := by
  obtain ⟨a,ha,b,hb,hs⟩ := Sion.exists_isSaddlePointOn hXne hXcv hXc hlsc
    (fun y hy ↦ (hconv y hy).quasiconvexOn) hYcv hYne hYc husc
    (fun x hx ↦ (hconc x hx).quasiconcaveOn)
  have hrow (x) (hx : x ∈ X) : BddAbove ((fun y ↦ φ x y) '' Y) := by
    obtain ⟨y,hy,hm⟩ := (husc x hx).exists_isMaxOn hYne hYc
    exact hm.bddAbove
  have hcol (y) (hy : y ∈ Y) : BddBelow ((fun x ↦ φ x y) '' X) := by
    obtain ⟨x,hx,hm⟩ := (hlsc y hy).exists_isMinOn hXne hXc
    exact hm.bddBelow
  have hr : sSup ((fun y ↦ φ a y) '' Y) = φ a b := by
    refine le_antisymm ?_ (le_csSup (hrow a ha) ⟨b,hb,rfl⟩)
    apply csSup_le (hYne.image _)
    rintro y ⟨z,hz,rfl⟩
    exact hs a ha z hz
  have hc : sInf ((fun x ↦ φ x b) '' X) = φ a b := by
    refine le_antisymm (csInf_le (hcol b hb) ⟨a,ha,rfl⟩) ?_
    apply le_csInf (hXne.image _)
    rintro x ⟨z,hz,rfl⟩
    exact hs z hz b hb
  refine ⟨a,ha,b,hb,⟨⟨a,ha,hr⟩,?_⟩,⟨⟨b,hb,hc⟩,?_⟩⟩
  · rintro y ⟨x,hx,rfl⟩
    exact (hs x hx b hb).trans (le_csSup (hrow x hx) ⟨b,hb,rfl⟩)
  · rintro x ⟨y,hy,rfl⟩
    exact (csInf_le (hcol y hy) ⟨a,ha,rfl⟩).trans (hs a ha y hy)


end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory WorstCaseCVaR.Mixture
theorem solution {m n : ℕ} (X : Set (Fin n → ℝ)) (Y : Set (Fin m → ℝ))
    (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (hYne : Y.Nonempty) (hYc : IsCompact Y) (hYcv : Convex ℝ Y)
    (φ : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hconv : ∀ y ∈ Y, ConvexOn ℝ X (fun x => φ x y))
    (hconc : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => φ x y))
    (hlsc : ∀ y ∈ Y, LowerSemicontinuousOn (fun x => φ x y) X)
    (husc : ∀ x ∈ X, UpperSemicontinuousOn (fun y => φ x y) Y) :
    ∃ x₀ ∈ X, ∃ y₀ ∈ Y,
      IsLeast ((fun x => sSup ((fun y => φ x y) '' Y)) '' X) (φ x₀ y₀) ∧
        IsGreatest ((fun y => sInf ((fun x => φ x y) '' X)) '' Y) (φ x₀ y₀) := MixtureCodex.lemma_1 X Y hXne hXc hXcv hYne hYc hYcv φ hconv hconc hlsc husc

end

#print axioms solution
