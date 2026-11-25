-- Prove2me | solution 1 for PositivityTheory.RgJS.AbsoluteRigidity.exists_common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:00:47.546839+00:00
-- url     : https://prove2.me/submissions/fe0d2dda-a659-4381-bffd-c4f3e814c844

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_AbsoluteRigidityLemma_AbsoluteRigidityOfCommon
import Theorems.Thm_PositivityTheory_RgJS_AbsoluteRigidity_rel_symm
import Theorems.Thm_PositivityTheory_RgJS_AbsoluteRigidity_rel_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgJS
open PositivityTheory.RgJS.AbsoluteRigidity
variable {W : Type} {q : W → ℕ} {X : Type} {d : X → ℕ} {A : ∀ x, W → Fin (d x) → ℂ}
namespace PositivityTheory.RgJS.AbsoluteRigidity
theorem _root_.solution (hC : Common0) (hS : Sys q X d A) {ι κ : Type} [Fintype ι] [Fintype κ]
    (x : ι → X × ℝ) (y : κ → X × ℝ) (h : Rel q A x y) (hne : Nonempty ι ∨ Nonempty κ) :
    ∃ i j, x i = y j := by
  classical
  set T : Finset ℝ := (Finset.univ.image fun i => (x i).2) ∪ (Finset.univ.image fun j => (y j).2) with hT
  have hTne : T.Nonempty := by
    rcases hne with ⟨⟨i⟩⟩ | ⟨⟨j⟩⟩
    · exact ⟨_, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
    · exact ⟨_, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))⟩
  set τ := T.min' hTne with hτ
  have hx : ∀ i, τ ≤ (x i).2 := fun i =>
    T.min'_le _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hy : ∀ j, τ ≤ (y j).2 := fun j =>
    T.min'_le _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have hmem : τ ∈ T := T.min'_mem hTne
  have hsh := rel_shift hS.primes.two h τ
  have hinj : ∀ p p' : X × ℝ, sh τ p = sh τ p' → p = p' := fun p p' e => by
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only [sh] at e1 e2
    exact Prod.ext e1 (by linarith)
  rcases Finset.mem_union.1 hmem with hm | hm
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hm
    obtain ⟨i', j, e⟩ := hC W q X d A hS ι κ (sh τ ∘ x) (sh τ ∘ y) hsh
      (fun i => by simp only [Function.comp_apply, sh]; linarith [hx i])
      (fun j => by simp only [Function.comp_apply, sh]; linarith [hy j])
      ⟨i, by simp only [Function.comp_apply, sh]; linarith⟩
    exact ⟨i', j, hinj _ _ e⟩
  · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hm
    obtain ⟨j', i, e⟩ := hC W q X d A hS κ ι (sh τ ∘ y) (sh τ ∘ x) (rel_symm hsh)
      (fun j => by simp only [Function.comp_apply, sh]; linarith [hy j])
      (fun i => by simp only [Function.comp_apply, sh]; linarith [hx i])
      ⟨j, by simp only [Function.comp_apply, sh]; linarith⟩
    exact ⟨i, j', (hinj _ _ e).symm⟩
end PositivityTheory.RgJS.AbsoluteRigidity
