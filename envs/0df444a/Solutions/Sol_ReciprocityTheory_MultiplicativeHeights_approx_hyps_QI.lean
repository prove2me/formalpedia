-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approx_hyps_QI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:31:19.5758+00:00
-- url     : https://prove2.me/submissions/a538eb40-154c-4e0b-ac86-89a3a02a388d

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatTest
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_mem_intLat
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_hermQI_h
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_cover_QI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (φ : QI →+* ℂ) :
    let σ : Unit → QI →+* ℂ := fun _ => φ
    let Q : Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 1
    let v : Fin 1 → Fin 1 → QI := fun _ _ => 1
    1 ≤ 1 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧ (∀ i, (Q i).det ≠ 0) ∧
    (∀ i x y, σ i (hermQI.h x y) =
      jForm 1 (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y)) ∧
    IsIntegralOn hermQI (intLat QI 1) ∧
    (∀ w : Unit → Fin 1 → ℂ, ∃ l ∈ intLat QI 1,
      ∑ i, normSq (Q i *ᵥ embVec (σ i) l - w i) ≤ (1 : ℝ) ^ 2) ∧
    (∀ j, v j ∈ intLat QI 1) ∧ LinearIndependent QI v ∧
    (∀ j, majSq σ Q (v j) ≤ (1 : ℝ) ^ 2) := by
  intro σ Q v
  refine ⟨le_rfl, one_pos, one_pos, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [Q]
  · intro i x y
    show φ (hermQI.h x y) = _
    rw [hermQI_h, map_mul, IsCMField.complexEmbedding_complexConj]
    simp [jForm, sgn, embVec, Q, σ]
  · intro x hx y hy
    rw [hermQI_h]
    rw [mem_intLat] at hx hy
    obtain ⟨z0, hz0⟩ := hx 0
    obtain ⟨z1, hz1⟩ := hy 0
    have hi : IsIntegral ℤ (IsCMField.complexConj QI (z0 : QI)) := by
      have := (NumberField.RingOfIntegers.isIntegral_coe z0).map
        ((IsCMField.complexConj QI : QI →+* QI)).toIntAlgHom
      simpa using this
    refine ⟨⟨_, hi⟩ * z1, ?_⟩
    show (IsCMField.complexConj QI (z0 : QI)) * (z1 : QI) = _
    rw [hz0, hz1]
  · intro w
    obtain ⟨l, hl, hn⟩ := cover_QI φ (w () 0)
    refine ⟨fun _ => l, (mem_intLat _).2 (fun _ => hl), ?_⟩
    simpa [normSq, embVec, Q, σ] using hn
  · intro j
    rw [mem_intLat]
    intro a
    exact ⟨1, by simp [v]⟩
  · refine linearIndependent_unique_iff.2 ?_
    intro h
    have := congrFun h 0
    simp [v] at this
  · intro j
    simp [majSq, normSq, embVec, Q, σ, v]
end ReciprocityTheory.MultiplicativeHeights
