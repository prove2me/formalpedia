-- Prove2me | solution 1 for ProcessingNetworks.BackPressure.bp_characteristic_fluid_equation
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:27:35.59599+00:00
-- url     : https://prove2.me/submissions/f7eb2c4b-2787-433c-b6ad-4c19b308c220

import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork
import Definitions.Def_ProcessingNetworks_BackPressure_AllocationPolytope
import Definitions.Def_ProcessingNetworks_BackPressure_RegularPoint
import Definitions.Def_ProcessingNetworks_BackPressure_FluidModelSolution

open Filter

namespace ProcessingNetworks.BackPressure.BPCharCE

open ProcessingNetworks.BackPressure

noncomputable def dat : SPNPlanningData 1 1 1 :=
  { B := 1, Γ := 0, m := fun _ => 1, hm := fun _ => one_pos, A := 0, b := fun _ => 1,
    hb := fun _ => one_pos }

theorem R_eq : dat.R = 1 := by
  ext i j; fin_cases i; fin_cases j
  simp [SPNPlanningData.R, dat]

theorem h91 : SatisfiesAssumption91 dat := by
  intro j
  refine ⟨0, ?_, fun i _ => Subsingleton.elim i 0⟩
  rw [R_eq]; fin_cases j; exact one_pos

theorem p_eq (β z : Fin 1 → ℝ) : p dat β z = z 0 * β 0 := by
  simp [p, R_eq, dotProduct]

theorem mem_poly (x : Fin 1 → ℝ) : x ∈ AllocationPolytope dat ↔ 0 ≤ x 0 := by
  constructor
  · intro h; exact h.1 0
  · intro h
    refine ⟨fun j => by fin_cases j; exact h, fun k => by simp [dat]⟩

theorem ext1 {x y : Fin 1 → ℝ} (h : x 0 = y 0) : x = y := by
  funext i; fin_cases i; exact h

theorem extreme_eq : ExtremeAllocations dat = {0} := by
  ext x
  simp only [ExtremeAllocations, Set.mem_singleton_iff, mem_extremePoints, mem_poly]
  constructor
  · rintro ⟨hx, hext⟩
    by_contra hne
    have hpos : 0 < x 0 := lt_of_le_of_ne hx (fun h => hne (ext1 (by simpa using h.symm)))
    have hseg : x ∈ openSegment ℝ ((1 / 2 : ℝ) • x) ((3 / 2 : ℝ) • x) := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      funext i; simp; ring
    have := (hext _ (by simp; positivity) _ (by simp; positivity) hseg).1
    have h0 := congrFun this 0
    simp at h0
    linarith
  · rintro rfl
    refine ⟨le_refl _, fun x1 h1 x2 h2 hseg => ?_⟩
    obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
    have e := congrFun heq 0
    simp at e
    have hx1 : x1 0 = 0 := by nlinarith
    have hx2 : x2 0 = 0 := by nlinarith
    exact ⟨ext1 (by simpa using hx1), ext1 (by simpa using hx2)⟩

end ProcessingNetworks.BackPressure.BPCharCE

open ProcessingNetworks.BackPressure in
theorem solution : ¬ (∀ {I J K : ℕ} (dat : SPNPlanningData I J K) (h91 : SatisfiesAssumption91 dat)
    (lam : Fin I → ℝ)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = ExtremeAllocations dat)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ)
    (hsol : IsFluidModelSolution dat lam Dh Fh Th Zh)
    (Yh : (Fin J → ℝ) → ℝ → ℝ)
    (hTY : ∀ t : ℝ, 0 ≤ t → ∀ j, Th t j = ∑ β ∈ E, β j * Yh β t)
    (hYmono : ∀ β ∈ E, Monotone (Yh β))
    (hYsum : ∀ t : ℝ, 0 ≤ t → ∑ β ∈ E, Yh β t = t)
    (hYopt : ∀ β ∈ E, ∀ t : ℝ, 0 < t → p dat β (Zh t) < ⨆ α ∈ E, p dat α (Zh t) →
      ∀ d : ℝ, HasDerivAt (Yh β) d t → d = 0)
    (t : ℝ) (ht : 0 < t) (hreg : RegularPoint Dh Fh Th Zh t)
    (hYreg : ∀ β ∈ E, DifferentiableAt ℝ (Yh β) t),
    ∀ d : Fin J → ℝ, HasDerivAt Th d t → IsZMaximal dat d (Zh t)) := by
  intro h
  open BPCharCE in
  have hsol : IsFluidModelSolution dat (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0)
      (fun t _ => 1 + t) := by
    refine ⟨fun t _ i => by simp, fun t ht i => by linarith, fun t _ i => by simp,
      fun t _ j => by simp, ⟨rfl, fun _ _ _ => le_refl _⟩, fun s t _ hst k => ?_⟩
    simp [dat]; linarith
  have hE : ((({0} : Finset (Fin 1 → ℝ))) : Set (Fin 1 → ℝ)) = ExtremeAllocations BPCharCE.dat := by
    rw [BPCharCE.extreme_eq]; simp
  have key := h BPCharCE.dat BPCharCE.h91 (fun _ => 1) {0} hE _ _ _ _ hsol (fun _ t => t)
    (fun t _ j => by simp) (fun _ _ _ _ hab => hab) (fun t _ => by simp)
    (fun β hβ t _ hlt => by
      exfalso
      rw [Finset.mem_singleton] at hβ
      subst hβ
      have hle : (⨆ α ∈ ({0} : Finset (Fin 1 → ℝ)), p BPCharCE.dat α (fun _ => 1 + t)) ≤ 0 := by
        refine Real.iSup_le (fun α => Real.iSup_le (fun hα => ?_) le_rfl) le_rfl
        rw [Finset.mem_singleton] at hα
        subst hα
        simp [BPCharCE.p_eq]
      have : p BPCharCE.dat 0 (fun _ => 1 + t) = 0 := by simp [BPCharCE.p_eq]
      linarith)
    1 one_pos
    ⟨differentiableAt_const _, differentiableAt_const _, differentiableAt_const _,
      differentiableAt_pi.mpr fun _ => (differentiableAt_const _).add differentiableAt_id⟩
    (fun _ _ => differentiableAt_id) 0 (hasDerivAt_const _ _)
  have hα : (fun _ => (1 : ℝ)) ∈ AllocationPolytope BPCharCE.dat :=
    (BPCharCE.mem_poly _).mpr zero_le_one
  have := key.2 _ hα
  rw [BPCharCE.p_eq, BPCharCE.p_eq] at this
  norm_num at this


