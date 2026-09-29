-- Prove2me | solution 1 for ValuativeSYZ.thm_4_5_kantorovich_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T19:46:43.928337+00:00
-- url     : https://prove2.me/submissions/e13c89d3-446a-4ff3-8456-aa0de6be4a62

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

/-! 5437a725 ValuativeSYZ.thm_4_5_kantorovich_bound: Kantorovich weak duality.
Pointwise c x p ≤ φᶜ(p) + φ(x) (the sup defining φᶜ is bounded above by 2M);
integrate against the coupling π and push the two marginal integrals forward
along Prod.fst / Prod.snd. All integrands are bounded measurable, hence integrable
for the probability measure π. No `Theorems.*` module is imported. -/

set_option autoImplicit false

open MeasureTheory

open MeasureTheory ValuativeSYZ in
theorem solution {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    [Nonempty X] (c : X → B → ℝ) (M : ℝ) (hc : ∀ x p, |c x p| ≤ M)
    (hcmeas : Measurable fun z : X × B => c z.1 z.2)
    (φ : X → ℝ) (hφ : ∀ x, |φ x| ≤ M) (hφmeas : Measurable φ)
    (htmeas : Measurable (ctransform c φ))
    (μ : Measure X) (ν : Measure B) (π : Measure (X × B))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure π]
    (hπ₁ : π.map Prod.fst = μ) (hπ₂ : π.map Prod.snd = ν) :
    ∫ z, c z.1 z.2 ∂π ≤ (∫ p, ctransform c φ p ∂ν) + ∫ x, φ x ∂μ := by
  have hbdd : ∀ p : B, BddAbove (Set.range fun x : X => c x p - φ x) := by
    intro p
    refine ⟨M + M, ?_⟩
    rintro _ ⟨x, rfl⟩
    have h1 := (abs_le.mp (hc x p)).2
    have h2 := (abs_le.mp (hφ x)).1
    show c x p - φ x ≤ M + M
    linarith
  have hpt : ∀ x p, c x p ≤ ctransform c φ p + φ x := by
    intro x p
    have := le_ciSup (hbdd p) x
    unfold ctransform
    linarith
  have htb : ∀ p, ‖ctransform c φ p‖ ≤ M + M := by
    intro p
    obtain ⟨x0⟩ := ‹Nonempty X›
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h0 := le_ciSup (hbdd p) x0
      have h1 := (abs_le.mp (hc x0 p)).1
      have h2 := (abs_le.mp (hφ x0)).2
      unfold ctransform
      linarith
    · unfold ctransform
      refine ciSup_le fun x => ?_
      have h1 := (abs_le.mp (hc x p)).2
      have h2 := (abs_le.mp (hφ x)).1
      linarith
  have hcI : Integrable (fun z : X × B => c z.1 z.2) π := by
    refine Integrable.of_bound hcmeas.aestronglyMeasurable M ?_
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hc z.1 z.2
  have htI : Integrable (fun z : X × B => ctransform c φ z.2) π := by
    refine Integrable.of_bound (htmeas.comp measurable_snd).aestronglyMeasurable (M + M) ?_
    exact Filter.Eventually.of_forall fun z => htb z.2
  have hφI : Integrable (fun z : X × B => φ z.1) π := by
    refine Integrable.of_bound (hφmeas.comp measurable_fst).aestronglyMeasurable M ?_
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hφ z.1
  have e1 : ∫ p, ctransform c φ p ∂ν = ∫ z, ctransform c φ z.2 ∂π := by
    rw [← hπ₂, integral_map measurable_snd.aemeasurable htmeas.aestronglyMeasurable]
  have e2 : ∫ x, φ x ∂μ = ∫ z, φ z.1 ∂π := by
    rw [← hπ₁, integral_map measurable_fst.aemeasurable hφmeas.aestronglyMeasurable]
  rw [e1, e2, ← integral_add htI hφI]
  exact integral_mono hcI (htI.add hφI) fun z => hpt z.1 z.2

#print axioms solution
