-- Prove2me | solution 1 for ValuativeSYZ.lemma_3_7_max_attained
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T19:53:18.173984+00:00
-- url     : https://prove2.me/submissions/5c25f280-792b-4353-ab81-4180b259428e

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

/-! 51d54626 ValuativeSYZ.lemma_3_7_max_attained: for φ = ψᶜ with ψ bounded and c continuous on
the compact X × B, both φ and φᶜ are lower semicontinuous (suprema of continuous families that
are uniformly bounded above), so x ↦ φ x - c x p and p ↦ φᶜ p - c x p attain their minima on
the compact spaces. The minimiser gives the maximiser of each supremum; for the first identity
one also uses φᶜ ≤ ψ, whence φ = ψᶜ ≤ (φᶜ)ᶜ ≤ φ. No `Theorems.*` module is imported. -/

set_option autoImplicit false

open MeasureTheory

open ValuativeSYZ in
theorem solution {X B : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace B] [CompactSpace B] [Nonempty B]
    (c : X → B → ℝ) (hc : Continuous fun z : X × B => c z.1 z.2)
    (φ : X → ℝ) (hφ : φ ∈ Pc c) :
    (∀ x : X, ∃ p : B, φ x = c x p - ctransform c φ p) ∧
      (∀ p : B, ∃ x : X, ctransform c φ p = c x p - φ x) := by
  obtain ⟨ψ, ⟨Mψ, hψ⟩, hφeq⟩ := hφ
  have hφx : ∀ x, φ x = ⨆ p, (c x p - ψ p) := fun x => by rw [hφeq]; rfl
  have hcx : ∀ x, Continuous fun p : B => c x p := fun x =>
    hc.comp (continuous_const.prodMk continuous_id : Continuous fun p : B => (x, p))
  have hcp : ∀ p, Continuous fun x : X => c x p := fun p =>
    hc.comp (continuous_id.prodMk continuous_const : Continuous fun x : X => (x, p))
  obtain ⟨U, hU⟩ := (isCompact_range hc).bddAbove
  obtain ⟨L, hL⟩ := (isCompact_range hc).bddBelow
  have hcU : ∀ x p, c x p ≤ U := fun x p => hU ⟨(x, p), rfl⟩
  have hcL : ∀ x p, L ≤ c x p := fun x p => hL ⟨(x, p), rfl⟩
  have hbddψ : ∀ x, BddAbove (Set.range fun p => c x p - ψ p) := fun x =>
    ⟨U + Mψ, by
      rintro _ ⟨p, rfl⟩
      have h1 := hcU x p
      have h2 := (abs_le.mp (hψ p)).1
      show c x p - ψ p ≤ U + Mψ
      linarith⟩
  have hφge : ∀ x p, c x p - ψ p ≤ φ x := fun x p => by
    rw [hφx x]; exact le_ciSup (hbddψ x) p
  obtain ⟨p₀⟩ := (inferInstance : Nonempty B)
  have hφL : ∀ x, L - Mψ ≤ φ x := fun x => by
    have h1 := hφge x p₀
    have h2 := hcL x p₀
    have h3 := (abs_le.mp (hψ p₀)).2
    linarith
  have hbddφ : ∀ p, BddAbove (Set.range fun x => c x p - φ x) := fun p =>
    ⟨U - (L - Mψ), by
      rintro _ ⟨x, rfl⟩
      have h1 := hcU x p
      have h2 := hφL x
      show c x p - φ x ≤ U - (L - Mψ)
      linarith⟩
  have hct : ∀ p, ctransform c φ p = ⨆ x, (c x p - φ x) := fun p => rfl
  -- lower semicontinuity of φ and of φᶜ
  have hφLSC : LowerSemicontinuous φ := by
    have h : LowerSemicontinuous fun x => ⨆ p, (c x p - ψ p) :=
      lowerSemicontinuous_ciSup (f := fun p x => c x p - ψ p) hbddψ
        (fun p => ((hcp p).sub continuous_const).lowerSemicontinuous)
    have he : φ = fun x => ⨆ p, (c x p - ψ p) := funext hφx
    rw [he]; exact h
  have hφcLSC : LowerSemicontinuous (ctransform c φ) := by
    have h : LowerSemicontinuous fun p => ⨆ x, (c x p - φ x) :=
      lowerSemicontinuous_ciSup (f := fun x p => c x p - φ x) hbddφ
        (fun x => ((hcx x).sub continuous_const).lowerSemicontinuous)
    have he : ctransform c φ = fun p => ⨆ x, (c x p - φ x) := funext hct
    rw [he]; exact h
  -- φᶜ ≤ ψ
  have hφcψ : ∀ p, ctransform c φ p ≤ ψ p := fun p => by
    rw [hct p]
    refine ciSup_le fun x => ?_
    have := hφge x p
    linarith
  constructor
  · intro x
    have hlsc : LowerSemicontinuous fun p => ctransform c φ p + (-c x p) :=
      hφcLSC.add ((hcx x).neg.lowerSemicontinuous)
    obtain ⟨q, -, hq⟩ := LowerSemicontinuousOn.exists_isMinOn Set.univ_nonempty isCompact_univ
      (hlsc.lowerSemicontinuousOn Set.univ)
    have hqmin : ∀ p, ctransform c φ q + (-c x q) ≤ ctransform c φ p + (-c x p) := fun p =>
      isMinOn_iff.mp hq p (Set.mem_univ p)
    refine ⟨q, le_antisymm ?_ ?_⟩
    · rw [hφx x]
      refine ciSup_le fun p => ?_
      have h1 := hqmin p
      have h2 := hφcψ p
      linarith
    · have h1 : c x q - φ x ≤ ctransform c φ q := by
        rw [hct q]; exact le_ciSup (hbddφ q) x
      linarith
  · intro p
    have hlsc : LowerSemicontinuous fun x => φ x + (-c x p) :=
      hφLSC.add ((hcp p).neg.lowerSemicontinuous)
    obtain ⟨y, -, hy⟩ := LowerSemicontinuousOn.exists_isMinOn Set.univ_nonempty isCompact_univ
      (hlsc.lowerSemicontinuousOn Set.univ)
    have hymin : ∀ x, φ y + (-c y p) ≤ φ x + (-c x p) := fun x =>
      isMinOn_iff.mp hy x (Set.mem_univ x)
    refine ⟨y, le_antisymm ?_ ?_⟩
    · rw [hct p]
      refine ciSup_le fun x => ?_
      have h1 := hymin x
      linarith
    · rw [hct p]; exact le_ciSup (hbddφ p) y

#print axioms solution
