-- Prove2me | solution 1 for WilliamsonShmoys.clean_arc_drawing_geometry__p2m_a073dd38_4e30_4f95_9bdc_3dc54f59a882_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:00:00.185709+00:00
-- url     : https://prove2.me/submissions/eae3e6ca-036e-4783-9ccf-0eb22c810540

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hdrawing : ∀ x y, x < y → K.Adj x y →
      ContinuousOn (arc x y) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (arc x y) (Set.Icc (0 : ℝ) 1) ∧
      arc x y 0 = p x ∧ arc x y 1 = p y ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w)
    (hcross : ∀ x y a b, x < y → a < b → K.Adj x y → K.Adj a b →
      (x, y) ≠ (a, b) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, arc x y t = arc a b s →
        (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) (gamma : ℝ → ℝ × ℝ)
    (huv : u < v)
    (hcont : ContinuousOn gamma (Set.Icc (0 : ℝ) 1))
    (hinj : Set.InjOn gamma (Set.Icc (0 : ℝ) 1))
    (hzero : gamma 0 = p u) (hone : gamma 1 = p v)
    (hvertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (harcs : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → K.Adj x y →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, gamma t ≠ arc x y s)
    (L : SimpleGraph V)
    (hL : ∀ a b, L.Adj a b ↔
      K.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) :
    ∃ (q : V → ℝ × ℝ) (β : V → V → ℝ → ℝ × ℝ),
      Function.Injective q ∧
      (∀ x y, x < y → L.Adj x y →
        ContinuousOn (β x y) (Set.Icc (0 : ℝ) 1) ∧
        Set.InjOn (β x y) (Set.Icc (0 : ℝ) 1) ∧
        β x y 0 = q x ∧ β x y 1 = q y ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, β x y t ≠ q w) ∧
      (∀ x y a b, x < y → a < b → L.Adj x y → L.Adj a b →
        (x, y) ≠ (a, b) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, β x y t = β a b s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by
  classical
  let β : V → V → ℝ → ℝ × ℝ :=
    fun x y t => if x = u ∧ y = v then gamma t else arc x y t
  have oldAdj : ∀ a b, a < b → ¬ (a = u ∧ b = v) →
      L.Adj a b → K.Adj a b := by
    intro a b hab hnot hLab
    rcases (hL a b).mp hLab with hk | hnew
    · exact hk
    · rcases hnew with hnew | hnew
      · exact False.elim (hnot hnew)
      · rcases hnew with ⟨hau, hbv⟩
        have hba : b < a := by simpa [hau, hbv] using huv
        exact False.elim ((not_lt_of_ge (le_of_lt hab)) hba)
  have endpoint : ∀ z, z ∈ Set.Icc (0 : ℝ) 1 →
      ¬ z ∈ Set.Ioo (0 : ℝ) 1 → z = 0 ∨ z = 1 := by
    intro z hz hn
    by_cases h0 : z = 0
    · exact Or.inl h0
    · by_cases h1 : z = 1
      · exact Or.inr h1
      · have hzopen : z ∈ Set.Ioo (0 : ℝ) 1 := by
          constructor
          · rcases lt_or_eq_of_le hz.1 with hzpos | hz0
            · exact hzpos
            · exact False.elim (h0 hz0.symm)
          · rcases lt_or_eq_of_le hz.2 with hzlt | hz1
            · exact hzlt
            · exact False.elim (h1 hz1)
        exact False.elim (hn hzopen)
  refine ⟨p, β, hp, ?_, ?_⟩
  · intro x y hxy hLxy
    by_cases hspecial : x = u ∧ y = v
    · have hgp : gamma 0 = p x ∧ gamma 1 = p y := by
        simp [hspecial.1, hspecial.2, hzero, hone]
      simpa [β, hspecial] using
        (show ContinuousOn gamma (Set.Icc (0 : ℝ) 1) ∧
          Set.InjOn gamma (Set.Icc (0 : ℝ) 1) ∧
          gamma 0 = p x ∧ gamma 1 = p y ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w from
          ⟨hcont, hinj, hgp.1, hgp.2, hvertices⟩)
    · have hK : K.Adj x y := oldAdj x y hxy hspecial hLxy
      simpa [β, hspecial] using hdrawing x y hxy hK
  · intro x y a b hxy hab hLxy hLab hneq t ht s hs heq
    by_cases hspecxy : x = u ∧ y = v
    · by_cases hspecab : a = u ∧ b = v
      · have hpairs : (x, y) = (a, b) := by
          simp [hspecxy.1, hspecxy.2, hspecab.1, hspecab.2]
        exact False.elim (hneq hpairs)
      · have hKab : K.Adj a b := oldAdj a b hab hspecab hLab
        have hgammaArc : gamma t = arc a b s := by
          simpa [β, hspecxy, hspecab] using heq
        have htnot : ¬ t ∈ Set.Ioo (0 : ℝ) 1 := by
          intro htopen
          exact (harcs t htopen a b hab hKab s hs) hgammaArc
        have htends := endpoint t ht htnot
        have hsnot : ¬ s ∈ Set.Ioo (0 : ℝ) 1 := by
          intro hsopen
          rcases htends with htzero | htone
          · have havoid := (hdrawing a b hab hKab).2.2.2.2 s hsopen u
            apply havoid
            rw [htzero, hzero] at hgammaArc
            exact hgammaArc.symm
          · have havoid := (hdrawing a b hab hKab).2.2.2.2 s hsopen v
            apply havoid
            rw [htone, hone] at hgammaArc
            exact hgammaArc.symm
        exact ⟨htends, endpoint s hs hsnot⟩
    · by_cases hspecab : a = u ∧ b = v
      · have hKxy : K.Adj x y := oldAdj x y hxy hspecxy hLxy
        have hArcGamma : arc x y t = gamma s := by
          simpa [β, hspecxy, hspecab] using heq
        have hsnot : ¬ s ∈ Set.Ioo (0 : ℝ) 1 := by
          intro hsopen
          exact (harcs s hsopen x y hxy hKxy t ht) hArcGamma.symm
        have hstends := endpoint s hs hsnot
        have htnot : ¬ t ∈ Set.Ioo (0 : ℝ) 1 := by
          intro htopen
          rcases hstends with hszero | hsone
          · have havoid := (hdrawing x y hxy hKxy).2.2.2.2 t htopen u
            apply havoid
            rw [hszero, hzero] at hArcGamma
            exact hArcGamma
          · have havoid := (hdrawing x y hxy hKxy).2.2.2.2 t htopen v
            apply havoid
            rw [hsone, hone] at hArcGamma
            exact hArcGamma
        exact ⟨endpoint t ht htnot, hstends⟩
      · have hKxy : K.Adj x y := oldAdj x y hxy hspecxy hLxy
        have hKab : K.Adj a b := oldAdj a b hab hspecab hLab
        have hArcEq : arc x y t = arc a b s := by
          simpa [β, hspecxy, hspecab] using heq
        exact hcross x y a b hxy hab hKxy hKab hneq t ht s hs hArcEq
