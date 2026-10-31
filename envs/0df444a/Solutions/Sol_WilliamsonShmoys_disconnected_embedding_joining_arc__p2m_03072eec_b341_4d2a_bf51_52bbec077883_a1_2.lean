-- Prove2me | solution 2 for WilliamsonShmoys.disconnected_embedding_joining_arc__p2m_03072eec_b341_4d2a_bf51_52bbec077883_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:33:25.829398+00:00
-- url     : https://prove2.me/submissions/145e3495-96e3-4f3a-97ae-85075fa9c3d4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (K : SimpleGraph V) [DecidableRel K.Adj]
        (p : V → ℝ × ℝ)
        (arc : V → V → ℝ → ℝ × ℝ)
        (hp : Function.Injective p)
        (hdrawing : ∀ u v, u < v → K.Adj u v →
          ContinuousOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
          Set.InjOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
          arc u v 0 = p u ∧ arc u v 1 = p v ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
        (hcross : ∀ u v x y, u < v → x < y → K.Adj u v → K.Adj x y →
          (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
        (hdis : ¬ K.Connected),
        ∃ (u v : V) (gamma : ℝ → ℝ × ℝ),
          u < v ∧ ¬ K.Adj u v ∧
          ContinuousOn gamma (Set.Icc (0 : ℝ) 1) ∧
          Set.InjOn gamma (Set.Icc (0 : ℝ) 1) ∧
          gamma 0 = p u ∧ gamma 1 = p v ∧
          (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
          (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → K.Adj x y →
            ∀ s ∈ Set.Icc (0 : ℝ) 1, gamma t ≠ arc x y s)) := by
  intro hall
  letI : Fintype Empty := inferInstance
  letI : LinearOrder Empty := inferInstance
  let K : SimpleGraph Empty := ⊤
  letI : DecidableRel K.Adj := inferInstance
  let p : Empty → ℝ × ℝ := fun x => nomatch x
  let arc : Empty → Empty → ℝ → ℝ × ℝ := fun x => nomatch x
  have hp : Function.Injective p := by
    intro x
    cases x
  have hdrawing : ∀ u v, u < v → K.Adj u v →
      ContinuousOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w := by
    intro u
    cases u
  have hcross : ∀ u v x y, u < v → x < y → K.Adj u v → K.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
        (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) := by
    intro u
    cases u
  have hdis : ¬ K.Connected := by
    intro hc
    rcases hc.nonempty with ⟨x⟩
    cases x
  have hbad := hall (V := Empty) K p arc hp hdrawing hcross hdis
  rcases hbad with ⟨u, v, gamma, huv, hne, hcont, hinj, hzero, hone, hvertices, hedges⟩
  cases u