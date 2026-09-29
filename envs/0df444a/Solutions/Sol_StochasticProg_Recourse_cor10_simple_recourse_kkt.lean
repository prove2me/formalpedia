-- Prove2me | solution 1 for StochasticProg.Recourse.cor10_simple_recourse_kkt
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-27T23:21:13.895479+00:00
-- url     : https://prove2.me/submissions/cf84d595-8022-4be9-98fd-3a010295144f

import Mathlib
import Definitions.Def_StochasticProg_Recourse_SimpleRecourse

open StochasticProg.Recourse

/-- Counterexample: `Q`, `F⁻`, `F⁺` are left completely abstract, constrained only by
`hsubdiff`. Take `n1 = m1 = m2 = 1`, `A = [1]`, `b = 0`, `c = 0`, `T = [1]`, `q⁺ = 0`,
`q⁻ = 1`, `F⁻ ≡ 1`, `F⁺ ≡ 0` and `Q(x) = -|x₀|`. Then `Q` has no subgradient anywhere and the
interval `[1, 0]` is empty, so `hsubdiff` holds (both sides are empty). `K1 = {0}`, so
`x* = 0` is optimal with value `0`, but no `π` satisfies `1 ≤ π ≤ 0`. -/
theorem solution : ¬ (∀ {n1 m1 m2 : ℕ} (inst : SimpleRecourseInstance n1 m1 m2)
    (Fminus Fplus : Fin m2 → ℝ → ℝ) (Q : (Fin n1 → ℝ) → EReal) (hQ : ∀ x, Q x ≠ ⊥)
    (hsubdiff : ∀ x : Fin n1 → ℝ,
      {η : Fin n1 → ℝ | ∀ y : Fin n1 → ℝ,
          Q x + ((dotProduct η (y - x) : ℝ) : EReal) ≤ Q y} =
        {η | ∃ pi : Fin m2 → ℝ,
          (∀ i, -(inst.qplus i) + inst.qsum i * Fminus i (Matrix.mulVec inst.T x i) ≤ pi i ∧
                pi i ≤ -(inst.qplus i) + inst.qsum i * Fplus i (Matrix.mulVec inst.T x i)) ∧
          η = fun j => ∑ i, pi i * inst.T i j})
    (hfin : ∃ z0 : ℝ,
      sInf ((fun x => ((dotProduct inst.c x : ℝ) : EReal) + Q x) '' inst.K1) = (z0 : EReal))
    (xstar : Fin n1 → ℝ) (hx : xstar ∈ inst.K1),
    (((dotProduct inst.c xstar : ℝ) : EReal) + Q xstar =
        sInf ((fun x => ((dotProduct inst.c x : ℝ) : EReal) + Q x) '' inst.K1)) ↔
      ∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ) (pi : Fin m2 → ℝ),
        (∀ j, 0 ≤ mu j) ∧ dotProduct mu xstar = 0 ∧
        (∀ i, -(inst.qplus i) + inst.qsum i * Fminus i (Matrix.mulVec inst.T xstar i) ≤ pi i ∧
              pi i ≤ -(inst.qplus i) + inst.qsum i * Fplus i (Matrix.mulVec inst.T xstar i)) ∧
        (fun j => -inst.c j + Matrix.mulVec (Matrix.transpose inst.A) lam j + mu j -
            ∑ i, pi i * inst.T i j) = 0) := by
  intro H
  let inst : SimpleRecourseInstance 1 1 1 :=
    { A := !![1], b := 0, c := 0, T := !![1], qplus := 0, qminus := 1 }
  let Q : (Fin 1 → ℝ) → EReal := fun x => ((-|x 0| : ℝ) : EReal)
  have hK : inst.K1 = {0} := by
    ext x
    simp only [SimpleRecourseInstance.K1, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, -⟩
      funext i
      fin_cases i
      have := congrFun h1 0
      simpa [inst, Matrix.mulVec, dotProduct] using this
    · rintro rfl
      exact ⟨by simp [inst], fun _ => le_rfl⟩
  have hsub : ∀ x : Fin 1 → ℝ,
      {η : Fin 1 → ℝ | ∀ y : Fin 1 → ℝ,
          Q x + ((dotProduct η (y - x) : ℝ) : EReal) ≤ Q y} =
        {η | ∃ pi : Fin 1 → ℝ,
          (∀ i, -(inst.qplus i) + inst.qsum i * (fun _ _ => (1 : ℝ)) i
              (Matrix.mulVec inst.T x i) ≤ pi i ∧
                pi i ≤ -(inst.qplus i) + inst.qsum i * (fun _ _ => (0 : ℝ)) i
              (Matrix.mulVec inst.T x i)) ∧
          η = fun j => ∑ i, pi i * inst.T i j} := by
    intro x
    ext η
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hη
      exfalso
      set a := x 0
      set t := |a| + 1
      have h1 := hη (x + fun _ => t)
      have h2 := hη (x - fun _ => t)
      simp only [Q] at h1 h2
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h1 h2
      simp [dotProduct] at h1 h2
      have e1 := le_abs_self (x 0 + t)
      have e2 := neg_abs_le (x 0 - t)
      have e3 := le_abs_self (x 0)
      have e4 := neg_abs_le (x 0)
      nlinarith [abs_nonneg (x 0)]
    · rintro ⟨pi, hpi, -⟩
      exfalso
      have := hpi 0
      simp [inst, SimpleRecourseInstance.qsum] at this
      linarith [this.1, this.2]
  have key := (H inst (fun _ _ => 1) (fun _ _ => 0) Q (fun x => EReal.coe_ne_bot _) hsub
    ⟨0, by rw [hK]; simp [Q, inst]⟩ 0 (by rw [hK]; rfl)).1 (by rw [hK]; simp [Q, inst])
  obtain ⟨_, _, pi, _, _, hpi, _⟩ := key
  have := hpi 0
  simp [inst, SimpleRecourseInstance.qsum] at this
  linarith [this.1, this.2]
