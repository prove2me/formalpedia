-- Prove2me | solution 1 for WilliamsonShmoys.simpleArcAvoidingDrawingComplement__p2m_ff2db21c_4994_4086_b5ef_9d99edb0d1bf_a3
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:57:38.696616+00:00
-- url     : https://prove2.me/submissions/589ad85d-94fd-472c-a105-98cd439bd966

import Mathlib

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
      (u v : V) (gamma : ℝ → ℝ × ℝ)
      (hcont : ContinuousOn gamma (Set.Icc 0 1))
      (hzero : gamma 0 = p u) (hone : gamma 1 = p v)
      (havoidV : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
      (havoidE : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y →
        ∀ s ∈ Set.Icc 0 1, gamma t ≠ arc x y s),
      ∃ delta : ℝ → ℝ × ℝ,
        ContinuousOn delta (Set.Icc 0 1) ∧
        Set.InjOn delta (Set.Icc 0 1) ∧
        delta 0 = p u ∧ delta 1 = p v ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, delta t ≠ p w) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y →
          ∀ s ∈ Set.Icc 0 1, delta t ≠ arc x y s)) := by
  intro H
  let G : SimpleGraph (Fin 1) := ⊥
  let p : Fin 1 → ℝ × ℝ := fun _ => (0, 0)
  let arc : Fin 1 → Fin 1 → ℝ → ℝ × ℝ := fun _ _ _ => (0, 0)
  let gamma : ℝ → ℝ × ℝ := fun t => (t * (1 - t), 0)
  have hcont : ContinuousOn gamma (Set.Icc 0 1) := by
    dsimp [gamma]
    fun_prop
  have hzero : gamma 0 = p 0 := by simp [gamma, p]
  have hone : gamma 1 = p 0 := by simp [gamma, p]
  have havoidV : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w := by
    intro t ht w
    change (t * (1 - t), 0) ≠ (0, 0)
    intro h
    have hprod : t * (1 - t) = 0 := by exact congrArg Prod.fst h
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have ht1 : 1 - t ≠ 0 := sub_ne_zero.mpr (ne_of_gt ht.2)
    exact (mul_ne_zero ht0 ht1) hprod
  have havoidE : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y →
      ∀ s ∈ Set.Icc 0 1, gamma t ≠ arc x y s := by
    intro t ht x y hxy hadj s hs
    have : False := by simpa [G] using hadj
    exact this.elim
  obtain ⟨delta, hdelta_cont, hdelta_inj, hdelta_zero, hdelta_one, hdelta_v, hdelta_e⟩ :=
    H (G := G) (p := p) (arc := arc) (u := (0 : Fin 1)) (v := 0)
      (gamma := gamma) hcont hzero hone havoidV havoidE
  have hEq : delta 0 = delta 1 := by rw [hdelta_zero, hdelta_one]
  have hzero_mem : (0 : ℝ) ∈ Set.Icc 0 1 := by norm_num
  have hone_mem : (1 : ℝ) ∈ Set.Icc 0 1 := by norm_num
  have h01 : (0 : ℝ) = 1 := hdelta_inj hzero_mem hone_mem hEq
  linarith