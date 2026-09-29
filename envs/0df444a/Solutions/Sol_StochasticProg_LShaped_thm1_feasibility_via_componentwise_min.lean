-- Prove2me | solution 1 for StochasticProg.LShaped.thm1_feasibility_via_componentwise_min
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T03:06:02.723865+00:00
-- url     : https://prove2.me/submissions/32cb683b-f1a2-482e-9dc1-2c4354bfe4c5

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases

/-! Disproof of 89f5f041 `StochasticProg.LShaped.thm1_feasibility_via_componentwise_min`.

`K2 inst = {x | Q inst x ≠ ⊤}` with `Q inst x = foldr bookAdd 0 [p k * QVal inst x k]`, and the
`Instance` structure only asks `0 ≤ p k`. In `EReal`, `0 * ⊤ = 0`, so a scenario of probability
zero that is second-stage infeasible (`QVal = ⊤`) does not make `Q` infinite. Put the
componentwise minimum `a = h ℓ` in such a scenario: `x ∈ K2`, yet `W y = a - T0 x, y ≥ 0` has no
solution.

Concrete instance: `n1 = n2 = m2 = 1`, `m1 = 0`, `K = 2`, `W = 1`, `q = 0`, `T ≡ 0`,
`h 0 = -1`, `h 1 = 0`, `p = (0, 1)`, `ℓ = 0`, `a = -1`, `x = 0`. -/

set_option autoImplicit false

open StochasticProg.Recourse StochasticProg.LShaped

noncomputable def dp89Inst : Instance 1 1 0 1 2 where
  A := 0
  b := 0
  c := 0
  W := 1
  q := fun _ => 0
  h := ![fun _ => -1, fun _ => 0]
  T := fun _ => 0
  p := ![0, 1]
  hp_nonneg := by
    intro k
    fin_cases k <;> simp
  hp_sum := by simp [Fin.sum_univ_two]

theorem dp89_QVal_one_ne_top : QVal dp89Inst 0 1 ≠ ⊤ := by
  have hle : QVal dp89Inst 0 1 ≤ 0 := by
    unfold QVal
    apply sInf_le
    refine ⟨0, fun _ => le_refl 0, ?_, ?_⟩
    · funext i
      simp [dp89Inst]
    · simp [dp89Inst]
  intro htop
  rw [htop] at hle
  exact absurd hle (by simp)

theorem dp89_mem_K2 : (0 : Fin 1 → ℝ) ∈ K2 dp89Inst := by
  have hQ : Q dp89Inst 0 = QVal dp89Inst 0 1 := by
    have h1 : ((dp89Inst.p 1 : ℝ) : EReal) = 1 := by simp [dp89Inst]
    have h0 : ((dp89Inst.p 0 : ℝ) : EReal) = 0 := by simp [dp89Inst]
    simp only [Q, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil]
    rw [show (Fin.succ (0 : Fin 1) : Fin 2) = 1 from rfl, h1, h0, zero_mul, one_mul]
    unfold bookAdd
    simp [dp89_QVal_one_ne_top]
  show Q dp89Inst 0 ≠ ⊤
  rw [hQ]
  exact dp89_QVal_one_ne_top

theorem solution : ¬ (∀ {n1 n2 m1 m2 K : ℕ}
    (inst : Instance n1 n2 m1 m2 K) (hK : 0 < K)
    (T0 : Matrix (Fin m2) (Fin n1) ℝ) (hT : ∀ k, inst.T k = T0)
    (hWpos : ∀ t : Fin m2 → ℝ, (∀ i, 0 ≤ t i) → posW inst t)
    (a : Fin m2 → ℝ) (ha : ∀ i, a i = sInf {v : ℝ | ∃ k : Fin K, v = inst.h k i})
    (ℓ : Fin K) (haℓ : a = inst.h ℓ) (x : Fin n1 → ℝ),
    x ∈ K2 inst ↔
      ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧ Matrix.mulVec inst.W y = a - Matrix.mulVec T0 x) := by
  intro H
  have hWpos : ∀ t : Fin 1 → ℝ, (∀ i, 0 ≤ t i) → posW dp89Inst t := by
    intro t ht
    refine ⟨t, ht, ?_⟩
    simp [dp89Inst]
  have ha : ∀ i : Fin 1, (fun _ => (-1 : ℝ)) i =
      sInf {v : ℝ | ∃ k : Fin 2, v = dp89Inst.h k i} := by
    intro i
    symm
    apply IsLeast.csInf_eq
    refine ⟨⟨0, by simp [dp89Inst]⟩, ?_⟩
    rintro v ⟨k, rfl⟩
    fin_cases k <;> simp [dp89Inst]
  have haℓ : (fun _ => (-1 : ℝ)) = dp89Inst.h 0 := by
    funext i
    simp [dp89Inst]
  have key := (H dp89Inst (by norm_num) 0 (fun _ => rfl) hWpos (fun _ => -1) ha 0 haℓ 0).1
    dp89_mem_K2
  obtain ⟨y, hy, hWy⟩ := key
  have h0 := congrFun hWy 0
  simp [dp89Inst] at h0
  linarith [hy 0]
