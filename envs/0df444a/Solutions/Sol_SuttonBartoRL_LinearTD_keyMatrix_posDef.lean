-- Prove2me | solution 1 for SuttonBartoRL.LinearTD.keyMatrix_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:43:30.532988+00:00
-- url     : https://prove2.me/submissions/bb031526-b325-4c39-9e1d-5a514218d997

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP
import Definitions.Def_SuttonBartoRL_LinearTD_LinearTD

open Matrix

set_option autoImplicit false

open SuttonBartoRL.LinearTD in
theorem KMPD_posDef_of_sums {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (hdiag : ∀ i, 0 < M i i) (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (hrow : ∀ i, 0 < ∑ j, M i j) (hcol : ∀ j, 0 ≤ ∑ i, M i j) :
    IsPosDefNonsym M := by
  intro y hy
  have key : ∀ i j, M i j * y i ^ 2 / 2 + M i j * y j ^ 2 / 2 ≤ y i * (M i j * y j) := by
    intro i j
    by_cases h : i = j
    · subst h; nlinarith
    · have := mul_nonpos_of_nonpos_of_nonneg (hoff i j h) (sq_nonneg (y i - y j))
      nlinarith [this]
  have hsum : y ⬝ᵥ (M *ᵥ y) = ∑ i, ∑ j, y i * (M i j * y j) := by
    simp [dotProduct, mulVec, Finset.mul_sum]
  have hlow : ∑ i, ∑ j, (M i j * y i ^ 2 / 2 + M i j * y j ^ 2 / 2)
      ≤ ∑ i, ∑ j, y i * (M i j * y j) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
  have hsplit : ∑ i, ∑ j, (M i j * y i ^ 2 / 2 + M i j * y j ^ 2 / 2)
      = (∑ i, y i ^ 2 * ∑ j, M i j) / 2 + (∑ j, y j ^ 2 * ∑ i, M i j) / 2 := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => M i j * y j ^ 2 / 2)]
    simp only [Finset.sum_div, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  obtain ⟨k, hk⟩ : ∃ k, y k ≠ 0 := by
    by_contra h; push_neg at h; exact hy (funext h)
  have hpos : 0 < ∑ i, y i ^ 2 * ∑ j, M i j := by
    apply Finset.sum_pos' (fun i _ => mul_nonneg (sq_nonneg _) (hrow i).le)
    exact ⟨k, Finset.mem_univ _, mul_pos (by positivity) (hrow k)⟩
  have hnn : 0 ≤ ∑ j, y j ^ 2 * ∑ i, M i j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hcol j)
  rw [hsum]
  linarith

theorem KMPD_quad_sum0 {n ι : Type} [Fintype n] (z : n → ℝ) (s : Finset ι)
    (N : ι → Matrix n n ℝ) :
    z ⬝ᵥ ((∑ i ∈ s, N i) *ᵥ z) = ∑ i ∈ s, z ⬝ᵥ (N i *ᵥ z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, dotProduct_add, ih]

theorem KMPD_quad_smul {n : Type} [Fintype n] (z : n → ℝ) (c : ℝ) (N : Matrix n n ℝ) :
    z ⬝ᵥ ((c • N) *ᵥ z) = c * (z ⬝ᵥ (N *ᵥ z)) := by
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem KMPD_quad_vecMulVec {n : Type} [Fintype n] (z u v : n → ℝ) :
    z ⬝ᵥ (vecMulVec u v *ᵥ z) = (z ⬝ᵥ u) * (v ⬝ᵥ z) := by
  simp only [dotProduct, mulVec, vecMulVec_apply, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem KMPD_quad_td {S : Type} [Fintype S] {d : ℕ} (X : Matrix S (Fin d) ℝ) (z : Fin d → ℝ)
    (γ : ℝ) (s s' : S) :
    z ⬝ᵥ (vecMulVec (X s) (X s - γ • X s') *ᵥ z)
      = (X *ᵥ z) s * ((X *ᵥ z) s - γ * (X *ᵥ z) s') := by
  rw [KMPD_quad_vecMulVec, dotProduct_comm z]
  congr 1
  simp only [mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

open Matrix SuttonBartoRL.LinearTD in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) (X : Matrix S (Fin d) ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hμ : IsStationaryDist (M.policyTrans π) μ) (hμpos : ∀ s, 0 < μ s)
    (hX : LinearIndependent ℝ Xᵀ) :
    IsPosDefNonsym (keyMatrix μ (M.policyTrans π) γ) ∧ IsPosDefNonsym (tdA M π μ X γ) := by
  set P := M.policyTrans π with hPdef
  have hPnn : ∀ s s', 0 ≤ P s s' := fun s s' =>
    Finset.sum_nonneg fun a _ => mul_nonneg (π.nonneg s a)
      (Finset.sum_nonneg fun r _ => M.p_nonneg s a s' r)
  have hProw : ∀ s, ∑ s', P s s' = 1 := by
    intro s
    simp only [hPdef, MDP.policyTrans, MDP.trans]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, M.p_sum, mul_one, π.sum_one]
  have hK : ∀ i j, keyMatrix μ P γ i j = μ i * ((if i = j then (1:ℝ) else 0) - γ * P i j) := by
    intro i j
    simp [keyMatrix, diagonal_mul, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  have hcolv : vecMul (fun _ => (1 : ℝ)) (keyMatrix μ P γ) = (1 - γ) • μ := by
    have h1 : vecMul (fun _ => (1 : ℝ)) (diagonal μ) = μ := by
      funext x; rw [vecMul_diagonal]; simp
    unfold keyMatrix
    rw [← vecMul_vecMul, h1, vecMul_sub, vecMul_one, vecMul_smul, hμ.2.2, sub_smul, one_smul]
  have hKpd : IsPosDefNonsym (keyMatrix μ P γ) := by
    apply KMPD_posDef_of_sums
    · intro i
      rw [hK, if_pos rfl]
      have hle : P i i ≤ 1 := by
        rw [← hProw i]
        exact Finset.single_le_sum (fun j _ => hPnn i j) (Finset.mem_univ i)
      have : γ * P i i < 1 := by nlinarith [hPnn i i]
      exact mul_pos (hμpos i) (by linarith)
    · intro i j hij
      rw [hK, if_neg hij]
      exact mul_nonpos_of_nonneg_of_nonpos (hμpos i).le
        (by nlinarith [hPnn i j])
    · intro i
      simp only [hK, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, hProw i]
      exact mul_pos (hμpos i) (by linarith)
    · intro j
      have := congrFun hcolv j
      simp only [vecMul, dotProduct, one_mul, Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      exact mul_nonneg (by linarith) (hμpos j).le
  refine ⟨hKpd, ?_⟩
  intro z hz
  set y := X *ᵥ z with hydef
  have hy : y ≠ 0 := by
    intro h0
    apply hz
    have := (Fintype.linearIndependent_iff.mp hX) z (by
      funext s
      have := congrFun h0 s
      simp only [hydef, mulVec, dotProduct, Pi.zero_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => by ring)
    funext i; exact this i
  have hys : ∀ s, X s ⬝ᵥ z = y s := fun s => rfl
  have heq : z ⬝ᵥ (tdA M π μ X γ *ᵥ z) = y ⬝ᵥ (keyMatrix μ P γ *ᵥ y) := by
    unfold tdA
    simp only [KMPD_quad_sum0, KMPD_quad_smul, KMPD_quad_td]
    rw [← hydef]
    simp only [dotProduct, mulVec, hK]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hT : ∀ a s', ∑ r ∈ M.R, M.p s a s' r * (y s * (y s - γ * y s'))
        = M.trans s a s' * (y s * (y s - γ * y s')) := fun a s' => by
      rw [MDP.trans, Finset.sum_mul]
    have hLHS : ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (y s * (y s - γ * y s'))
        = y s * y s - γ * y s * ∑ s', P s s' * y s' := by
      simp_rw [hT, Finset.mul_sum]
      rw [Finset.sum_comm]
      have h1 : ∀ s', ∑ a, π.prob s a * (M.trans s a s' * (y s * (y s - γ * y s')))
          = P s s' * (y s * (y s - γ * y s')) := by
        intro s'
        simp only [hPdef, MDP.policyTrans, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [Finset.sum_congr rfl fun s' _ => h1 s']
      have h2 : ∀ s', P s s' * (y s * (y s - γ * y s'))
          = y s * y s * P s s' - γ * y s * (P s s' * y s') := fun s' => by ring
      rw [Finset.sum_congr rfl fun s' _ => h2 s', Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hProw, mul_one]
    have hRHS : ∑ x, μ s * ((if s = x then (1:ℝ) else 0) - γ * P s x) * y x
        = μ s * y s - μ s * γ * ∑ x, P s x * y x := by
      have h3 : ∀ x, μ s * ((if s = x then (1:ℝ) else 0) - γ * P s x) * y x
          = (if s = x then μ s * y x else 0) - μ s * γ * (P s x * y x) := fun x => by
        split_ifs <;> ring
      rw [Finset.sum_congr rfl fun x _ => h3 x, Finset.sum_sub_distrib, Finset.sum_ite_eq,
        if_pos (Finset.mem_univ _), ← Finset.mul_sum]
    rw [hLHS, hRHS]
    ring
  rw [heq]
  exact hKpd y hy
