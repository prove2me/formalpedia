-- Prove2me | solution 1 for SpatialPricing.ABC.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T18:59:11.177359+00:00
-- url     : https://prove2.me/submissions/357887b1-40d7-4d3f-a051-b71d3c49e46e

import Mathlib
import Definitions.Def_SpatialPricing_ABC_Setting

open SpatialPricing.ABC

/-- Uniform bound `0 ≤ r ≤ Ψ3` on `[0,1]` from `r 0 = 0` and `|r'| ≤ Ψ3`. -/
lemma spabc_r_le (f : ℝ → ℝ) (Ψ3 : ℝ) (hd : ContDiff ℝ 2 f)
    (hb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv f x| ≤ Ψ3) (h0 : f 0 = 0)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : f x ≤ Ψ3 := by
  have hdiff : Differentiable ℝ f := hd.differentiable (by norm_num)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := f) (C := Ψ3)
    (s := Set.Icc (0 : ℝ) 1) (fun y _ => hdiff y) (fun y hy => by
      rw [Real.norm_eq_abs]; exact hb y hy) (convex_Icc 0 1)
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp) hx
  rw [h0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero,
    abs_of_nonneg hx.1] at h
  have := le_abs_self (f x)
  nlinarith [hx.2, hx.1, abs_nonneg (f x), (abs_nonneg (deriv f 0)).trans (hb 0 (by simp))]

theorem solution (P : Instance) (Ψ3 : ℝ) (hP : P.Standing Ψ3) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ Ψ0 : ℝ, 0 < Ψ0 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ζ : ℝ, 0 ≤ ζ → ζ < ζbar →
        (∃ x, (P.scale n).DCPFeasible ζ x) ∧
        (P.scale n).J 0 - (P.scale n).J ζ ≤ Ψ0 * P.TN n * ζ := by
  obtain ⟨hN, hT, hτ, hC, hΨ, hr⟩ := hP
  -- M bounds all travel times
  set M : ℕ := ∑ p : Fin P.N × Fin P.N, P.τ p.1 p.2 with hMdef
  have hτM : ∀ i j, P.τ i j ≤ M := fun i j => by
    rw [hMdef]
    exact Finset.single_le_sum (f := fun p : Fin P.N × Fin P.N => P.τ p.1 p.2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))
  have hM1 : 1 ≤ M := by
    have i0 : Fin P.N := ⟨0, by omega⟩
    exact (hτ i0 i0).trans (hτM i0 i0)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  set c : ℝ := 1 / (2 * (M : ℝ)) with hcdef
  have hc0 : 0 < c := by positivity
  have hc2 : c ≤ 1 / 2 := by
    rw [hcdef]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    linarith
  have hcM : c * (M : ℝ) = 1 / 2 := by rw [hcdef]; field_simp
  have hNpos : (0 : ℝ) < P.N := by exact_mod_cast (show 0 < P.N by omega)
  refine ⟨c, hc0, (P.N : ℝ) ^ 2 * Ψ3 / c, by positivity, ?_⟩
  intro n hn ζ hζ0 hζc
  set Q := P.scale n with hQ
  have hQN : Q.N = P.N := rfl
  have hQT : Q.T = n * P.T := rfl
  -- index of the scaled revenue lies in the original horizon
  have hidx : ∀ t ∈ Finset.Icc 1 Q.T, (t + n - 1) / n ∈ Finset.Icc 1 P.T := by
    intro t ht
    rw [Finset.mem_Icc] at ht ⊢
    rw [hQT] at ht
    constructor
    · rw [Nat.le_div_iff_mul_le (by omega)]; omega
    · rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
      have : t ≤ n * P.T := ht.2
      have hc := Nat.mul_comm n P.T
      omega
  have hrQ : ∀ t ∈ Finset.Icc 1 Q.T, ∀ i j,
      ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (Q.r t i j) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Q.r t i j x ∧ Q.r t i j x ≤ Ψ3) := by
    intro t ht i j
    obtain ⟨⟨m, hm, hsc⟩, hcd, hb, h0⟩ := hr _ (hidx t ht) i j
    refine ⟨(hsc.strictConcaveOn hm).concaveOn, fun x hx => ⟨(hb x hx).2.2, ?_⟩⟩
    exact spabc_r_le _ Ψ3 hcd (fun y hy => (hb y hy).1) h0 x hx
  -- the constant schedule c
  let y : ℕ → Fin Q.N → Fin Q.N → ℝ := fun _ _ _ => c
  have hyflow : ∀ t ∈ Finset.Icc 1 Q.T, ∀ i,
      0 ≤ (Q.C i : ℝ) - ∑ j, ∑ s ∈ Finset.Icc 1 t, y s i j +
        ∑ j, ∑ s ∈ Finset.Icc 1 (t - Q.τ j i), y s j i := by
    intro t _ i
    simp only [y, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Finset.card_univ,
      Fintype.card_fin]
    have key : ∀ j : Fin Q.N, ((t + 1 - 1 : ℕ) : ℝ) * c ≤
        ((t - Q.τ j i + 1 - 1 : ℕ) : ℝ) * c + (n : ℝ) * M * c := by
      intro j
      have h1 : t + 1 - 1 ≤ (t - Q.τ j i + 1 - 1) + n * M := by
        have : Q.τ j i = n * P.τ j i := rfl
        have h2 : n * P.τ j i ≤ n * M := Nat.mul_le_mul_left n (hτM j i)
        omega
      have : ((t + 1 - 1 : ℕ) : ℝ) ≤ ((t - Q.τ j i + 1 - 1 : ℕ) : ℝ) + (n : ℝ) * M := by
        exact_mod_cast h1
      nlinarith
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => key j)
    rw [Finset.sum_add_distrib] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hCi : (n : ℝ) * P.N ≤ (Q.C i : ℝ) := by
      have : Q.C i = n * P.C i := rfl
      rw [this]; push_cast
      have : (P.N : ℝ) ≤ P.C i := by exact_mod_cast hC i
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith
    have hQN' : (Q.N : ℝ) = P.N := rfl
    simp only [hQN'] at hsum ⊢
    have : (P.N : ℝ) * ((n : ℝ) * M * c) = (n : ℝ) * P.N / 2 := by
      rw [show (P.N : ℝ) * ((n : ℝ) * M * c) = (n : ℝ) * P.N * (c * M) by ring, hcM]; ring
    nlinarith
  have hyfeas : ∀ ζ' : ℝ, ζ' ≤ c → Q.DCPFeasible ζ' y := by
    intro ζ' hζ'
    refine ⟨hyflow, fun t _ i j => ⟨hζ', ?_⟩⟩
    show c ≤ 1 - ζ'
    linarith
  refine ⟨⟨y, hyfeas ζ hζc.le⟩, ?_⟩
  -- bound on objective for feasible schedules with nonnegative cushion
  have hobj_le : ∀ ζ' : ℝ, 0 ≤ ζ' → ∀ x, Q.DCPFeasible ζ' x →
      Q.DCPObj x ≤ (Q.T : ℝ) * (P.N * (P.N * Ψ3)) := by
    intro ζ' hζ' x hx
    unfold Instance.DCPObj
    have : ∀ t ∈ Finset.Icc 1 Q.T, ∑ i, ∑ j, Q.r t i j (x t i j) ≤ P.N * (P.N * Ψ3) := by
      intro t ht
      have h2 : ∀ i, ∑ j, Q.r t i j (x t i j) ≤ P.N * Ψ3 := by
        intro i
        calc ∑ j, Q.r t i j (x t i j) ≤ ∑ _j : Fin Q.N, Ψ3 := by
              apply Finset.sum_le_sum; intro j _
              obtain ⟨a, b⟩ := hx.2 t ht i j
              exact ((hrQ t ht i j).2 _ ⟨by linarith, by linarith⟩).2
          _ = P.N * Ψ3 := by simp [hQN]
      calc ∑ i, ∑ j, Q.r t i j (x t i j) ≤ ∑ _i : Fin Q.N, (P.N * Ψ3 : ℝ) :=
            Finset.sum_le_sum (fun i _ => h2 i)
        _ = P.N * (P.N * Ψ3) := by simp [hQN]
    calc _ ≤ ∑ _t ∈ Finset.Icc 1 Q.T, (P.N * (P.N * Ψ3) : ℝ) := Finset.sum_le_sum this
      _ = _ := by simp
  have hbdd : BddAbove (Q.DCPObj '' {x | Q.DCPFeasible ζ x}) := by
    refine ⟨(Q.T : ℝ) * (P.N * (P.N * Ψ3)), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hobj_le ζ hζ0 x hx
  set θ : ℝ := ζ / c with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one hc0]; exact hζc
  have hθc : θ * c = ζ := by rw [hθ]; field_simp
  -- main inequality
  have hmain : ∀ x, Q.DCPFeasible 0 x →
      Q.DCPObj x ≤ Q.J ζ + θ * ((Q.T : ℝ) * (P.N * (P.N * Ψ3))) := by
    intro x hx
    let x' : ℕ → Fin Q.N → Fin Q.N → ℝ := fun t i j => (1 - θ) * x t i j + θ * y t i j
    have hx'feas : Q.DCPFeasible ζ x' := by
      refine ⟨?_, ?_⟩
      · intro t ht i
        have hA := hx.1 t ht i
        have hB := hyflow t ht i
        have : (Q.C i : ℝ) - ∑ j, ∑ s ∈ Finset.Icc 1 t, x' s i j +
            ∑ j, ∑ s ∈ Finset.Icc 1 (t - Q.τ j i), x' s j i =
            (1 - θ) * ((Q.C i : ℝ) - ∑ j, ∑ s ∈ Finset.Icc 1 t, x s i j +
              ∑ j, ∑ s ∈ Finset.Icc 1 (t - Q.τ j i), x s j i) +
            θ * ((Q.C i : ℝ) - ∑ j, ∑ s ∈ Finset.Icc 1 t, y s i j +
              ∑ j, ∑ s ∈ Finset.Icc 1 (t - Q.τ j i), y s j i) := by
          simp only [x', Finset.sum_add_distrib, ← Finset.mul_sum]
          ring
        rw [this]
        have h1θ : 0 ≤ 1 - θ := by linarith
        positivity
      · intro t ht i j
        obtain ⟨a, b⟩ := hx.2 t ht i j
        simp only [x', y]
        constructor
        · nlinarith
        · nlinarith
    have hle : Q.DCPObj x' ≤ Q.J ζ := le_csSup hbdd ⟨x', hx'feas, rfl⟩
    have hterm : ∀ t ∈ Finset.Icc 1 Q.T, ∀ i j,
        Q.r t i j (x t i j) - θ * Ψ3 ≤ Q.r t i j (x' t i j) := by
      intro t ht i j
      obtain ⟨a, b⟩ := hx.2 t ht i j
      have hxI : x t i j ∈ Set.Icc (0 : ℝ) 1 := ⟨a, by linarith⟩
      have hyI : y t i j ∈ Set.Icc (0 : ℝ) 1 := ⟨hc0.le, by simp only [y]; linarith⟩
      have hcc := (hrQ t ht i j).1.2 hxI hyI (by linarith : (0 : ℝ) ≤ 1 - θ) hθ0
        (by ring)
      simp only [smul_eq_mul] at hcc
      have := (hrQ t ht i j).2 _ hxI
      have := (hrQ t ht i j).2 _ hyI
      simp only [x']
      nlinarith
    have hsum : Q.DCPObj x - θ * ((Q.T : ℝ) * (P.N * (P.N * Ψ3))) ≤ Q.DCPObj x' := by
      unfold Instance.DCPObj
      have : θ * ((Q.T : ℝ) * (P.N * (P.N * Ψ3))) =
          ∑ _t ∈ Finset.Icc 1 Q.T, ∑ _i : Fin Q.N, ∑ _j : Fin Q.N, θ * Ψ3 := by
        simp [hQN]; ring
      rw [this, ← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum; intro t ht
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum; intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum; intro j _
      exact hterm t ht i j
    linarith
  have hne : (Q.DCPObj '' {x | Q.DCPFeasible 0 x}).Nonempty :=
    ⟨_, y, hyfeas 0 hc0.le, rfl⟩
  have hJ0 : Q.J 0 ≤ Q.J ζ + θ * ((Q.T : ℝ) * (P.N * (P.N * Ψ3))) := by
    apply csSup_le hne
    rintro _ ⟨x, hx, rfl⟩
    exact hmain x hx
  have hTN : P.TN n = (Q.T : ℝ) := by
    simp [Instance.TN, hQT]
  rw [hTN]
  have : (P.N : ℝ) ^ 2 * Ψ3 / c * (Q.T : ℝ) * ζ = θ * ((Q.T : ℝ) * (P.N * (P.N * Ψ3))) := by
    rw [← hθc]; field_simp
  linarith
