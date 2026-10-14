-- Prove2me | solution 1 for RegLearnGames.FirstOrder.theorem_23
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:12:08.964757+00:00
-- url     : https://prove2.me/submissions/a048ba1b-9eac-472b-944a-ce1b514aca07

import Mathlib
import Definitions.Def_RegLearnGames_FirstOrder_Setting

namespace RRAux_RegLearnGames_FirstOrder_theorem_23

open Finset

variable {n d : ℕ}

noncomputable def Pr (σ : Fin n → Fin d → ℝ) (i : Fin n) (r : {j // j ≠ i} → Fin d) : ℝ :=
  ∏ j : {j // j ≠ i}, σ j.1 (r j)

lemma decomp (σ : Fin n → Fin d → ℝ) (i : Fin n) (f : (Fin n → Fin d) → ℝ) :
    ∑ s, AGT.profileProb σ s * f s =
      ∑ a, σ i a * ∑ r, Pr σ i r * f ((Equiv.funSplitAt i (Fin d)).symm (a, r)) := by
  rw [← (Equiv.funSplitAt i (Fin d)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  unfold AGT.profileProb Pr
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  have h1 : (Equiv.funSplitAt i (Fin d)).symm (a, r) i = a := by
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have h2 : ∀ j : {j // j ≠ i}, (Equiv.funSplitAt i (Fin d)).symm (a, r) j.1 = r j := by
    intro j; simp [Equiv.funSplitAt, Equiv.piSplitAt, j.2]
  simp only [h1, h2]
  ring

lemma update_symm (i : Fin n) (a b : Fin d) (r : {j // j ≠ i} → Fin d) :
    Function.update ((Equiv.funSplitAt i (Fin d)).symm (a, r)) i b =
      (Equiv.funSplitAt i (Fin d)).symm (b, r) := by
  funext j
  by_cases h : j = i
  · subst h; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [Equiv.funSplitAt, Equiv.piSplitAt, h]

lemma Pr_update (σ : Fin n → Fin d → ℝ) (i : Fin n) (v : Fin d → ℝ) (r : {j // j ≠ i} → Fin d) :
    Pr (Function.update σ i v) i r = Pr σ i r := by
  unfold Pr
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Function.update_of_ne j.2]

noncomputable def K (c : Fin n → (Fin n → Fin d) → ℝ) (σ : Fin n → Fin d → ℝ) (i : Fin n)
    (x : Fin d) : ℝ :=
  ∑ r, Pr σ i r * c i ((Equiv.funSplitAt i (Fin d)).symm (x, r))

lemma costVec_eq (c : Fin n → (Fin n → Fin d) → ℝ) (σ : Fin n → Fin d → ℝ) (i : Fin n)
    (x : Fin d) : RegLearnGames.FirstOrder.costVec c σ i x = K c σ i x := by
  unfold RegLearnGames.FirstOrder.costVec AGT.expectedPayoff
  rw [decomp _ i]
  simp only [Function.update_self, Pr_update]
  rw [Finset.sum_eq_single x]
  · simp [K]
  · intro b _ hb; simp [hb]
  · simp

lemma dot_costVec (c : Fin n → (Fin n → Fin d) → ℝ) (σ : Fin n → Fin d → ℝ) (i : Fin n) :
    σ i ⬝ᵥ RegLearnGames.FirstOrder.costVec c σ i = AGT.expectedPayoff c σ i := by
  unfold AGT.expectedPayoff
  rw [decomp _ i]
  simp only [dotProduct, costVec_eq, K]

lemma dev_eq (c : Fin n → (Fin n → Fin d) → ℝ) (σ : Fin n → Fin d → ℝ) (i : Fin n)
    (hσ : ∑ a, σ i a = 1) (b : Fin d) :
    ∑ s, AGT.profileProb σ s * c i (Function.update s i b) =
      RegLearnGames.FirstOrder.costVec c σ i b := by
  rw [decomp _ i, costVec_eq]
  simp only [update_symm]
  rw [← Finset.sum_mul, hσ, one_mul]; rfl

lemma amgm (A L l g : ℝ) (hL : 0 ≤ L) (hl : 0 ≤ l) (hg : 0 < g) :
    A * Real.sqrt (l * L) ≤ g * L + A ^ 2 * l / (4 * g) := by
  have hq := Real.sq_sqrt (mul_nonneg hl hL)
  have hq0 := Real.sqrt_nonneg (l * L)
  set q := Real.sqrt (l * L)
  rcases hl.lt_or_eq with hl | hl
  · rw [← sub_nonneg]
    have : g * L + A ^ 2 * l / (4 * g) - A * q = (2*g*q - A*l)^2 / (4*g*l) := by
      field_simp; linear_combination (-4*g^2) * hq
    rw [this]; positivity
  · subst hl; simp at hq; have : q = 0 := by nlinarith
    rw [this]; simp; positivity

lemma final (S SL T lam O mu A1 A2 n l : ℝ) (hT : 0 < T) (h0 : 0 < mu) (h1 : mu < 1)
    (ha : S - SL ≤ (1 - mu) / (2 * mu) * SL + n * (A1 ^ 2 * l / (4 * ((1 - mu) / (2 * mu))) + A2 * l))
    (hb : SL ≤ T * (lam * O) + mu * S) :
    (1 / T) * S ≤ lam * (1 + mu) / (mu * (1 - mu)) * O +
        (A1 ^ 2 * mu / (1 - mu) ^ 2 + 2 * A2 / (1 - mu)) * n * l / T := by
  have hm : 0 < 1 - mu := by linarith
  have hT' : T ≠ 0 := hT.ne'
  have hm' : 1 - mu ≠ 0 := hm.ne'
  have h0' : mu ≠ 0 := h0.ne'
  have hc : SL * ((1 + mu) / (2 * mu)) ≤ (T * (lam * O) + mu * S) * ((1 + mu) / (2 * mu)) :=
    mul_le_mul_of_nonneg_right hb (by positivity)
  have e2 : n * (A1 ^ 2 * l / (4 * ((1 - mu) / (2 * mu))) + A2 * l)
      = n * l * (A1 ^ 2 * mu / (2 * (1 - mu)) + A2) := by
    field_simp; ring
  rw [e2] at ha
  have key : S * ((1 - mu) / 2) ≤ (1 + mu) / (2 * mu) * (T * (lam * O)) +
      n * l * (A1 ^ 2 * mu / (2 * (1 - mu)) + A2) := by
    have e1 : (T * (lam * O) + mu * S) * ((1 + mu) / (2 * mu)) =
        (1 + mu) / (2 * mu) * (T * (lam * O)) + S * ((1 + mu) / 2) := by
      field_simp
    have e3 : (1 - mu) / (2 * mu) * SL = SL * ((1 + mu) / (2 * mu)) - SL := by field_simp; ring
    have e4 : S * ((1 - mu) / 2) = S - S * ((1 + mu) / 2) := by ring
    linarith
  have key2 : S ≤ (2 / (1 - mu)) * ((1 + mu) / (2 * mu) * (T * (lam * O)) +
      n * l * (A1 ^ 2 * mu / (2 * (1 - mu)) + A2)) := by
    have := mul_le_mul_of_nonneg_left key (show (0:ℝ) ≤ 2 / (1 - mu) by positivity)
    have e5 : 2 / (1 - mu) * (S * ((1 - mu) / 2)) = S := by field_simp
    linarith
  rw [one_div_mul_eq_div, div_le_iff₀ hT]
  refine key2.trans (le_of_eq ?_)
  symm
  rw [add_mul, div_mul_cancel₀ _ hT']
  field_simp

end RRAux_RegLearnGames_FirstOrder_theorem_23

open RegLearnGames.FirstOrder Finset RRAux_RegLearnGames_FirstOrder_theorem_23 in
-- Theorem 23: first-order regret gives fast convergence in a smooth cost game.
theorem solution {n d : ℕ} [NeZero d]
    (c : Fin n → (Fin n → Fin d) → ℝ)
    (hc : ∀ i s, c i s ∈ Set.Icc (0 : ℝ) 1)
    (lam mu : ℝ) (hmu₀ : 0 < mu) (hmu₁ : mu < 1)
    (hsmooth : IsSmoothCost c lam mu)
    (A₁ A₂ : ℝ)
    (T : ℕ) (hT : 1 ≤ T)
    (w : ℕ → Fin n → Fin d → ℝ)
    (hw : ∀ t ∈ Finset.Icc 1 T, AGT.IsMixedProfile (w t))
    (hreg : HasFirstOrderRegret c w T A₁ A₂) :
    (1 / (T : ℝ)) *
        (∑ t ∈ Finset.Icc 1 T, socialCost c (w t)) ≤
      lam * (1 + mu) / (mu * (1 - mu)) * optCost c +
        (A₁ ^ 2 * mu / (1 - mu) ^ 2 + 2 * A₂ / (1 - mu)) *
          (n : ℝ) * Real.log (d : ℝ) / (T : ℝ) := by
  classical
  obtain ⟨ss, hss⟩ := hsmooth
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  have hd : (1:ℝ) ≤ d := by
    have := NeZero.ne d
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hl : 0 ≤ Real.log (d:ℝ) := Real.log_nonneg hd
  have hγ : 0 < (1 - mu) / (2 * mu) := by apply div_pos <;> linarith
  have F1 : ∑ i, ∑ t ∈ Icc 1 T, (w t i) ⬝ᵥ costVec c (w t) i =
      ∑ t ∈ Icc 1 T, socialCost c (w t) := by
    rw [Finset.sum_comm]; refine sum_congr rfl (fun t _ => ?_)
    simp only [dot_costVec]; unfold socialCost socialCostPure AGT.expectedPayoff
    simp only [Finset.mul_sum]; rw [Finset.sum_comm]
  have Lnn : ∀ i, 0 ≤ ∑ t ∈ Icc 1 T, costVec c (w t) i (ss i) := by
    intro i; apply sum_nonneg; intro t ht; rw [costVec_eq]; unfold K Pr
    apply sum_nonneg; intro r _
    exact mul_nonneg (prod_nonneg fun j _ => (hw t ht j.1).1 _) (hc _ _).1
  have F2t : ∀ t ∈ Icc 1 T, ∑ i, costVec c (w t) i (ss i) ≤
      lam * optCost c + mu * socialCost c (w t) := by
    intro t ht
    rw [← sum_congr rfl (fun i _ => dev_eq c (w t) i (hw t ht i).2 (ss i)), Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hp : ∀ s, 0 ≤ AGT.profileProb (w t) s := fun s => prod_nonneg fun j _ => (hw t ht j).1 _
    have h1 : ∑ s, AGT.profileProb (w t) s = 1 := by
      unfold AGT.profileProb; rw [← Fintype.prod_sum]; simp [(hw t ht _).2]
    calc _ ≤ ∑ s, AGT.profileProb (w t) s * (lam * optCost c + mu * socialCostPure c s) :=
          sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hss s) (hp s)
      _ = _ := by
          simp_rw [mul_add, sum_add_distrib, ← sum_mul, h1]
          unfold socialCost; rw [mul_sum]
          congr 1
          · ring
          · refine sum_congr rfl fun s _ => by ring
  have F2 : ∑ i, ∑ t ∈ Icc 1 T, costVec c (w t) i (ss i) ≤
      T * (lam * optCost c) + mu * ∑ t ∈ Icc 1 T, socialCost c (w t) := by
    rw [Finset.sum_comm]
    refine (sum_le_sum F2t).trans (le_of_eq ?_)
    rw [sum_add_distrib, sum_const, ← mul_sum]; simp
  have F3 : ∀ i, (∑ t ∈ Icc 1 T, (w t i) ⬝ᵥ costVec c (w t) i) -
      ∑ t ∈ Icc 1 T, costVec c (w t) i (ss i) ≤
      (1 - mu) / (2 * mu) * ∑ t ∈ Icc 1 T, costVec c (w t) i (ss i) +
        (A₁ ^ 2 * Real.log d / (4 * ((1 - mu) / (2 * mu))) + A₂ * Real.log d) := by
    intro i
    have := hreg i (ss i)
    have := amgm A₁ _ _ _ (Lnn i) hl hγ
    linarith
  have F4 := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin n))) => F3 i
  rw [sum_sub_distrib, F1, sum_add_distrib, ← mul_sum] at F4
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at F4
  exact final _ _ _ _ _ _ _ _ _ _ hTpos hmu₀ hmu₁ (by linarith) F2

#print axioms solution
