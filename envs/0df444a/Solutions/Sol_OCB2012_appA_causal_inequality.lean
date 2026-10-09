-- Prove2me | solution 1 for OCB2012.appA_causal_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T10:08:58.853977+00:00
-- url     : https://prove2.me/submissions/2c9a8ee6-7181-4834-b4f2-3cae29f9e214

import Mathlib
import Definitions.Def_OCB2012_appA

namespace OCB2012Sol
open OCB2012

/-- A sum over the three causal relations. -/
lemma sum_causalRel (f : CausalRel → ℝ) :
    ∑ R, f R = f CausalRel.AB + f CausalRel.BA + f CausalRel.incomparable := by
  show ∑ R ∈ ({CausalRel.AB, CausalRel.BA, CausalRel.incomparable} : Finset CausalRel), f R = _
  simp [Finset.sum_insert, add_assoc]

lemma pr_nonneg {P : EventDist} (hP : P.IsProb)
    (E : Bool → Bool → Bool → Bool → Bool → CausalRel → Bool) : 0 ≤ P.pr E := by
  unfold EventDist.pr
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun b' _ =>
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun R _ => ?_
  split_ifs
  · exact hP.1 a b b' x y R
  · exact le_rfl

/-! Marginalization identities: each is a finite rearrangement of the defining sum of `pr`. -/

lemma total_eq (P : EventDist) :
    ∑ a, ∑ b, ∑ b', ∑ x, ∑ y, ∑ R, P a b b' x y R =
      ∑ R₀, P.pr (fun _ _ _ _ _ R => decide (R = R₀)) := by
  simp [EventDist.pr, Fintype.sum_bool, sum_causalRel]; ring

lemma bp_eq (P : EventDist) (v : Bool) :
    P.pr (fun _ _ b' _ _ _ => decide (b' = v)) =
      ∑ R₀, P.pr (fun _ _ b' _ _ R => decide (b' = v ∧ R = R₀)) := by
  cases v <;> simp [EventDist.pr, Fintype.sum_bool, sum_causalRel] <;> ring

lemma B_eq (P : EventDist) (v : Bool) (R₀ : CausalRel) :
    P.pr (fun _ _ b' _ _ R => decide (b' = v ∧ R = R₀)) =
      ∑ a₀, ∑ b₀, P.pr (fun a b b' _ _ R => decide (a = a₀ ∧ b = b₀ ∧ b' = v ∧ R = R₀)) := by
  cases v <;> cases R₀ <;> simp [EventDist.pr, Fintype.sum_bool]

lemma C_eq (P : EventDist) (b₀ v : Bool) (R₀ : CausalRel) :
    P.pr (fun _ b b' _ _ R => decide (b = b₀ ∧ b' = v ∧ R = R₀)) =
      ∑ a₀, P.pr (fun a b b' _ _ R => decide (a = a₀ ∧ b = b₀ ∧ b' = v ∧ R = R₀)) := by
  cases b₀ <;> cases v <;> cases R₀ <;> simp [EventDist.pr, Fintype.sum_bool]

lemma D_eq (P : EventDist) (a₀ v : Bool) (R₀ : CausalRel) :
    P.pr (fun a _ b' _ _ R => decide (a = a₀ ∧ b' = v ∧ R = R₀)) =
      ∑ b₀, P.pr (fun a b b' _ _ R => decide (a = a₀ ∧ b = b₀ ∧ b' = v ∧ R = R₀)) := by
  cases a₀ <;> cases v <;> cases R₀ <;> simp [EventDist.pr, Fintype.sum_bool]

lemma X_sum (P : EventDist) (v : Bool) (R₀ : CausalRel) :
    ∑ x₀, P.pr (fun _ _ b' x _ R => decide (x = x₀ ∧ b' = v ∧ R = R₀)) =
      P.pr (fun _ _ b' _ _ R => decide (b' = v ∧ R = R₀)) := by
  cases v <;> cases R₀ <;> simp [EventDist.pr, Fintype.sum_bool] <;> ring

lemma Y_sum (P : EventDist) (v : Bool) (R₀ : CausalRel) :
    ∑ y₀, P.pr (fun _ _ b' _ y R => decide (y = y₀ ∧ b' = v ∧ R = R₀)) =
      P.pr (fun _ _ b' _ _ R => decide (b' = v ∧ R = R₀)) := by
  cases v <;> cases R₀ <;> simp [EventDist.pr, Fintype.sum_bool] <;> ring

lemma T_sum (P : EventDist) (v : Bool) (R₀ : CausalRel) :
    ∑ x₀, ∑ b₀, P.pr (fun _ b b' x _ R => decide (x = x₀ ∧ b = b₀ ∧ b' = v ∧ R = R₀)) =
      P.pr (fun _ _ b' _ _ R => decide (b' = v ∧ R = R₀)) := by
  cases v <;> cases R₀ <;> simp [EventDist.pr, Fintype.sum_bool] <;> ring

lemma U_sum (P : EventDist) (v : Bool) (R₀ : CausalRel) :
    ∑ y₀, ∑ a₀, P.pr (fun a _ b' _ y R => decide (y = y₀ ∧ a = a₀ ∧ b' = v ∧ R = R₀)) =
      P.pr (fun _ _ b' _ _ R => decide (b' = v ∧ R = R₀)) := by
  cases v <;> cases R₀ <;> simp [EventDist.pr, Fintype.sum_bool] <;> ring

/-- The numerator of `p(x = b | b' = 0)`, split by the common value of `x = b` and by `R`. -/
lemma N0_eq (P : EventDist) :
    P.pr (fun _ b b' x _ _ => decide (x = b) && decide (b' = false)) =
      ∑ R₀, ∑ x₀, P.pr (fun _ b b' x _ R => decide (x = x₀ ∧ b = x₀ ∧ b' = false ∧ R = R₀)) := by
  simp [EventDist.pr, Fintype.sum_bool, sum_causalRel]; ring

/-- The numerator of `p(y = a | b' = 1)`, split by the common value of `y = a` and by `R`. -/
lemma N1_eq (P : EventDist) :
    P.pr (fun a _ b' _ y _ => decide (y = a) && decide (b' = true)) =
      ∑ R₀, ∑ y₀, P.pr (fun a _ b' _ y R => decide (y = y₀ ∧ a = y₀ ∧ b' = true ∧ R = R₀)) := by
  simp [EventDist.pr, Fintype.sum_bool, sum_causalRel]; ring

/-- The arithmetic core of the bound for a value of `R` under which the guess is local:
if `T₁, T₂` satisfy `T_i · B = X_i · p/4` with `B = p/2` and `X₁ + X₂ = B`, and
`T₁ + T₂ + T₃ + T₄ = B` with all `T_i ≥ 0`, then `T₁ + T₂ ≤ p/4`. -/
lemma local_bound {T₁ T₂ T₃ T₄ X₁ X₂ B p : ℝ} (h₁ : 0 ≤ T₁) (h₂ : 0 ≤ T₂) (h₃ : 0 ≤ T₃)
    (h₄ : 0 ≤ T₄) (hB : B = p / 2) (hX : X₁ + X₂ = B) (hT : T₁ + T₂ + T₃ + T₄ = B)
    (e₁ : T₁ * B = X₁ * (p / 4)) (e₂ : T₂ * B = X₂ * (p / 4)) : T₁ + T₂ ≤ p / 4 := by
  subst hB
  have h : (T₁ + T₂ - p / 4) * p = 0 := by linear_combination 2 * e₁ + 2 * e₂ + (p / 2) * hX
  rcases mul_eq_zero.1 h with h | h
  · linarith
  · subst h; linarith

end OCB2012Sol

open OCB2012 OCB2012Sol EventDist in
theorem solution (P : EventDist) (hP : P.IsProb)
    (hFC : ∀ a₀ b₀ b'₀ R₀,
      P.pr (fun a b b' _ _ R => decide (a = a₀ ∧ b = b₀ ∧ b' = b'₀ ∧ R = R₀)) =
        (1 / 8 : ℝ) * P.pr (fun _ _ _ _ _ R => decide (R = R₀)))
    (hCLx : ∀ R₀, R₀ ≠ CausalRel.BA → ∀ b'₀ x₀ b₀,
      P.pr (fun _ b b' x _ R => decide (x = x₀ ∧ b = b₀ ∧ b' = b'₀ ∧ R = R₀)) *
          P.pr (fun _ _ b' _ _ R => decide (b' = b'₀ ∧ R = R₀)) =
        P.pr (fun _ _ b' x _ R => decide (x = x₀ ∧ b' = b'₀ ∧ R = R₀)) *
          P.pr (fun _ b b' _ _ R => decide (b = b₀ ∧ b' = b'₀ ∧ R = R₀)))
    (hCLy : ∀ R₀, R₀ ≠ CausalRel.AB → ∀ b'₀ y₀ a₀,
      P.pr (fun a _ b' _ y R => decide (y = y₀ ∧ a = a₀ ∧ b' = b'₀ ∧ R = R₀)) *
          P.pr (fun _ _ b' _ _ R => decide (b' = b'₀ ∧ R = R₀)) =
        P.pr (fun _ _ b' _ y R => decide (y = y₀ ∧ b' = b'₀ ∧ R = R₀)) *
          P.pr (fun a _ b' _ _ R => decide (a = a₀ ∧ b' = b'₀ ∧ R = R₀))) :
    P.pSucc ≤ 3 / 4 := by
  -- the distribution `p(R)` of the causal relation, and the free-choice marginals
  set p : CausalRel → ℝ := fun R₀ => P.pr (fun _ _ _ _ _ R => decide (R = R₀)) with hp_def
  have hp1 : p CausalRel.AB + p CausalRel.BA + p CausalRel.incomparable = 1 := by
    rw [← sum_causalRel p, hp_def, ← total_eq, hP.2]
  have hB : ∀ v R₀, P.pr (fun _ _ b' _ _ R => decide (b' = v ∧ R = R₀)) = p R₀ / 2 := by
    intro v R₀; rw [B_eq]; simp only [hFC, Fintype.sum_bool]; ring
  have hC : ∀ b₀ v R₀,
      P.pr (fun _ b b' _ _ R => decide (b = b₀ ∧ b' = v ∧ R = R₀)) = p R₀ / 4 := by
    intro b₀ v R₀; rw [C_eq]; simp only [hFC, Fintype.sum_bool]; ring
  have hD : ∀ a₀ v R₀,
      P.pr (fun a _ b' _ _ R => decide (a = a₀ ∧ b' = v ∧ R = R₀)) = p R₀ / 4 := by
    intro a₀ v R₀; rw [D_eq]; simp only [hFC, Fintype.sum_bool]; ring
  have hb' : ∀ v, P.pr (fun _ _ b' _ _ _ => decide (b' = v)) = 1 / 2 := by
    intro v; rw [bp_eq, sum_causalRel]; simp only [hB]; linarith
  -- Alice's guess `x = b` when `b' = 0`
  set T : Bool → Bool → CausalRel → ℝ := fun x₀ b₀ R₀ =>
    P.pr (fun _ b b' x _ R => decide (x = x₀ ∧ b = b₀ ∧ b' = false ∧ R = R₀)) with hT_def
  have hTsum : ∀ R₀, T true true R₀ + T false false R₀ + T true false R₀ + T false true R₀ =
      p R₀ / 2 := by
    intro R₀; rw [← hB false R₀, ← T_sum]; simp only [hT_def, Fintype.sum_bool]; ring
  have hTx : ∀ R₀, R₀ ≠ CausalRel.BA → T true true R₀ + T false false R₀ ≤ p R₀ / 4 := by
    intro R₀ hR
    have hX := X_sum P false R₀
    simp only [Fintype.sum_bool] at hX
    refine local_bound (pr_nonneg hP _) (pr_nonneg hP _) (pr_nonneg hP _) (pr_nonneg hP _)
      (hB false R₀) hX ((hTsum R₀).trans (hB false R₀).symm) ?_ ?_
    · have := hCLx R₀ hR false true true; rwa [hC] at this
    · have := hCLx R₀ hR false false false; rwa [hC] at this
  have hTBA : T true true CausalRel.BA + T false false CausalRel.BA ≤ p CausalRel.BA / 2 := by
    have := hTsum CausalRel.BA
    linarith [pr_nonneg hP (fun _ b b' x _ R =>
        decide (x = true ∧ b = false ∧ b' = false ∧ R = CausalRel.BA)),
      pr_nonneg hP (fun _ b b' x _ R =>
        decide (x = false ∧ b = true ∧ b' = false ∧ R = CausalRel.BA))]
  -- Bob's guess `y = a` when `b' = 1`
  set U : Bool → Bool → CausalRel → ℝ := fun y₀ a₀ R₀ =>
    P.pr (fun a _ b' _ y R => decide (y = y₀ ∧ a = a₀ ∧ b' = true ∧ R = R₀)) with hU_def
  have hUsum : ∀ R₀, U true true R₀ + U false false R₀ + U true false R₀ + U false true R₀ =
      p R₀ / 2 := by
    intro R₀; rw [← hB true R₀, ← U_sum]; simp only [hU_def, Fintype.sum_bool]; ring
  have hUy : ∀ R₀, R₀ ≠ CausalRel.AB → U true true R₀ + U false false R₀ ≤ p R₀ / 4 := by
    intro R₀ hR
    have hY := Y_sum P true R₀
    simp only [Fintype.sum_bool] at hY
    refine local_bound (pr_nonneg hP _) (pr_nonneg hP _) (pr_nonneg hP _) (pr_nonneg hP _)
      (hB true R₀) hY ((hUsum R₀).trans (hB true R₀).symm) ?_ ?_
    · have := hCLy R₀ hR true true true; rwa [hD] at this
    · have := hCLy R₀ hR true false false; rwa [hD] at this
  have hUAB : U true true CausalRel.AB + U false false CausalRel.AB ≤ p CausalRel.AB / 2 := by
    have := hUsum CausalRel.AB
    linarith [pr_nonneg hP (fun a _ b' _ y R =>
        decide (y = true ∧ a = false ∧ b' = true ∧ R = CausalRel.AB)),
      pr_nonneg hP (fun a _ b' _ y R =>
        decide (y = false ∧ a = true ∧ b' = true ∧ R = CausalRel.AB))]
  -- assemble: `p_succ = p(x = b, b' = 0) + p(y = a, b' = 1)` since `p(b' = 0) = p(b' = 1) = 1/2`
  have hN0 := N0_eq P
  have hN1 := N1_eq P
  simp only [sum_causalRel, Fintype.sum_bool] at hN0 hN1
  have h1 := hTx CausalRel.AB (by decide)
  have h2 := hTx CausalRel.incomparable (by decide)
  have h3 := hUy CausalRel.BA (by decide)
  have h4 := hUy CausalRel.incomparable (by decide)
  have hp0 : 0 ≤ p CausalRel.AB := pr_nonneg hP _
  have hp0' : 0 ≤ p CausalRel.BA := pr_nonneg hP _
  have hp0'' : 0 ≤ p CausalRel.incomparable := pr_nonneg hP _
  have hhalf : ∀ z : ℝ, 1 / 2 * (z / (1 / 2)) = z := fun z => by ring
  simp only [EventDist.pSucc, EventDist.cond, hb', hN0, hN1, hhalf]
  simp only [hT_def, hU_def] at h1 h2 h3 h4 hTBA hUAB
  linarith
