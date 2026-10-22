-- Prove2me | solution 1 for SidB.weakly_norming_bound
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:43:13.277462+00:00
-- url     : https://prove2.me/submissions/bde4b9a4-8c7a-466f-97a2-7828c7dbb455

import Mathlib
import Definitions.Def_SidB_graph
import Definitions.Def_SidB_hyper
open SidB

noncomputable def g73s_model : Graphon where
  dom := Unit
  W := fun _ _ => 1/2
  w_nonneg := by intros; norm_num
  w_symm := by intros; rfl
  w_le_one := by intros; norm_num
  exp := fun _ _ f => f (fun _ => ())
  exp_one := by intros; rfl
  exp_mono := by intro S hS f g h; exact h _
  exp_linear := by intros; rfl
  exp_fubini := by
    intro S T hS hT hST F
    show F _ = F _
    congr 1

  exp_transport := by intros; rfl
  exp_holder := by
    intro S hS J hJ f hf hJ0
    apply le_of_eq
    apply Finset.prod_congr rfl
    intro j _
    rw [one_div, Real.rpow_rpow_inv (hf j _) (Nat.cast_ne_zero.mpr hJ0.ne')]

lemma g73s_finSub {A : Type} [DecidableEq A] (s t : Finset A) : finSub s t = decide (s ⊆ t) := by
  unfold finSub
  rw [Bool.eq_iff_iff]; simp [List.all_eq_true, Finset.subset_iff]

lemma g73s_finEq {A : Type} [DecidableEq A] (s t : Finset A) : finEq s t = decide (s = t) := by
  unfold finEq
  rw [g73s_finSub, g73s_finSub, Bool.eq_iff_iff]
  simp [Finset.Subset.antisymm_iff]

lemma g73s_prod_cond {α : Type} [Fintype α] (P : α → Bool) (a : ℝ) :
    ∏ e, cond (P e) a 1 = a ^ (Finset.univ.filter (fun e => P e = true)).card := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun e => P e = true)]
  rw [Finset.prod_congr rfl (g := fun _ => a), Finset.prod_const, Finset.prod_congr rfl (g := fun _ => 1),
    Finset.prod_const_one, mul_one]
  · intro e he; simp at he; simp [he]
  · intro e he; simp at he; simp [he]

lemma g73s_rDens {r : ℕ} (R : RGraph r) [Fintype R.vert] (q : Fin r → ℝ) :
    rDens g73s_model R q = (∏ k : Fin r, (1/2 : ℝ) ^ q k) ^
      (Finset.univ.filter (fun e => R.edge e = true)).card := by
  rw [← g73s_prod_cond]; rfl

lemma g73s_q1 : qOf 1 (fun _ => 1) = fun _ => 1 := by
  funext k; fin_cases k; simp [qOf]

lemma g73s_betaMax : betaMax 1 (fun _ => 1) = 1 := by decide

lemma g73s_edge (m : ℕ) (a p : Fin m) (B S : Finset (Fin m)) (c : Fin (betaMax 1 (fun _ => 1) + 1)) :
    hAlphaEdge m 1 (fun _ => 1) ![(true, a, B, S, c), (false, p, {a}, {a}, 0)] = true := by
  simp [hAlphaEdge, g73s_finSub, g73s_finEq, HV.isPoint, HV.sub, HV.big, HV.cp, HV.pt, List.all_eq_true]

lemma g73s_card_lower (m : ℕ) :
    m * m * (2 ^ m * 2 ^ m * 2) ≤
      (Finset.univ.filter (fun e => (hAlpha m 1 (fun _ => 1)).edge e = true)).card := by
  let f : Fin m × Fin m × Finset (Fin m) × Finset (Fin m) × Fin (betaMax 1 (fun _ => 1) + 1) →
      (Fin 2 → HV m 1 (fun _ => 1)) :=
    fun t => ![(true, t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2), (false, t.2.1, {t.1}, {t.1}, 0)]
  have hinj : Function.Injective f := by
    intro t t' h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [f] at h0 h1
    obtain ⟨a, p, B, S, c⟩ := t
    obtain ⟨a', p', B', S', c'⟩ := t'
    simp_all
  have := Finset.card_le_card_of_injOn f (s := Finset.univ)
    (t := Finset.univ.filter (fun e => (hAlpha m 1 (fun _ => 1)).edge e = true))
    (by intro t _; simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and]; exact g73s_edge m _ _ _ _ _)
    hinj.injOn
  refine le_trans (le_of_eq ?_) this
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_finset, g73s_betaMax]
  ring

lemma g73s_card_upper :
    (Finset.univ.filter (fun e => (gAlpha 1 (fun _ => 1)).edge e = true)).card ≤ 256 := by
  refine le_trans (Finset.card_filter_le _ _) (le_of_eq ?_)
  rw [Finset.card_univ]
  show Fintype.card (Fin 2 → HV 1 1 (fun _ => 1)) = 256
  simp [Fintype.card_fun, Fintype.card_prod, Fintype.card_finset, g73s_betaMax]

theorem solution : ¬ (∀ (g : Graphon) (m r : ℕ) (β : ℕ → ℕ) (hr : 0 < r) (hmr : r ≤ m)
    (hβ : ∀ k, 1 ≤ k → k ≤ r → 0 < β k),
    rDens g (gAlpha r β) (qOf r β) ^ (m.choose r : ℝ) ≤ rDens g (hAlpha m r β) (qOf r β)) := by
  intro H
  have h := H g73s_model 3 1 (fun _ => 1) one_pos (by norm_num) (fun _ _ _ => one_pos)
  rw [g73s_rDens, g73s_rDens, g73s_q1] at h
  simp only [Fin.prod_univ_one, Real.rpow_one] at h
  have h3 : ((Nat.choose 3 1 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  rw [h3, Real.rpow_natCast, ← pow_mul] at h
  have hu := g73s_card_upper
  have hl := g73s_card_lower 3
  norm_num at hl
  have a1 := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) hl
  have a2 := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    (Nat.mul_le_mul_right 3 hu)
  have a3 : (1/2 : ℝ) ^ 1152 < (1/2) ^ (256 * 3) :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by norm_num)
  linarith
