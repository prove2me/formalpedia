-- Prove2me | solution 1 for SidB.weighted_eq_hyper
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:43:14.151246+00:00
-- url     : https://prove2.me/submissions/953f3474-9277-4bb2-97c9-438170e14f5b

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

theorem solution : ¬ (∀ (g : Graphon) (m r : ℕ) (α β : ℕ → ℕ) (hr : 0 < r) (hmr : r ≤ m)
    (hα : ∀ k, 1 ≤ k → k ≤ r → α k = β k * (m - k).choose (r - k))
    (hβ : ∀ k, 1 ≤ k → k ≤ r → 0 < β k),
    g.downsetDens m r (fun k => (α k : ℝ)) = rDens g (hAlpha m r β) (qOf r β)) := by
  intro H
  have h := H g73s_model 1 1 (fun _ => 1) (fun _ => 1) one_pos le_rfl
    (fun k _ _ => by simp) (fun _ _ _ => one_pos)
  rw [g73s_rDens, g73s_q1] at h
  simp only [Fin.prod_univ_one, Real.rpow_one] at h
  have hL : g73s_model.downsetDens 1 1 (fun k => (((fun _ => 1 : ℕ → ℕ) k : ℕ) : ℝ)) =
      (1/2 : ℝ) ^ Fintype.card {s : Finset (Fin 1) // 0 < s.card ∧ s.card ≤ 1} := by
    show (∏ s : {s : Finset (Fin 1) // 0 < s.card ∧ s.card ≤ 1},
      (∏ i ∈ s.1, (1/2 : ℝ)) ^ (((1 : ℕ) : ℝ))) = _
    rw [← Finset.card_univ, ← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro s _
    rw [Nat.cast_one, Real.rpow_one, Finset.prod_const]
    have := s.2
    have : s.1.card = 1 := by omega
    rw [this, pow_one]
  rw [hL] at h
  have hc : Fintype.card {s : Finset (Fin 1) // 0 < s.card ∧ s.card ≤ 1} ≤ 2 := by
    refine le_trans (Fintype.card_subtype_le _) (le_of_eq ?_)
    simp [Fintype.card_finset]
  have hl := g73s_card_lower 1
  norm_num at hl
  have a1 := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) hl
  have a2 := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) hc
  have a3 : (1/2 : ℝ) ^ 8 < (1/2) ^ 2 :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by norm_num)
  linarith
