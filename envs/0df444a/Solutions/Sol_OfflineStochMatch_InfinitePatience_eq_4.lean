-- Prove2me | solution 1 for OfflineStochMatch.InfinitePatience.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T00:38:57.680624+00:00
-- url     : https://prove2.me/submissions/f77c0015-bc0a-41a2-82b8-b2589bbebd1f

import Mathlib
import Definitions.Def_OfflineStochMatch_InfinitePatience_Setting

open OfflineStochMatch.InfinitePatience
open scoped Classical

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def flipAt (e : E) : (E → Bool) ≃ (E → Bool) where
  toFun c := Function.update c e (!c e)
  invFun c := Function.update c e (!c e)
  left_inv c := by
    ext f
    by_cases hf : f = e
    · subst hf; simp
    · simp [hf]
  right_inv c := by
    ext f
    by_cases hf : f = e
    · subst hf; simp
    · simp [hf]

@[simp]
lemma flipAt_self (e : E) (c : E → Bool) : flipAt e c e = !c e := by
  change Function.update c e (!c e) e = !c e
  exact Function.update_self e (!c e) c

lemma flipAt_ne (e f : E) (hf : f ≠ e) (c : E → Bool) : flipAt e c f = c f := by
  change Function.update c e (!c e) f = c f
  exact Function.update_of_ne hf (!c e) c

def coinWeightErase (q : E → ℝ) (e : E) (c : E → Bool) : ℝ :=
  ∏ f ∈ Finset.univ.erase e, bern (q f) (c f)

lemma coinWeight_eq_mul_erase (q : E → ℝ) (e : E) (c : E → Bool) :
    coinWeight q c = bern (q e) (c e) * coinWeightErase q e c := by
  unfold coinWeight coinWeightErase
  exact (Finset.mul_prod_erase Finset.univ (fun f => bern (q f) (c f)) (Finset.mem_univ e)).symm

lemma coinWeightErase_flipAt (q : E → ℝ) (e : E) (c : E → Bool) :
    coinWeightErase q e (flipAt e c) = coinWeightErase q e c := by
  unfold coinWeightErase
  refine Finset.prod_congr rfl (fun f hf => ?_)
  rw [flipAt_ne e f (Finset.ne_of_mem_erase hf)]

lemma sum_coinWeight_indep (q : E → ℝ) (e : E) (Φ : (E → Bool) → ℝ)
    (hΦ : ∀ (c : E → Bool) (b : Bool), Φ (Function.update c e b) = Φ c) :
    ∑ c : E → Bool, coinWeight q c * (if c e = true then Φ c else 0) =
      q e * ∑ c : E → Bool, coinWeight q c * Φ c := by
  let L : (E → Bool) → ℝ := fun c => coinWeight q c * (if c e = true then Φ c else 0)
  let R : (E → Bool) → ℝ := fun c => coinWeight q c * Φ c
  have hL_flip : ∑ c : E → Bool, L (flipAt e c) = ∑ c : E → Bool, L c :=
    Equiv.sum_comp (flipAt e) L
  have hR_flip : ∑ c : E → Bool, R (flipAt e c) = ∑ c : E → Bool, R c :=
    Equiv.sum_comp (flipAt e) R
  have hpair : ∀ c : E → Bool, L c + L (flipAt e c) = q e * (R c + R (flipAt e c)) := by
    intro c
    have hΦ_flip : Φ (flipAt e c) = Φ c := hΦ c (!c e)
    dsimp [L, R]
    rw [coinWeight_eq_mul_erase q e c, coinWeight_eq_mul_erase q e (flipAt e c),
      coinWeightErase_flipAt, flipAt_self, hΦ_flip]
    cases c e <;> simp [bern] <;> ring
  have hsum : ∑ c : E → Bool, (L c + L (flipAt e c)) =
      ∑ c : E → Bool, q e * (R c + R (flipAt e c)) :=
    Finset.sum_congr rfl (fun c _ => hpair c)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, hL_flip, hR_flip] at hsum
  dsimp [L, R] at hsum
  linarith

lemma sum_coinWeight (q : E → ℝ) :
    ∑ c : E → Bool, coinWeight q c = 1 := by
  unfold coinWeight
  rw [(Fintype.prod_sum (fun (i : E) (b : Bool) => bern (q i) b)).symm]
  have h1 : ∀ i ∈ (Finset.univ : Finset E), (∑ b : Bool, bern (q i) b) = 1 := by
    intro i _
    rw [Fintype.sum_bool]
    unfold bern
    simp
  rw [Finset.prod_congr rfl h1, Finset.prod_const_one]

lemma card_equiv_fin :
    Fintype.card (E ≃ Fin (Fintype.card E)) = (Fintype.card E).factorial := by
  rw [Fintype.card_congr ((Fintype.equivFin E).equivCongr (Equiv.refl _)),
    Fintype.card_perm, Fintype.card_fin]

lemma foldl_step_congr (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (Y Y' A A' P P' : E → Bool) (e : E)
    (hY : ∀ f ≠ e, Y' f = Y f) (hA : ∀ f ≠ e, A' f = A f) (hP : ∀ f ≠ e, P' f = P f)
    (l : List E) (hl : ∀ f ∈ l, f ≠ e) (st : RunState V) :
    l.foldl (step G t Y' A' P') st = l.foldl (step G t Y A P) st := by
  induction l generalizing st with
  | nil => rfl
  | cons f fs ih =>
    have hf : f ≠ e := hl f List.mem_cons_self
    have hstep : step G t Y' A' P' st f = step G t Y A P st f := by
      unfold step
      rw [hY f hf, hA f hf, hP f hf]
    simp only [List.foldl_cons, hstep]
    exact ih (fun g hg => hl g (List.mem_cons_of_mem f hg)) _

lemma mem_stateBefore_list {σ : E ≃ Fin (Fintype.card E)} {e f : E}
    (hf : f ∈ (((List.finRange (Fintype.card E)).filter (fun i => decide (i < σ e))).map σ.symm)) :
    f ≠ e := by
  rcases List.mem_map.mp hf with ⟨i, hi, rfl⟩
  rw [List.mem_filter, decide_eq_true_eq] at hi
  intro h
  have h1 : σ (σ.symm i) = σ e := congrArg σ h
  rw [Equiv.apply_symm_apply] at h1
  exact absurd h1 (ne_of_lt hi.2)

lemma stateBefore_update_Y (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) (b : Bool) :
    stateBefore G t σ (Function.update Y e b) A P e = stateBefore G t σ Y A P e := by
  unfold stateBefore
  refine foldl_step_congr G t Y (Function.update Y e b) A A P P e
    (fun f hf => Function.update_of_ne hf b Y) (fun _ _ => rfl) (fun _ _ => rfl) _ ?_ initState
  intro f hf
  exact mem_stateBefore_list hf

lemma stateBefore_update_A (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) (b : Bool) :
    stateBefore G t σ Y (Function.update A e b) P e = stateBefore G t σ Y A P e := by
  unfold stateBefore
  refine foldl_step_congr G t Y Y A (Function.update A e b) P P e
    (fun _ _ => rfl) (fun f hf => Function.update_of_ne hf b A) (fun _ _ => rfl) _ ?_ initState
  intro f hf
  exact mem_stateBefore_list hf

lemma stateBefore_update_P (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) (b : Bool) :
    stateBefore G t σ Y A (Function.update P e b) e = stateBefore G t σ Y A P e := by
  unfold stateBefore
  refine foldl_step_congr G t Y Y A A P (Function.update P e b) e
    (fun _ _ => rfl) (fun _ _ => rfl) (fun f hf => Function.update_of_ne hf b P) _ ?_ initState
  intro f hf
  exact mem_stateBefore_list hf

lemma isFree_update_Y (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) (b : Bool) :
    IsFree G t σ (Function.update Y e b) A P e ↔ IsFree G t σ Y A P e := by
  unfold IsFree
  rw [stateBefore_update_Y]

lemma isFree_update_A (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) (b : Bool) :
    IsFree G t σ Y (Function.update A e b) P e ↔ IsFree G t σ Y A P e := by
  unfold IsFree
  rw [stateBefore_update_A]

lemma isFree_update_P (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) (b : Bool) :
    IsFree G t σ Y A (Function.update P e b) e ↔ IsFree G t σ Y A P e := by
  unfold IsFree
  rw [stateBefore_update_P]

lemma prob_and_Pe (p y : E → ℝ) (aT : ℝ → ℝ) (e : E)
    (Ψ : (E ≃ Fin (Fintype.card E)) → (E → Bool) → (E → Bool) → (E → Bool) → Prop)
    (hΨ : ∀ σ Y A P b, Ψ σ Y A (Function.update P e b) ↔ Ψ σ Y A P) :
    prob p y aT (fun σ Y A P => Ψ σ Y A P ∧ P e = true) = p e * prob p y aT Ψ := by
  unfold prob
  rw [← mul_assoc, mul_comm (p e), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  trans coinWeight y Y * coinWeight (fun f => aT (p f * y f)) A *
      ∑ P : E → Bool, coinWeight p P * (if P e = true then (if Ψ σ Y A P then 1 else 0) else 0)
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    by_cases hP : P e = true <;> by_cases hψ : Ψ σ Y A P <;> simp [hP, hψ] <;> ring
  · rw [sum_coinWeight_indep p e (fun P => if Ψ σ Y A P then (1 : ℝ) else 0)]
    · rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun P _ => by ring)
    · intro P b
      exact if_ctx_congr (hΨ σ Y A P b) (fun _ => rfl) (fun _ => rfl)

lemma prob_and_Ae (p y : E → ℝ) (aT : ℝ → ℝ) (e : E)
    (Ψ : (E ≃ Fin (Fintype.card E)) → (E → Bool) → (E → Bool) → (E → Bool) → Prop)
    (hΨ : ∀ σ Y A P b, Ψ σ Y (Function.update A e b) P ↔ Ψ σ Y A P) :
    prob p y aT (fun σ Y A P => Ψ σ Y A P ∧ A e = true) = aT (p e * y e) * prob p y aT Ψ := by
  unfold prob
  rw [← mul_assoc, mul_comm (aT (p e * y e)), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  trans coinWeight y Y * coinWeight p P *
      ∑ A : E → Bool, coinWeight (fun f => aT (p f * y f)) A *
        (if A e = true then (if Ψ σ Y A P then 1 else 0) else 0)
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    by_cases hA : A e = true <;> by_cases hψ : Ψ σ Y A P <;> simp [hA, hψ] <;> ring
  · rw [sum_coinWeight_indep (fun f => aT (p f * y f)) e (fun A => if Ψ σ Y A P then (1 : ℝ) else 0)]
    · rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun A _ => by ring)
    · intro A b
      exact if_ctx_congr (hΨ σ Y A P b) (fun _ => rfl) (fun _ => rfl)

lemma prob_and_Ye (p y : E → ℝ) (aT : ℝ → ℝ) (e : E)
    (Ψ : (E ≃ Fin (Fintype.card E)) → (E → Bool) → (E → Bool) → (E → Bool) → Prop)
    (hΨ : ∀ σ Y A P b, Ψ σ (Function.update Y e b) A P ↔ Ψ σ Y A P) :
    prob p y aT (fun σ Y A P => Ψ σ Y A P ∧ Y e = true) = y e * prob p y aT Ψ := by
  unfold prob
  rw [← mul_assoc, mul_comm (y e), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  trans coinWeight (fun f => aT (p f * y f)) A * coinWeight p P *
      ∑ Y : E → Bool, coinWeight y Y * (if Y e = true then (if Ψ σ Y A P then 1 else 0) else 0)
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    by_cases hY : Y e = true <;> by_cases hψ : Ψ σ Y A P <;> simp [hY, hψ] <;> ring
  · rw [sum_coinWeight_indep y e (fun Y => if Ψ σ Y A P then (1 : ℝ) else 0)]
    · rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Y _ => by ring)
    · intro Y b
      exact if_ctx_congr (hΨ σ Y A P b) (fun _ => rfl) (fun _ => rfl)

lemma prob_true (p y : E → ℝ) (aT : ℝ → ℝ) :
    prob p y aT (fun _ _ _ _ => True) = 1 := by
  unfold prob
  simp only [if_true, mul_one]
  simp_rw [← Finset.mul_sum, sum_coinWeight, mul_one]
  simp_rw [← Finset.mul_sum, sum_coinWeight, mul_one]
  simp_rw [sum_coinWeight, Finset.sum_const, Finset.card_univ,
    card_equiv_fin, nsmul_eq_mul, mul_one]
  have h0 : ((Fintype.card E).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  exact one_div_mul_cancel h0

lemma prob_Ye_Ae (p y : E → ℝ) (aT : ℝ → ℝ) (e : E) :
    prob p y aT (fun _ Y A _ => Y e = true ∧ A e = true) = y e * aT (p e * y e) := by
  have heq : (fun (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) => Y e = true ∧ A e = true) =
      (fun σ Y A P => (True ∧ Y e = true) ∧ A e = true) := by
    ext σ Y A P; simp
  rw [heq, prob_and_Ae p y aT e (fun _ Y _ _ => True ∧ Y e = true) (fun _ _ _ _ _ => Iff.rfl),
    prob_and_Ye p y aT e (fun _ _ _ _ => True) (fun _ _ _ _ _ => Iff.rfl), prob_true]
  ring

lemma prob_isProbed_and_Pe (G : EdmondsMatching65.Polyhedron.Graph V E) (p y : E → ℝ)
    (t : V → ℕ∞) (aT : ℝ → ℝ) (e : E) :
    prob p y aT (fun σ Y A P => IsProbed G t σ Y A P e ∧ P e = true) =
      p e * y e * aT (p e * y e) * probFree G p t y aT e := by
  rw [prob_and_Pe p y aT e (fun σ Y A P => IsProbed G t σ Y A P e)]
  · have heq : (fun σ Y A P => IsProbed G t σ Y A P e) =
        (fun σ Y A P => (IsFree G t σ Y A P e ∧ Y e = true) ∧ A e = true) := by
      ext σ Y A P
      unfold IsProbed
      tauto
    rw [heq, prob_and_Ae p y aT e (fun σ Y A P => IsFree G t σ Y A P e ∧ Y e = true),
      prob_and_Ye p y aT e (fun σ Y A P => IsFree G t σ Y A P e)]
    · unfold probFree
      ring
    · intro σ Y A P b
      exact isFree_update_Y G t σ Y A P e b
    · intro σ Y A P b
      simp only [isFree_update_A]
  · intro σ Y A P b
    unfold IsProbed
    simp only [isFree_update_P]

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (p y w : E → ℝ) (t : V → ℕ∞) (aT : ℝ → ℝ)
    (_hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (_hy : LPFeasible G p t y)
    (_haT : ∀ z ∈ Set.Icc (0 : ℝ) 1, aT z ∈ Set.Icc (0 : ℝ) 1) :
    ∑ e, w e * prob p y aT (fun σ Y A P => IsProbed G t σ Y A P e ∧ P e = true)
        = ∑ e, w e * p e * probFree G p t y aT e *
            prob p y aT (fun _ Y A _ => Y e = true ∧ A e = true) ∧
      ∑ e, w e * p e * probFree G p t y aT e *
            prob p y aT (fun _ Y A _ => Y e = true ∧ A e = true)
        = ∑ e, w e * p e * y e * aT (p e * y e) * probFree G p t y aT e := by
  have h2 : ∑ e, w e * p e * probFree G p t y aT e *
        prob p y aT (fun _ Y A _ => Y e = true ∧ A e = true) =
      ∑ e, w e * p e * y e * aT (p e * y e) * probFree G p t y aT e := by
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [prob_Ye_Ae]
    ring
  refine ⟨?_, h2⟩
  rw [h2]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [prob_isProbed_and_Pe]
  ring
