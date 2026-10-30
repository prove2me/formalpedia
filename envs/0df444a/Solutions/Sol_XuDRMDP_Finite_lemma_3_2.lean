-- Prove2me | solution 1 for XuDRMDP.Finite.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:35:48.595996+00:00
-- url     : https://prove2.me/submissions/e50032fd-13f4-4663-bce2-f6a0540da3ad

import Mathlib
import Definitions.Def_XuDRMDP_Finite_Setup
import Definitions.Def_XuDRMDP_Finite_Policies
import Definitions.Def_XuDRMDP_Finite_Ambiguity
import Definitions.Def_XuDRMDP_Finite_Returns
import Definitions.Def_XuDRMDP_Finite_Robustness

open MeasureTheory XuDRMDP.Finite

section S226X
variable {n : ℕ} {a : Fin n → ℕ}

lemma s226x_pol (π : Policy a) {p1 p2 : List (Sigma fun s => Fin (a s))} (e : p1 = p2)
    (s : Fin n) (c : Fin (a s)) : (π ⟨p1, s⟩).val c = (π ⟨p2, s⟩).val c := by
  subst e; rfl

lemma s226x_condiff (G : Setup n a) (h : History a) (b : Fin (a h.state)) (k : ℕ)
    (z' : Suffix a k) (jf : Fin n) :
    ((∀ t : Fin (k+1), G.stage ((Fin.cons ⟨h.state, b⟩ z' : Suffix a (k+1)) t).1 =
        G.stage h.state + t.val) ∧
      (∀ t : Fin (k+1), t.val = 0 → ((Fin.cons ⟨h.state, b⟩ z' : Suffix a (k+1)) t).1 = h.state) ∧
      G.stage jf = G.stage h.state + (k+1) ∧ (k + 1 = 0 → jf = h.state)) ↔
    (G.stage (successorState (Fin.cons ⟨h.state, b⟩ z' : Suffix a (k+1)) jf 0) = G.stage h.state + 1 ∧
      ((∀ t : Fin k, G.stage (z' t).1 =
          G.stage (successorState (Fin.cons ⟨h.state, b⟩ z' : Suffix a (k+1)) jf 0) + t.val) ∧
        (∀ t : Fin k, t.val = 0 →
          (z' t).1 = successorState (Fin.cons ⟨h.state, b⟩ z' : Suffix a (k+1)) jf 0) ∧
        G.stage jf = G.stage (successorState (Fin.cons ⟨h.state, b⟩ z' : Suffix a (k+1)) jf 0) + k ∧
        (k = 0 → jf = successorState (Fin.cons ⟨h.state, b⟩ z' : Suffix a (k+1)) jf 0))) := by
  cases k with
  | zero =>
    have hs : successorState (Fin.cons ⟨h.state, b⟩ z' : Suffix a (0+1)) jf 0 = jf := by
      simp [successorState]
    rw [hs]
    constructor
    · rintro ⟨_, _, h3, _⟩
      exact ⟨by simpa using h3, fun t => t.elim0, fun t => t.elim0, by simp, fun _ => rfl⟩
    · rintro ⟨h1, -, -, -, -⟩
      refine ⟨fun t => ?_, fun t _ => ?_, by simpa using h1, fun h => absurd h (by omega)⟩
      · have : t = 0 := by ext; have := t.isLt; first | (simp; done) | (simp; omega)
        subst this; simp
      · have : t = 0 := by ext; have := t.isLt; first | (simp; done) | (simp; omega)
        subst this; simp
  | succ k =>
    have hs : successorState (Fin.cons ⟨h.state, b⟩ z' : Suffix a (k+1+1)) jf 0 = (z' 0).1 := by
      first | (simp [successorState]; done) | (simp [successorState]; rfl)
    rw [hs]
    constructor
    · rintro ⟨h1, -, h3, -⟩
      have h10 := h1 (Fin.succ 0)
      simp only [Fin.cons_succ, Fin.val_succ, Fin.val_zero] at h10
      refine ⟨by simpa using h10, fun t => ?_, fun t ht => ?_, by omega, fun h => absurd h (by omega)⟩
      · have := h1 t.succ
        simp only [Fin.cons_succ, Fin.val_succ] at this
        omega
      · have : t = 0 := Fin.ext ht
        rw [this]
    · rintro ⟨h0, h1, -, h3, -⟩
      refine ⟨fun t => ?_, fun t ht => ?_, by omega, fun h => absurd h (by omega)⟩
      · refine Fin.cases ?_ (fun t' => ?_) t
        · simp
        · have := h1 t'
          simp only [Fin.cons_succ, Fin.val_succ]
          omega
      · have : t = 0 := Fin.ext ht
        subst this; simp

end S226X

section S226X2
variable {n : ℕ} {a : Fin n → ℕ}

lemma s226x_key (G : Setup n a) (π : Policy a) (x : Parameters n a) (h : History a)
    (b : Fin (a h.state)) (k : ℕ) (z' : Suffix a k) (jf : Fin n) :
    trajectoryProbability G π x h (Fin.cons ⟨h.state, b⟩ z' : Suffix a (k+1)) jf =
      (π h).val b * ∑ j : Fin n, if G.stage j = G.stage h.state + 1 then
        (x h.state).1 b j * trajectoryProbability G π x (h.extend b j) z' jf else 0 := by
  have hc := s226x_condiff G h b k z' jf
  set z : Suffix a (k+1) := Fin.cons ⟨h.state, b⟩ z' with hzdef
  set js := successorState z jf 0 with hjs
  have hzero : ∀ j, j ≠ js → trajectoryProbability G π x (h.extend b j) z' jf = 0 := by
    intro j hj
    unfold trajectoryProbability
    rw [if_neg]
    rintro ⟨-, h2, -, h4⟩
    apply hj
    cases k with
    | zero =>
      have e : js = jf := by rw [hjs]; simp [successorState]
      rw [e]; exact (h4 rfl).symm
    | succ k =>
      have e : js = (z' 0).1 := by
        rw [hjs, hzdef]; first | (simp [successorState]; done) | (simp [successorState]; rfl)
      rw [e]; exact (h2 0 rfl).symm
  rw [Finset.sum_eq_single js (fun j _ hj => by rw [hzero j hj]; simp) (by simp)]
  have h0 : (π (suffixHistory h z 0)).val (z 0).2 = (π h).val b := by
    show (π ⟨h.past ++ List.take 0 (List.ofFn z), h.state⟩).val b = (π ⟨h.past, h.state⟩).val b
    exact s226x_pol π (by simp) h.state b
  have hsucc : ∀ t' : Fin k,
      (π (suffixHistory h z t'.succ)).val (z t'.succ).2 *
        (x (z t'.succ).1).1 (z t'.succ).2 (successorState z jf t'.succ) =
      (π (suffixHistory (h.extend b js) z' t')).val (z' t').2 *
        (x (z' t').1).1 (z' t').2 (successorState z' jf t') := by
    intro t'
    have e1 : (π (suffixHistory h z t'.succ)).val (z t'.succ).2 =
        (π (suffixHistory (h.extend b js) z' t')).val (z' t').2 := by
      show (π ⟨h.past ++ List.take (t'.val+1) (List.ofFn z), (z' t').1⟩).val (z' t').2 =
        (π ⟨(h.past ++ [⟨h.state, b⟩]) ++ List.take t'.val (List.ofFn z'), (z' t').1⟩).val (z' t').2
      apply s226x_pol
      rw [hzdef, List.ofFn_succ, List.take_succ_cons]
      simp
    have e2 : successorState z jf t'.succ = successorState z' jf t' := by
      simp only [successorState, Fin.val_succ]
      split_ifs with q1 q2 q2
      · rfl
      · omega
      · omega
      · rfl
    rw [e1, e2]; rfl
  have hmain : (∏ t : Fin (k+1), (π (suffixHistory h z t)).val (z t).2 *
      (x (z t).1).1 (z t).2 (successorState z jf t)) =
      (π h).val b * ((x h.state).1 b js * ∏ t : Fin k,
        (π (suffixHistory (h.extend b js) z' t)).val (z' t).2 *
          (x (z' t).1).1 (z' t).2 (successorState z' jf t)) := by
    rw [Fin.prod_univ_succ, Finset.prod_congr rfl (fun t' _ => hsucc t'), h0]
    show (π h).val b * (x h.state).1 b js * _ = _
    ring
  have hst : (h.extend b js).state = js := rfl
  unfold trajectoryProbability
  simp only [hst, Nat.add_one_ne_zero, false_implies, and_true, IsEmpty.forall_iff] at hc ⊢
  split_ifs
  all_goals first | exact hmain | (simp; done) | (exfalso; tauto)

lemma s226x_swap {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (c : ℝ)
    (f : γ → α → β → ℝ) (g : α → β → ℝ) :
    ∑ x, ∑ y, (c * ∑ j, f j x y) * g x y = c * ∑ j, ∑ x, ∑ y, f j x y * g x y := by
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  symm; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro _ _; rw [Finset.sum_comm]

lemma s226x_dec (G : Setup n a) (π : Policy a) (x : Parameters n a) (h : History a) (k : ℕ)
    (F : Suffix a (k+1) → ℝ) :
    ∑ z : Suffix a (k+1), ∑ jf : Fin n, trajectoryProbability G π x h z jf * F z =
      ∑ b : Fin (a h.state), (π h).val b * ∑ j : Fin n,
        if G.stage j = G.stage h.state + 1 then (x h.state).1 b j *
          ∑ z' : Suffix a k, ∑ jf : Fin n, trajectoryProbability G π x (h.extend b j) z' jf *
            F (Fin.cons ⟨h.state, b⟩ z') else 0 := by
  rw [← (Fin.consEquiv (fun _ : Fin (k+1) => Sigma fun s => Fin (a s))).sum_comp,
    Fintype.sum_prod_type, Fintype.sum_sigma, Finset.sum_eq_single h.state]
  · apply Finset.sum_congr rfl; intro b _
    simp only [Fin.consEquiv, Equiv.coe_fn_mk]
    simp_rw [s226x_key G π x h b k]
    rw [s226x_swap]
    congr 1; apply Finset.sum_congr rfl; intro j _
    split_ifs
    · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z' _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro jf _; ring
    · simp
  · intro s _ hs
    apply Finset.sum_eq_zero; intro b _
    apply Finset.sum_eq_zero; intro z' _
    apply Finset.sum_eq_zero; intro jf _
    rw [trajectoryProbability, if_neg, zero_mul]
    rintro ⟨-, h2, -⟩
    exact hs (h2 0 rfl)
  · simp

end S226X2

section S226X3
variable {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]

lemma s226x_rowsum {G : Setup n a} {s : Fin n} {y : Local n a s} (hy : ValidLocal G s y)
    (b : Fin (a s)) : ∑ j, y.1 b j = 1 := by
  obtain ⟨⟨M, hM⟩, -, -⟩ := hy
  subst hM
  exact (hasSum_fintype _).unique (M.trans_sum s b)

lemma s226x_rownn {G : Setup n a} {s : Fin n} {y : Local n a s} (hy : ValidLocal G s y)
    (b : Fin (a s)) (j : Fin n) : 0 ≤ y.1 b j := by
  obtain ⟨⟨M, hM⟩, -, -⟩ := hy
  subst hM
  exact M.trans_nonneg s b j

lemma s226x_next {G : Setup n a} {s : Fin n} {y : Local n a s} (hy : ValidLocal G s y)
    (hs : G.stage s + 1 < G.horizon) (b : Fin (a s)) :
    ∑ j, (if G.stage j = G.stage s + 1 then y.1 b j else 0) = 1 := by
  rw [← s226x_rowsum hy b]
  apply Finset.sum_congr rfl; intro j _
  split_ifs with h
  · rfl
  · exact (hy.2.2 hs b j h).symm

lemma s226x_tot (G : Setup n a) (π : Policy a) (x : Parameters n a)
    (hx : ∀ s, ValidLocal G s (x s)) :
    ∀ (k : ℕ) (h : History a), G.stage h.state + k < G.horizon →
      ∑ z : Suffix a k, ∑ jf, trajectoryProbability G π x h z jf = 1 := by
  intro k
  induction k with
  | zero =>
    intro h _
    simp [trajectoryProbability]
    rw [Finset.card_eq_one]
    refine ⟨h.state, ?_⟩
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · exact fun h' => h'.2
    · intro e; subst e; exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro h hk
    have := s226x_dec G π x h k (fun _ => 1)
    simp only [mul_one] at this
    rw [this]
    have hs : G.stage h.state + 1 < G.horizon := by omega
    have e : ∀ b : Fin (a h.state), (∑ j : Fin n, if G.stage j = G.stage h.state + 1 then
        (x h.state).1 b j * ∑ z' : Suffix a k, ∑ jf : Fin n,
          trajectoryProbability G π x (h.extend b j) z' jf else 0) = 1 := by
      intro b
      rw [← s226x_next (hx h.state) hs b]
      apply Finset.sum_congr rfl; intro j _
      split_ifs with hj
      · rw [ih (h.extend b j) (by show G.stage j + k < G.horizon; omega), mul_one]
      · rfl
    simp_rw [e, mul_one]
    exact (π h).2.2

lemma s226x_rfk (G : Setup n a) (π : Policy a) (x : Parameters n a) (h : History a) (k : ℕ)
    (hk : G.horizon - 1 - G.stage h.state = k) :
    returnFrom G π x h = ∑ z : Suffix a k, ∑ j : Fin n,
      trajectoryProbability G π x h z j * trajectoryReward G x z := by
  subst hk; rfl

lemma s226x_rew (G : Setup n a) (x : Parameters n a) (k : ℕ) (s : Fin n) (b : Fin (a s))
    (z' : Suffix a k) :
    trajectoryReward G x (Fin.cons ⟨s, b⟩ z' : Suffix a (k+1)) =
      (x s).2 b + G.discount * trajectoryReward G x z' := by
  unfold trajectoryReward
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  simp only [Fin.cons_zero, Fin.val_zero, pow_zero, one_mul, Fin.cons_succ, Fin.val_succ, pow_succ]
  congr 1
  apply Finset.sum_congr rfl; intro t _
  rw [show (Fin.cons ⟨s, b⟩ z' : Suffix a (k+1)) t.succ = z' t from Fin.cons_succ _ _ _]
  ring

lemma s226x_rec (G : Setup n a) (π : Policy a) (x : Parameters n a)
    (hx : ∀ s, ValidLocal G s (x s)) (h : History a) (hs : G.stage h.state + 1 < G.horizon) :
    returnFrom G π x h = ∑ b, (π h).val b * ((x h.state).2 b + G.discount *
      ∑ j, if G.stage j = G.stage h.state + 1 then
        (x h.state).1 b j * returnFrom G π x (h.extend b j) else 0) := by
  have hk : G.horizon - 1 - G.stage h.state = (G.horizon - 2 - G.stage h.state) + 1 := by omega
  rw [s226x_rfk G π x h _ hk, s226x_dec]
  apply Finset.sum_congr rfl; intro b _
  congr 1
  have e : ∀ j, (if G.stage j = G.stage h.state + 1 then (x h.state).1 b j *
      ∑ z' : Suffix a (G.horizon - 2 - G.stage h.state), ∑ jf : Fin n,
        trajectoryProbability G π x (h.extend b j) z' jf *
          trajectoryReward G x (Fin.cons ⟨h.state, b⟩ z') else 0) =
      (x h.state).2 b * (if G.stage j = G.stage h.state + 1 then (x h.state).1 b j else 0) +
      G.discount * (if G.stage j = G.stage h.state + 1 then
        (x h.state).1 b j * returnFrom G π x (h.extend b j) else 0) := by
    intro j
    split_ifs with hj
    · have hk' : G.horizon - 1 - G.stage (h.extend b j).state = G.horizon - 2 - G.stage h.state := by
        show G.horizon - 1 - G.stage j = _; omega
      rw [s226x_rfk G π x (h.extend b j) _ hk']
      simp_rw [s226x_rew, mul_add, Finset.sum_add_distrib]
      have htot := s226x_tot G π x hx (G.horizon - 2 - G.stage h.state) (h.extend b j)
        (by show G.stage j + _ < G.horizon; omega)
      have : ∑ z' : Suffix a (G.horizon - 2 - G.stage h.state), ∑ jf : Fin n,
          trajectoryProbability G π x (h.extend b j) z' jf * (x h.state).2 b = (x h.state).2 b := by
        simp_rw [← Finset.sum_mul]; rw [htot, one_mul]
      rw [this]
      have : ∑ z' : Suffix a (G.horizon - 2 - G.stage h.state), ∑ jf : Fin n,
          trajectoryProbability G π x (h.extend b j) z' jf * (G.discount * trajectoryReward G x z') =
          G.discount * ∑ z' : Suffix a (G.horizon - 2 - G.stage h.state), ∑ jf : Fin n,
            trajectoryProbability G π x (h.extend b j) z' jf * trajectoryReward G x z' := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro _ _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro _ _; ring
      rw [this]; ring
    · simp
  rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, s226x_next (hx h.state) hs b, mul_one]

end S226X3

section S226X4

lemma s226x_indep {n : ℕ} [NeZero n] {X : Fin n → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] (s : Fin n) (f : X s → ℝ)
    (g : (∀ i, X i) → ℝ) (hg : ∀ x y, g (Function.update x s y) = g x) :
    ∫ x, f (x s) * g x ∂(Measure.pi μ) = (∫ y, f y ∂μ s) * ∫ x, g x ∂(Measure.pi μ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.pos n; omega⟩
  have e := measurePreserving_piFinSuccAbove μ s
  have es := MeasurePreserving.symm _ e
  obtain ⟨y0⟩ := Measure.nonempty_of_neZero (μ s)
  have hg' : ∀ y w, g (Fin.insertNth s y w) = g (Fin.insertNth s y0 w) := by
    intro y w
    rw [← Fin.update_insertNth s y0 y w, hg]
  rw [← es.integral_comp', ← es.integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk,
    Fin.insertNth_apply_same, hg']
  rw [integral_prod_mul (fun y => f y) (fun w => g (Fin.insertNth s y0 w))]
  have := integral_prod_mul (μ := μ s) (ν := Measure.pi fun j => μ (s.succAbove j))
    (fun _ => (1:ℝ)) (fun w => g (Fin.insertNth s y0 w))
  simp only [one_mul, integral_const, probReal_univ, smul_eq_mul] at this
  rw [this]

end S226X4

section S226X5
variable {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]

lemma s226x_cont (G : Setup n a) (π : Policy a) (h : History a) :
    Continuous (fun x : Parameters n a => returnFrom G π x h) := by
  unfold returnFrom
  apply continuous_finset_sum; intro z _
  apply continuous_finset_sum; intro j _
  apply Continuous.mul
  · unfold trajectoryProbability
    split_ifs
    · fun_prop
    · exact continuous_const
  · unfold trajectoryReward; fun_prop

lemma s226x_upd (G : Setup n a) (π : Policy a) (x : Parameters n a) (h : History a)
    (s : Fin n) (hs : G.stage s < G.stage h.state) (y : Local n a s) :
    returnFrom G π (Function.update x s y) h = returnFrom G π x h := by
  unfold returnFrom
  apply Finset.sum_congr rfl; intro z _
  apply Finset.sum_congr rfl; intro j _
  unfold trajectoryProbability
  split_ifs with hc
  · have hne : ∀ t, (z t).1 ≠ s := by
      intro t ht; have := hc.1 t; rw [ht] at this; omega
    have hx : ∀ t, Function.update x s y (z t).1 = x (z t).1 := fun t =>
      Function.update_of_ne (hne t) _ _
    unfold trajectoryReward
    simp only [hx]
  · simp

variable {G : Setup n a} {U : Uncertainty G}

lemma s226x_aes (μ : Marginals n a) (hμ : admissibleMarginals U μ) (s : Fin n) :
    ∀ᵐ y ∂(μ s), y ∈ U.sets s (Fin.last U.layers) := by
  have hS : MeasurableSet (U.sets s (Fin.last U.layers)) :=
    (U.compact s _).isClosed.measurableSet
  haveI := (hμ s).1
  rw [ae_iff]
  exact (prob_compl_eq_zero_iff hS).2 (hμ s).2.1

lemma s226x_ae (μ : Marginals n a) (hμ : admissibleMarginals U μ) :
    ∀ᵐ x ∂(productLaw μ), ∀ s, x s ∈ U.sets s (Fin.last U.layers) := by
  haveI : ∀ s, IsProbabilityMeasure (μ s) := fun s => (hμ s).1
  rw [ae_all_iff]
  intro s
  exact (measurePreserving_eval μ s).quasiMeasurePreserving.ae (s226x_aes μ hμ s)

lemma s226x_intg (μ : Marginals n a) (hμ : admissibleMarginals U μ)
    {F : Parameters n a → ℝ} (hF : Continuous F) : Integrable F (productLaw μ) := by
  haveI : ∀ s, IsProbabilityMeasure (μ s) := fun s => (hμ s).1
  haveI : IsProbabilityMeasure (productLaw μ) := by unfold productLaw; infer_instance
  have hK : IsCompact (Set.univ.pi fun s => U.sets s (Fin.last U.layers)) :=
    isCompact_univ_pi fun s => U.compact s _
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine Integrable.of_bound hF.aestronglyMeasurable C ?_
  filter_upwards [s226x_ae μ hμ] with x hx
  exact hC x (fun s _ => hx s)

lemma s226x_intgs (μ : Marginals n a) (hμ : admissibleMarginals U μ) (s : Fin n)
    {E : Type*} [NormedAddCommGroup E] {F : Local n a s → E} (hF : Continuous F) :
    Integrable F (μ s) := by
  haveI := (hμ s).1
  obtain ⟨C, hC⟩ := (U.compact s (Fin.last U.layers)).exists_bound_of_continuousOn hF.continuousOn
  refine Integrable.of_bound hF.aestronglyMeasurable C ?_
  filter_upwards [s226x_aes μ hμ s] with y hy
  exact hC y hy

lemma s226x_lin {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ] (ν : Measure Ω)
    (c : ι → ℝ) (A : ι → Ω → ℝ) (D : ι → κ → Ω → ℝ) (p : κ → Prop) [DecidablePred p] (γ : ℝ)
    (hA : ∀ b, Integrable (A b) ν) (hD : ∀ b j, Integrable (D b j) ν) :
    ∫ x, ∑ b, c b * (A b x + γ * ∑ j, if p j then D b j x else 0) ∂ν =
      ∑ b, c b * ((∫ x, A b x ∂ν) + γ * ∑ j, if p j then ∫ x, D b j x ∂ν else 0) := by
  have hI : ∀ b j, Integrable (fun x => if p j then D b j x else 0) ν := by
    intro b j; split_ifs
    · exact hD b j
    · exact integrable_zero _ _ _
  have hS : ∀ b, Integrable (fun x => ∑ j, if p j then D b j x else 0) ν :=
    fun b => integrable_finset_sum _ (fun j _ => hI b j)
  rw [integral_finset_sum _ (fun b _ => (show Integrable
    (fun x => c b * (A b x + γ * ∑ j, if p j then D b j x else 0)) ν from
      ((hA b).add ((hS b).const_mul γ)).const_mul (c b)))]
  apply Finset.sum_congr rfl; intro b _
  rw [integral_const_mul, integral_add (hA b) ((hS b).const_mul γ), integral_const_mul,
    integral_finset_sum _ (fun j _ => hI b j)]
  congr 3
  apply Finset.sum_congr rfl; intro j _
  split_ifs
  · rfl
  · simp

end S226X5

theorem s226x_l31 {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]
    (G : Setup n a) (U : Uncertainty G) (π : Policy a)
    (μ : Marginals n a) (hμ : admissibleMarginals U μ)
    (h : History a) (ht : G.stage h.state + 1 < G.horizon) :
    expectedFrom G π (productLaw μ) h =
      ∫ x, averagedStep G π (productLaw μ) h x ∂(μ h.state) ∧
    (∫ x, averagedStep G π (productLaw μ) h x ∂(μ h.state)) =
      averagedStep G π (productLaw μ) h (globalMean (productLaw μ) h.state) := by
  haveI : ∀ s, IsProbabilityMeasure (μ s) := fun s => (hμ s).1
  have hvalid : ∀ᵐ x ∂(productLaw μ), ∀ s, ValidLocal G s (x s) := by
    filter_upwards [s226x_ae μ hμ] with x hx s
    exact U.valid s _ _ (hx s)
  have hstep : ∀ b j, G.stage j = G.stage h.state + 1 →
      ∫ x, (x h.state).1 b j * returnFrom G π x (h.extend b j) ∂(productLaw μ) =
        (∫ y, y.1 b j ∂(μ h.state)) * expectedFrom G π (productLaw μ) (h.extend b j) := by
    intro b j hj
    exact s226x_indep μ h.state (fun y => y.1 b j) (fun x => returnFrom G π x (h.extend b j))
      (fun x y => s226x_upd G π x (h.extend b j) h.state
        (by show G.stage h.state < G.stage j; omega) y)
  have hA : ∀ b, Integrable (fun x : Parameters n a => (x h.state).2 b) (productLaw μ) :=
    fun b => s226x_intg μ hμ (by fun_prop)
  have hD : ∀ b j, Integrable (fun x : Parameters n a =>
      (x h.state).1 b j * returnFrom G π x (h.extend b j)) (productLaw μ) :=
    fun b j => s226x_intg μ hμ
      ((by fun_prop : Continuous fun x : Parameters n a => (x h.state).1 b j).mul
        (s226x_cont G π _))
  have hA' : ∀ b, Integrable (fun y : Local n a h.state => y.2 b) (μ h.state) :=
    fun b => s226x_intgs μ hμ _ (by fun_prop)
  have hD' : ∀ b j, Integrable (fun y : Local n a h.state =>
      y.1 b j * expectedFrom G π (productLaw μ) (h.extend b j)) (μ h.state) :=
    fun b j => s226x_intgs μ hμ _ ((by fun_prop : Continuous fun y : Local n a h.state => y.1 b j).mul
      continuous_const)
  have L2 := s226x_lin (μ h.state) (fun b => (π h).val b) (fun b y => y.2 b)
    (fun b j y => y.1 b j * expectedFrom G π (productLaw μ) (h.extend b j))
    (fun j => G.stage j = G.stage h.state + 1) G.discount hA' hD'
  beta_reduce at L2
  constructor
  · unfold expectedFrom
    rw [integral_congr_ae (hvalid.mono fun x hx => s226x_rec G π x hx h ht)]
    have L1 := s226x_lin (productLaw μ) (fun b => (π h).val b) (fun b x => (x h.state).2 b)
      (fun b j x => (x h.state).1 b j * returnFrom G π x (h.extend b j))
      (fun j => G.stage j = G.stage h.state + 1) G.discount hA hD
    beta_reduce at L1
    unfold averagedStep
    rw [L1, L2]
    apply Finset.sum_congr rfl; intro b _
    congr 2
    · exact integral_comp_eval (f := fun y : Local n a h.state => y.2 b)
        (by fun_prop : Continuous fun y : Local n a h.state => y.2 b).aestronglyMeasurable
    · congr 1; apply Finset.sum_congr rfl; intro j _
      split_ifs with hj
      · rw [hstep b j hj, integral_mul_const]
      · rfl
  · have hid : Integrable (fun y : Local n a h.state => y) (μ h.state) :=
      s226x_intgs μ hμ _ continuous_id
    have hm : globalMean (productLaw μ) h.state = ∫ y, y ∂(μ h.state) := by
      show ∫ x, x h.state ∂(Measure.pi μ) = _
      exact integral_comp_eval (f := fun y : Local n a h.state => y) aestronglyMeasurable_id
    unfold averagedStep
    rw [L2, hm]
    apply Finset.sum_congr rfl; intro b _
    congr 2
    · exact ((ContinuousLinearMap.proj b).comp
        (ContinuousLinearMap.snd ℝ (Fin (a h.state) → Fin n → ℝ) (Fin (a h.state) → ℝ))).integral_comp_comm hid
    · congr 1; apply Finset.sum_congr rfl; intro j _
      split_ifs with hj
      · rw [integral_mul_const]
        congr 1
        exact ((ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.proj b).comp
          (ContinuousLinearMap.fst ℝ (Fin (a h.state) → Fin n → ℝ) (Fin (a h.state) → ℝ)))).integral_comp_comm hid
      · rfl

theorem solution {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]
    (G : Setup n a) (U : Uncertainty G) (π : Policy a)
    (ν : Measure (Parameters n a)) (hν : ν ∈ globalClass U) :
    performance G π ν = totalReturn G π (globalMean ν) := by
  obtain ⟨μ, hμ, rfl⟩ := hν
  haveI : ∀ s, IsProbabilityMeasure (μ s) := fun s => (hμ s).1
  have hmv : ∀ s, ValidLocal G s ((globalMean (productLaw μ)) s) := by
    intro s
    apply U.valid s (Fin.last U.layers)
    show ∫ x, x s ∂(Measure.pi μ) ∈ _
    rw [integral_comp_eval (f := fun y : Local n a s => y) aestronglyMeasurable_id]
    exact (U.convex s _).integral_mem (U.compact s _).isClosed (s226x_aes μ hμ s)
      (s226x_intgs μ hμ s continuous_id)
  have key : ∀ d (h : History a), G.horizon - 1 - G.stage h.state = d →
      expectedFrom G π (productLaw μ) h = returnFrom G π (globalMean (productLaw μ)) h := by
    intro d
    induction d with
    | zero =>
      intro h hd
      have h0 : ∀ x, returnFrom G π x h = 0 := fun x => by
        rw [s226x_rfk G π x h 0 hd]; simp [trajectoryReward]
      unfold expectedFrom; simp [h0]
    | succ d ih =>
      intro h hd
      have ht : G.stage h.state + 1 < G.horizon := by have := G.stage_lt h.state; omega
      obtain ⟨e1, e2⟩ := s226x_l31 G U π μ hμ h ht
      rw [e1, e2, s226x_rec G π (globalMean (productLaw μ)) hmv h ht]
      unfold averagedStep
      have hE : ∀ b j, (if G.stage j = G.stage h.state + 1 then
          ((globalMean (productLaw μ)) h.state).1 b j * expectedFrom G π (productLaw μ) (h.extend b j) else 0) =
          (if G.stage j = G.stage h.state + 1 then
          ((globalMean (productLaw μ)) h.state).1 b j * returnFrom G π (globalMean (productLaw μ)) (h.extend b j) else 0) := by
        intro b j
        split_ifs with hj
        · rw [ih (h.extend b j) (by show G.horizon - 1 - G.stage j = d; omega)]
        · rfl
      simp_rw [hE]
  exact key _ (initialHistory G) rfl
