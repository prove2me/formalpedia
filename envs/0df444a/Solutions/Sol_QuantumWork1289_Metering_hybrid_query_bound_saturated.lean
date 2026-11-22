-- Prove2me | solution 1 for QuantumWork1289.Metering.hybrid_query_bound_saturated
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:47:15.052179+00:00
-- url     : https://prove2.me/submissions/1844a26b-e155-451f-8a6a-ddac9fdd74fc

import Mathlib
import Definitions.Def_QuantumWork1289_Metering_oracleExperiment
import Definitions.Def_QuantumWork1289_Metering_listRecovery

set_option autoImplicit false
open QuantumWork1289.Metering
open scoped Matrix ComplexOrder ENNReal

private def answerShift {X B : Type} [AddCommGroup B] {n : ℕ}
    (w : QueryWire X B n) (f : X → B) :
    Equiv.Perm ((Fin w.addresses × B) × Fin w.workspace) where
  toFun x := ((x.1.1, x.1.2 + f (w.address x.1.1)), x.2)
  invFun x := ((x.1.1, x.1.2 - f (w.address x.1.1)), x.2)
  left_inv x := by simp
  right_inv x := by simp

private theorem query_star_mul {X B : Type} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {n : ℕ} (w : QueryWire X B n) (f : X → B) :
    (queryMatrix w f)ᴴ * queryMatrix w f = 1 := by
  let e : Equiv.Perm (Fin n) := w.split.trans ((answerShift w f).trans w.split.symm)
  have hperm : queryMatrix w f = Equiv.Perm.permMatrix ℂ (e.symm : Equiv.Perm (Fin n)) := by
    ext p q
    have he : e.symm p = q ↔
        (w.split p).1.1 = (w.split q).1.1 ∧
        (w.split p).1.2 = (w.split q).1.2 + f (w.address (w.split q).1.1) ∧
        (w.split p).2 = (w.split q).2 := by
      rw [Equiv.symm_apply_eq]
      change p = e q ↔ _
      rw [← w.split.apply_eq_iff_eq]
      rcases w.split p with ⟨⟨_, _⟩, _⟩
      simp only [e, Equiv.trans_apply, Equiv.apply_symm_apply, answerShift, Equiv.coe_fn_mk,
        Prod.mk.injEq]
      tauto
    simp only [queryMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply, QAlgorithms.xorOracle, Matrix.of_apply,
      Function.comp_apply, Matrix.one_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply]
    split_ifs <;> simp_all
  rw [hperm, Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

private theorem instrumentBranch_positive {n b : ℕ}
    (M : QAlgorithms.CopyMeasurements.QuantumInstrument (Fin n) (Fin b))
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef) (j : Fin b) :
    (QAlgorithms.CopyMeasurements.instrumentBranch M j ρ).PosSemidef := by
  unfold QAlgorithms.CopyMeasurements.instrumentBranch QAlgorithms.krausApply
  exact Matrix.posSemidef_sum _ fun i _ => hρ.mul_mul_conjTranspose_same _

private theorem instrument_trace_sum {n b : ℕ}
    (M : QAlgorithms.CopyMeasurements.QuantumInstrument (Fin n) (Fin b))
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    ∑ j, Matrix.trace (QAlgorithms.CopyMeasurements.instrumentBranch M j ρ) = Matrix.trace ρ := by
  unfold QAlgorithms.CopyMeasurements.instrumentBranch QAlgorithms.krausApply
  simp only [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (M.kraus _ _)]
  simp_rw [← Matrix.trace_sum, ← Matrix.sum_mul]
  rw [M.complete, one_mul]

private theorem execute_psd {X B O S : Type} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {n : ℕ} (A : HybridMachine X B O S n) (f : X → B) (t : ℕ) (s : S)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef) :
    ∀ z ∈ execute A f t s ρ, z.state.PosSemidef := by
  induction t generalizing s ρ with
  | zero => simp [execute, hρ]
  | succ t ih =>
    unfold execute
    cases h : A.step s with
    | halt o => simp [hρ]
    | privateOp b M next =>
      intro z hz
      obtain ⟨ys, hys, hzys⟩ := List.mem_flatten.mp hz
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hys
      exact ih _ _ (instrumentBranch_positive M ρ hρ j) z hzys
    | classicalRead x next =>
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact ih _ _ hρ y hy
    | coherentCall w next =>
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact ih _ _ (hρ.mul_mul_conjTranspose_same _) y hy

private theorem execute_trace {X B O S : Type} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {n : ℕ} (A : HybridMachine X B O S n) (f : X → B) (t : ℕ) (s : S)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    ((execute A f t s ρ).map (Matrix.trace ∘ Terminal.state)).sum = Matrix.trace ρ := by
  induction t generalizing s ρ with
  | zero => simp [execute]
  | succ t ih =>
    unfold execute
    cases h : A.step s with
    | halt o => simp
    | privateOp b M next =>
      simp only [List.map_flatten, List.map_ofFn, List.sum_flatten, List.sum_ofFn, Function.comp_apply]
      simp_rw [ih]
      exact instrument_trace_sum M ρ
    | classicalRead x next =>
      simpa [List.map_map, Function.comp_def] using ih (next (f x)) ρ
    | coherentCall w next =>
      rw [List.map_map]
      change ((execute A f t next (queryMatrix w f * ρ * (queryMatrix w f)ᴴ)).map
        (Matrix.trace ∘ Terminal.state)).sum = Matrix.trace ρ
      rw [ih, Matrix.trace_mul_cycle (queryMatrix w f), query_star_mul, one_mul]

private theorem trace_re_nonneg {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.PosSemidef) :
    0 ≤ (Matrix.trace ρ).re := by
  rw [Matrix.trace, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => (Complex.nonneg_iff.mp (hρ.diag_nonneg (i := i))).1

private theorem total_trace_re_nonneg {O : Type} {n : ℕ} (ts : List (Terminal O n))
    (hts : ∀ z ∈ ts, z.state.PosSemidef) :
    0 ≤ ((ts.map (Matrix.trace ∘ Terminal.state)).sum).re := by
  induction ts with
  | nil => simp
  | cons z ts ih =>
    simp only [List.map_cons, List.sum_cons, Complex.add_re, Function.comp_apply]
    exact add_nonneg (trace_re_nonneg (hts z (by simp)))
      (ih (fun y hy => hts y (List.mem_cons_of_mem z hy)))

private theorem ofReal_map_sum {O : Type} {n : ℕ} (ts : List (Terminal O n))
    (hts : ∀ z ∈ ts, z.state.PosSemidef) :
    (ts.map branchMass).sum = ENNReal.ofReal (((ts.map (Matrix.trace ∘ Terminal.state)).sum).re) := by
  induction ts with
  | nil => simp
  | cons z ts ih =>
    have hz := trace_re_nonneg (hts z (by simp))
    have ht : ∀ y ∈ ts, y.state.PosSemidef := fun y hy => hts y (List.mem_cons_of_mem z hy)
    simp only [List.map_cons, List.sum_cons, Complex.add_re, Function.comp_apply]
    rw [ih ht, ENNReal.ofReal_add hz]
    · rfl
    · exact total_trace_re_nonneg ts ht

open Classical in
private theorem accepted_le_total {X B O : Type} {n : ℕ}
    (f : X → B) (accept : (X → B) → O → Prop) (ts : List (Terminal O n)) :
    (ts.map (fun z => match z.output with
      | none => 0
      | some o => if accept f o then branchMass z else 0)).sum ≤ (ts.map branchMass).sum := by
  classical
  induction ts with
  | nil => simp
  | cons z ts ih =>
    simp only [List.map_cons, List.sum_cons]
    apply add_le_add _ ih
    cases hz : z.output with
    | none => simp [hz]
    | some o =>
      by_cases ha : accept f o <;> simp [hz, ha]

private theorem normalized {X B O S : Type} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {n : ℕ} (A : HybridMachine X B O S n) (ρ : InitialState n)
    (accept : (X → B) → O → Prop) (t : ℕ) (f : X → B) :
    ((execute A f t A.initial ρ.matrix).map branchMass).sum = 1 ∧
      acceptedMass A ρ accept t f ≤ 1 := by
  have h := ofReal_map_sum _ (execute_psd A f t A.initial _ ρ.positive)
  rw [execute_trace, ρ.normalized] at h
  have htotal : ((execute A f t A.initial ρ.matrix).map branchMass).sum = 1 := by simpa using h
  exact ⟨htotal, (accepted_le_total f accept _).trans_eq htotal⟩

open MeasureTheory

private theorem success_le_one {X B O Ω S : Type} [Fintype B] [Nonempty B] [DecidableEq B]
    [AddCommGroup B] [MeasurableSpace B] [MeasurableSpace Ω] {n : ℕ}
    (A : SeededMachine X B O Ω S n) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (accept : (X → B) → O → Prop) : successProbability A μ accept ≤ 1 := by
  haveI : IsProbabilityMeasure (oracleLaw X B) := by unfold oracleLaw; infer_instance
  apply iSup_le
  intro t
  calc
    _ ≤ ∫⁻ _ : Ω × (X → B), (1 : ℝ≥0∞) ∂μ.prod (oracleLaw X B) :=
      lintegral_mono fun p => (normalized (A.machine p.1) (A.initialState p.1) accept t p.2).2
    _ = 1 := by simp

private theorem beta_saturated (m Q : ℕ) (h : m ≤ Q) : beta m Q = 1 := by
  rw [beta, min_eq_right h]
  have hs : (∑ j ∈ Finset.range (m+1), (m.choose j : ℝ)) = (2 : ℝ)^m := by
    exact_mod_cast Nat.sum_range_choose m
  rw [hs, zpow_neg, zpow_natCast]
  exact inv_mul_cancel₀ (by positivity)

theorem solution {E Γ Ω S : Type} [Fintype E] [MeasurableSpace Ω]
    {N n C Q : ℕ} (code : Set (Fin N → Γ)) (ζ ℓ L : ℝ)
    (hcode : ListRecoverable code ζ ℓ L) (hclassical : (C : ℝ) + 1 ≤ ℓ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : SeededMachine (E × Fin N × Γ) Bool (Option (E × (Fin N → Γ))) Ω S n)
    (hlarge : unread ζ N ≤ Q) :
    successProbability A μ (yzAccept code) ≤
      ENNReal.ofReal (((C : ℝ) + 1) * L * beta (unread ζ N) Q) := by
  classical
  rcases Set.eq_empty_or_nonempty code with rfl | ⟨w, hw⟩
  · have hfalse (f : E × Fin N × Γ → Bool) (o : Option (E × (Fin N → Γ))) :
        ¬ yzAccept (∅ : Set (Fin N → Γ)) f o := by cases o <;> simp [yzAccept]
    have hz (ω : Ω) (t : ℕ) (f : E × Fin N × Γ → Bool) :
        acceptedMass (A.machine ω) (A.initialState ω) (yzAccept ∅) t f = 0 := by
      unfold acceptedMass
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
      cases h : z.output <;> simp [h, hfalse]
    simp [successProbability, hz]
  · have hone : (1 : ℝ) ≤ ℓ := by linarith [Nat.cast_nonneg (α := ℝ) C]
    have hsingle (i : Fin N) : HasAtMost ({w i} : Set Γ) ℓ := by
      intro t ht
      have hc : t.card ≤ ({w i} : Finset Γ).card :=
        Finset.card_le_card (fun x hx => Finset.mem_singleton.mpr (ht hx))
      simpa using (le_trans (by exact_mod_cast hc : (t.card : ℝ) ≤ (({w i} : Finset Γ).card : ℝ)) (by simpa using hone))
    have hlist := hcode.2.2 (fun i => {w i}) hsingle ({w} : Finset (Fin N → Γ))
    have hL : (1 : ℝ) ≤ L := by
      apply (by simpa only [Finset.card_singleton, Nat.cast_one] using hlist : _ → 1 ≤ L)
      intro x hx
      have hxw : x = w := Finset.mem_singleton.mp hx
      subst x
      refine ⟨hw, ?_⟩
      simp
      nlinarith [mul_nonneg hcode.1.le (Nat.cast_nonneg (α := ℝ) N)]
    have hb : 1 ≤ ((C : ℝ) + 1) * L := by
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) C) (zero_le_one.trans hL)]
    rw [beta_saturated _ _ hlarge, mul_one]
    exact (success_le_one A μ _).trans (by simpa using ENNReal.ofReal_le_ofReal hb)

#print axioms solution
