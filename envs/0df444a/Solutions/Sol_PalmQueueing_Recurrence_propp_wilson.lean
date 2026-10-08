-- Prove2me | solution 1 for PalmQueueing.Recurrence.propp_wilson
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:54:17.527975+00:00
-- url     : https://prove2.me/submissions/063b89cc-c05e-4a96-b2f5-d14ef581f637

import Mathlib
import Definitions.Def_PalmQueueing_Recurrence_ExactSampling

/-!
# Theorem 2.5.1: the Propp-Wilson coupling-from-the-past theorem (§2.5.3, p.112)
-/


namespace PalmQueueing.Recurrence

open MeasureTheory Filter Topology ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

section CFTPBasic

variable {r : ℕ}

/-- pure iteration of the updating function along an array word indexed by time and state -/
def iterA (h : Fin r → ℝ → Fin r) : (n : ℕ) → Fin r → (Fin n × Fin r → ℝ) → Fin r
  | 0, i, _ => i
  | n + 1, i, v =>
      h (iterA h n i (fun p => v (p.1.castSucc, p.2)))
        (v (Fin.last n, iterA h n i (fun p => v (p.1.castSucc, p.2))))

lemma measurable_iterA (h : Fin r → ℝ → Fin r) (hh : ∀ i, Measurable (h i)) (n : ℕ)
    (i : Fin r) : Measurable (iterA h n i) := by
  induction n generalizing i with
  | zero => exact measurable_const
  | succ n ih =>
    have hg : Measurable (fun v : Fin (n + 1) × Fin r → ℝ =>
        iterA h n i (fun p => v (p.1.castSucc, p.2))) :=
      (ih i).comp (measurable_pi_lambda _ fun p => measurable_pi_apply _)
    have hh' : Measurable (fun q : Fin r × (Fin (n + 1) × Fin r → ℝ) =>
        h q.1 (q.2 (Fin.last n, q.1))) :=
      measurable_from_prod_countable_right fun x =>
        (hh x).comp (measurable_pi_apply (Fin.last n, x))
    exact hh'.comp (hg.prodMk measurable_id)

variable (C : CFTP Ω r)

lemma X_eq_iterA (k : ℤ) (n : ℕ) (i : Fin r) (ω : Ω) :
    C.X k n i ω = iterA C.h n i (fun p : Fin n × Fin r => C.xi (k + ((p.1 : ℕ) : ℤ)) p.2 ω) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [CFTP.X, iterA]
    rw [ih]
    simp [Fin.val_last]

lemma X_succ (k : ℤ) (n : ℕ) (i : Fin r) (ω : Ω) :
    C.X k (n + 1) i ω = C.h (C.X k n i ω) (C.xi (k + n) (C.X k n i ω) ω) := rfl

lemma X_comp (k : ℤ) (n m : ℕ) (i : Fin r) (ω : Ω) :
    C.X k (n + m) i ω = C.X (k + n) m (C.X k n i ω) ω := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show n + (m + 1) = (n + m) + 1 by ring, X_succ, X_succ, ih]
    congr 2
    push_cast
    ring

lemma law_block (k : ℤ) (n : ℕ) :
    Measure.map (fun ω (p : Fin n × Fin r) => C.xi (k + ((p.1 : ℕ) : ℤ)) p.2 ω) C.P
      = Measure.pi (fun _ : Fin n × Fin r => (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) := by
  haveI := C.isProb
  have hind : iIndepFun (fun p : Fin n × Fin r => C.xi (k + ((p.1 : ℕ) : ℤ)) p.2) C.P := by
    have hinj : Function.Injective (fun p : Fin n × Fin r => (k + ((p.1 : ℕ) : ℤ), p.2)) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      have := add_left_cancel hab.1
      exact Prod.ext (Fin.ext (by exact_mod_cast this)) hab.2
    exact C.indep_xi.precomp hinj
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun p => (C.measurable_xi _ _).aemeasurable)] at hind
  rw [hind]
  congr 1
  funext p
  exact C.unif_xi _ _

lemma measurable_block (k : ℤ) (n : ℕ) :
    Measurable (fun ω (p : Fin n × Fin r) => C.xi (k + ((p.1 : ℕ) : ℤ)) p.2 ω) :=
  measurable_pi_lambda _ fun p => C.measurable_xi _ _

lemma prob_block_invariant (k k' : ℤ) (n : ℕ) {S : Set (Fin n × Fin r → ℝ)}
    (hS : MeasurableSet S) :
    C.P ((fun ω (p : Fin n × Fin r) => C.xi (k + ((p.1 : ℕ) : ℤ)) p.2 ω) ⁻¹' S)
      = C.P ((fun ω (p : Fin n × Fin r) => C.xi (k' + ((p.1 : ℕ) : ℤ)) p.2 ω) ⁻¹' S) := by
  rw [← Measure.map_apply (measurable_block C k n) hS,
    ← Measure.map_apply (measurable_block C k' n) hS, law_block C, law_block C]

lemma set_X_eq (k : ℤ) (n : ℕ) (i j : Fin r) :
    {ω | C.X k n i ω = j} =
      (fun ω (p : Fin n × Fin r) => C.xi (k + ((p.1 : ℕ) : ℤ)) p.2 ω) ⁻¹'
        (iterA C.h n i ⁻¹' {j}) := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, X_eq_iterA]

lemma measurableSet_X_eq (k : ℤ) (n : ℕ) (i j : Fin r) :
    MeasurableSet {ω | C.X k n i ω = j} := by
  rw [set_X_eq]
  exact measurable_block C k n
    ((measurable_iterA C.h C.measurable_h n i) (measurableSet_singleton j))

lemma prob_X_eq_invariant (k k' : ℤ) (n : ℕ) (i j : Fin r) :
    C.P {ω | C.X k n i ω = j} = C.P {ω | C.X k' n i ω = j} := by
  rw [set_X_eq, set_X_eq]
  exact prob_block_invariant C k k' n
    ((measurable_iterA C.h C.measurable_h n i) (measurableSet_singleton j))

lemma measurableSet_coalesced (n : ℕ) : MeasurableSet {ω | C.Coalesced n ω} := by
  have : {ω | C.Coalesced n ω} =
      ⋂ i, ⋂ j, ⋃ x, {ω | C.X (-(n : ℤ)) n i ω = x} ∩ {ω | C.X (-(n : ℤ)) n j ω = x} := by
    ext ω
    simp only [CFTP.Coalesced, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion,
      Set.mem_inter_iff]
    constructor
    · intro h i j; exact ⟨_, rfl, (h i j).symm⟩
    · intro h i j; obtain ⟨x, h1, h2⟩ := h i j; rw [h1, h2]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iUnion fun x =>
    (measurableSet_X_eq C _ n i x).inter (measurableSet_X_eq C _ n j x)

lemma coalesced_mono (n : ℕ) (ω : Ω) (h : C.Coalesced n ω) : C.Coalesced (n + 1) ω := by
  intro i j
  have e : ∀ a : Fin r, C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) a ω =
      C.X (-(n : ℤ)) n (C.X (-((n + 1 : ℕ) : ℤ)) 1 a ω) ω := by
    intro a
    rw [show n + 1 = 1 + n by ring, X_comp]
    congr 2
    push_cast
    ring
  rw [e i, e j]
  exact h _ _

end CFTPBasic

section CFTPMarkov

variable {r : ℕ} (C : CFTP Ω r)

lemma row_sum_one (i : Fin r) : ∑ j, ENNReal.ofReal (C.IP i j) = 1 := by
  haveI := C.isProb
  have huniv : (⋃ j : Fin r, {ω | C.h i (C.xi 0 i ω) = j}) = Set.univ := by
    ext ω; simp
  have hmeas : ∀ j, MeasurableSet {ω | C.h i (C.xi 0 i ω) = j} := fun j =>
    ((C.measurable_h i).comp (C.measurable_xi 0 i)) (measurableSet_singleton j)
  have hdisj : Pairwise (Function.onFun Disjoint fun j : Fin r => {ω | C.h i (C.xi 0 i ω) = j}) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    intro ω ha hb
    exact hab (ha.symm.trans hb)
  have := measure_iUnion (μ := C.P) hdisj hmeas
  rw [huniv, measure_univ, tsum_fintype] at this
  simp_rw [C.implements] at this
  exact this.symm

lemma ofReal_eq_ofReal_max' (x : ℝ) : ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
  rcases le_or_gt 0 x with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h.le, ENNReal.ofReal_of_nonpos h.le, ENNReal.ofReal_zero]

lemma row_max_sum_one (i : Fin r) : ∑ j, max (C.IP i j) 0 = 1 := by
  have h := row_sum_one C i
  have : ∑ j, ENNReal.ofReal (C.IP i j) = ENNReal.ofReal (∑ j, max (C.IP i j) 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => le_max_right _ _)]
    congr 1
    funext j
    exact ofReal_eq_ofReal_max' _
  rw [this] at h
  have h1 : (0:ℝ) ≤ ∑ j, max (C.IP i j) 0 := Finset.sum_nonneg (fun j _ => le_max_right _ _)
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_eq_ofReal_iff h1 zero_le_one] at h
  exact h

lemma IP_nonneg_and_pi_pos : (∀ i j, 0 ≤ C.IP i j) ∧ (∀ j, 0 < C.pi j) := by
  classical
  have hsum_le : ∀ i, ∑ j, C.IP i j ≤ 1 := by
    intro i
    rw [← row_max_sum_one C i]
    exact Finset.sum_le_sum fun j _ => le_max_left _ _
  have hπsum : ∑ i, C.pi i * ∑ j, C.IP i j = 1 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [C.pi_stationary]
    exact C.pi_sum
  have hterms : ∀ i, C.pi i * (1 - ∑ j, C.IP i j) = 0 := by
    have hz : ∑ i, C.pi i * (1 - ∑ j, C.IP i j) = 0 := by
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib, hπsum, C.pi_sum, sub_self]
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin r)), 0 ≤ C.pi i * (1 - ∑ j, C.IP i j) :=
      fun i _ => mul_nonneg (C.pi_nonneg i) (sub_nonneg.mpr (hsum_le i))
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz i (Finset.mem_univ i)
  have hrow_nonneg : ∀ i, 0 < C.pi i → ∀ j, 0 ≤ C.IP i j := by
    intro i hi j
    have h1 : 1 - ∑ j, C.IP i j = 0 := by
      rcases mul_eq_zero.mp (hterms i) with h | h
      · exact absurd h hi.ne'
      · exact h
    have h2 : ∑ j, (max (C.IP i j) 0 - C.IP i j) = 0 := by
      rw [Finset.sum_sub_distrib, row_max_sum_one C i]
      linarith
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin r)), 0 ≤ max (C.IP i j) 0 - C.IP i j :=
      fun j _ => sub_nonneg.mpr (le_max_left _ _)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h2 j (Finset.mem_univ j)
    have hmax : max (C.IP i j) 0 = C.IP i j := by linarith
    rw [max_eq_left_iff] at hmax
    exact hmax
  have hzero : ∀ i, 0 < C.pi i → ∀ j, C.pi j = 0 → C.IP i j = 0 := by
    intro i hi j hj
    have hs : ∑ x, C.pi x * C.IP x j = 0 := by rw [C.pi_stationary, hj]
    have hnn : ∀ x ∈ (Finset.univ : Finset (Fin r)), 0 ≤ C.pi x * C.IP x j := by
      intro x _
      rcases (C.pi_nonneg x).lt_or_eq with hx | hx
      · exact mul_nonneg hx.le (hrow_nonneg x hx j)
      · rw [← hx, zero_mul]
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hs i (Finset.mem_univ i)
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hi.ne'
    · exact h
  have hpow : ∀ n : ℕ, ∀ i, 0 < C.pi i → ∀ j, C.pi j = 0 → (C.IP ^ n) i j = 0 := by
    intro n
    induction n with
    | zero =>
      intro i hi j hj
      rw [pow_zero, Matrix.one_apply_ne]
      rintro rfl
      exact hi.ne' hj
    | succ n ih =>
      intro i hi j hj
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro x _
      rcases (C.pi_nonneg x).lt_or_eq with hx | hx
      · rw [hzero x hx j hj, mul_zero]
      · rw [ih i hi x hx.symm, zero_mul]
  have hpos : ∀ j, 0 < C.pi j := by
    intro j
    by_contra hj
    have hj0 : C.pi j = 0 := le_antisymm (not_lt.mp hj) (C.pi_nonneg j)
    obtain ⟨i, hi⟩ : ∃ i, 0 < C.pi i := by
      by_contra hall
      push Not at hall
      have : ∑ i, C.pi i = 0 :=
        Finset.sum_eq_zero fun i _ => le_antisymm (hall i) (C.pi_nonneg i)
      rw [C.pi_sum] at this
      exact one_ne_zero this
    obtain ⟨n, hn⟩ := C.irreducible i j
    rw [hpow n i hi j hj0] at hn
    exact lt_irrefl _ hn
  exact ⟨fun i j => hrow_nonneg i (hpos i) j, hpos⟩

lemma IP_nonneg (i j : Fin r) : 0 ≤ C.IP i j := (IP_nonneg_and_pi_pos C).1 i j

lemma pi_pos (j : Fin r) : 0 < C.pi j := (IP_nonneg_and_pi_pos C).2 j

lemma IPpow_nonneg (n : ℕ) (i j : Fin r) : 0 ≤ (C.IP ^ n) i j := by
  induction n generalizing i j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (ih i x) (IP_nonneg C x j)

/-- the index block `{0, …, n-1} × E` -/
noncomputable def blkA (n : ℕ) : Finset (ℤ × Fin r) := (Finset.Ico 0 (n : ℤ)) ×ˢ Finset.univ

lemma mem_blkA (n : ℕ) (p : Fin n × Fin r) : (((p.1 : ℕ) : ℤ), p.2) ∈ blkA (r := r) n := by
  simp only [blkA, Finset.mem_product, Finset.mem_Ico, Finset.mem_univ, and_true]
  omega

noncomputable def restrA (n : ℕ) (w : ↥(blkA (r := r) n) → ℝ) : Fin n × Fin r → ℝ :=
  fun p => w ⟨(((p.1 : ℕ) : ℤ), p.2), mem_blkA n p⟩

lemma measurable_restrA (n : ℕ) : Measurable (restrA (r := r) n) :=
  measurable_pi_lambda _ fun p => measurable_pi_apply _

lemma X_zero_eq (n : ℕ) (i : Fin r) (ω : Ω) :
    C.X 0 n i ω = iterA C.h n i (restrA n (fun q : ↥(blkA (r := r) n) => C.xi q.1.1 q.1.2 ω)) := by
  rw [X_eq_iterA]
  simp only [zero_add]
  rfl

/-- the index block `{n} × E` -/
noncomputable def sngA (n : ℕ) : Finset (ℤ × Fin r) := {(n : ℤ)} ×ˢ Finset.univ

lemma mem_sngA (n : ℕ) (x : Fin r) : ((n : ℤ), x) ∈ sngA (r := r) n := by
  simp [sngA]

lemma blkA_disjoint (n : ℕ) : Disjoint (blkA (r := r) n) (sngA n) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  simp only [blkA, sngA, Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton] at hp hq
  omega

lemma markov (n : ℕ) (i j : Fin r) :
    C.P {ω | C.X 0 n i ω = j} = ENNReal.ofReal ((C.IP ^ n) i j) := by
  classical
  haveI := C.isProb
  induction n generalizing j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [CFTP.X]
    · simp [CFTP.X, hij]
  | succ n ih =>
    have hunion : {ω | C.X 0 (n + 1) i ω = j} =
        ⋃ x : Fin r, {ω | C.X 0 n i ω = x} ∩ {ω | C.h x (C.xi n x ω) = j} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, X_succ, zero_add]
      constructor
      · intro h; exact ⟨_, rfl, h⟩
      · rintro ⟨x, h1, h2⟩; rw [h1]; exact h2
    have hmeasB : ∀ x : Fin r, MeasurableSet {ω | C.h x (C.xi n x ω) = j} := fun x =>
      ((C.measurable_h x).comp (C.measurable_xi n x)) (measurableSet_singleton j)
    have hdisj : Pairwise (Function.onFun Disjoint fun x : Fin r =>
        {ω | C.X 0 n i ω = x} ∩ {ω | C.h x (C.xi n x ω) = j}) := by
      intro a b hab
      rw [Function.onFun, Set.disjoint_left]
      intro ω ha hb
      exact hab (ha.1.symm.trans hb.1)
    rw [hunion, measure_iUnion hdisj (fun x => (measurableSet_X_eq C 0 n i x).inter (hmeasB x)),
      tsum_fintype]
    have hind := C.indep_xi.indepFun_finset (blkA n) (sngA n) (blkA_disjoint n)
      (fun p => C.measurable_xi p.1 p.2)
    have hterm : ∀ x : Fin r,
        C.P ({ω | C.X 0 n i ω = x} ∩ {ω | C.h x (C.xi n x ω) = j})
          = C.P {ω | C.X 0 n i ω = x} * C.P {ω | C.h x (C.xi n x ω) = j} := by
      intro x
      have hA : {ω | C.X 0 n i ω = x} =
          (fun ω (q : ↥(blkA (r := r) n)) => C.xi q.1.1 q.1.2 ω) ⁻¹'
            ((iterA C.h n i ∘ restrA n) ⁻¹' {x}) := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Function.comp, Set.mem_singleton_iff,
          X_zero_eq]
      have hB : {ω | C.h x (C.xi n x ω) = j} =
          (fun ω (q : ↥(sngA (r := r) n)) => C.xi q.1.1 q.1.2 ω) ⁻¹'
            ((fun w : ↥(sngA (r := r) n) → ℝ => C.h x (w ⟨((n : ℤ), x), mem_sngA n x⟩))
              ⁻¹' {j}) := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      rw [hA, hB]
      apply hind.measure_inter_preimage_eq_mul
      · exact ((measurable_iterA C.h C.measurable_h n i).comp (measurable_restrA n))
          (measurableSet_singleton x)
      · exact ((C.measurable_h x).comp (measurable_pi_apply _)) (measurableSet_singleton j)
    simp_rw [hterm, ih, C.implements]
    rw [pow_succ, Matrix.mul_apply,
      ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (IPpow_nonneg C n i x) (IP_nonneg C x j))]
    congr 1
    funext x
    rw [ENNReal.ofReal_mul (IPpow_nonneg C n i x)]

end CFTPMarkov

section CFTPCoal

variable {r : ℕ} (C : CFTP Ω r)

lemma exists_n0 (j : Fin r) : ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ x, 0 < (C.IP ^ n0) x j := by
  have h1 : ∀ x, ∀ᶠ n in atTop, 0 < (C.IP ^ n) x j := fun x =>
    (C.ergodic x j).eventually (lt_mem_nhds (pi_pos C j))
  obtain ⟨n0, hn0⟩ := ((eventually_ge_atTop 1).and (Filter.eventually_all.mpr h1)).exists
  exact ⟨n0, hn0.1, hn0.2⟩

lemma exists_pos_entry (x : Fin r) : ∃ y, 0 < C.IP x y := by
  by_contra h
  push Not at h
  have h1 := row_max_sum_one C x
  have h2 : ∑ y, max (C.IP x y) 0 = 0 := Finset.sum_eq_zero fun y _ => max_eq_right (h y)
  rw [h2] at h1
  exact zero_ne_one h1

noncomputable def nextF (n0 : ℕ) (j : Fin r) (s : ℕ) (x : Fin r) : Fin r :=
  if h : ∃ y, 0 < C.IP x y ∧ 0 < (C.IP ^ (n0 - s - 1)) y j then h.choose
  else (exists_pos_entry C x).choose

lemma nextF_pos (n0 : ℕ) (j : Fin r) (s : ℕ) (x : Fin r) : 0 < C.IP x (nextF C n0 j s x) := by
  unfold nextF
  split_ifs with h
  · exact h.choose_spec.1
  · exact (exists_pos_entry C x).choose_spec

lemma nextF_step (n0 : ℕ) (j : Fin r) (s : ℕ) (x : Fin r) (hs : s < n0)
    (hx : 0 < (C.IP ^ (n0 - s)) x j) :
    0 < (C.IP ^ (n0 - s - 1)) (nextF C n0 j s x) j := by
  obtain ⟨m, hm⟩ : ∃ m, n0 - s = m + 1 := ⟨n0 - s - 1, by omega⟩
  have hm' : n0 - s - 1 = m := by omega
  rw [hm, pow_succ', Matrix.mul_apply] at hx
  have hex : ∃ y, 0 < C.IP x y ∧ 0 < (C.IP ^ (n0 - s - 1)) y j := by
    rw [hm']
    by_contra hcon
    push Not at hcon
    have : ∑ y, C.IP x y * (C.IP ^ m) y j ≤ 0 := by
      apply Finset.sum_nonpos
      intro y _
      rcases (IP_nonneg C x y).lt_or_eq with h1 | h1
      · exact mul_nonpos_of_nonneg_of_nonpos h1.le (hcon y h1)
      · rw [← h1, zero_mul]
    linarith
  unfold nextF
  rw [dif_pos hex]
  exact hex.choose_spec.2

noncomputable def pathF (n0 : ℕ) (j : Fin r) : ℕ → Fin r → Fin r
  | 0, i => i
  | s + 1, i => nextF C n0 j s (pathF n0 j s i)

lemma pathF_inv (n0 : ℕ) (j : Fin r) (hn0 : ∀ x, 0 < (C.IP ^ n0) x j) (i : Fin r) :
    ∀ s, s ≤ n0 → 0 < (C.IP ^ (n0 - s)) (pathF C n0 j s i) j := by
  intro s
  induction s with
  | zero => intro _; simpa [pathF] using hn0 i
  | succ s ih =>
    intro hs
    simp only [pathF]
    rw [show n0 - (s + 1) = n0 - s - 1 from (Nat.sub_sub _ _ _).symm]
    exact nextF_step C n0 j s _ (by omega) (ih (by omega))

lemma pathF_end (n0 : ℕ) (j : Fin r) (hn0 : ∀ x, 0 < (C.IP ^ n0) x j) (i : Fin r) :
    pathF C n0 j n0 i = j := by
  have := pathF_inv C n0 j hn0 i n0 le_rfl
  rw [Nat.sub_self, pow_zero, Matrix.one_apply] at this
  by_contra hne
  rw [if_neg hne] at this
  exact lt_irrefl _ this

/-- the good event for the block starting at time `t` -/
def Gev (n0 : ℕ) (j : Fin r) (t : ℤ) : Set Ω :=
  ⋂ p : Fin n0 × Fin r, {ω | C.h p.2 (C.xi (t + ((p.1 : ℕ) : ℤ)) p.2 ω) = nextF C n0 j p.1 p.2}

lemma mem_Gev (n0 : ℕ) (j : Fin r) (t : ℤ) (ω : Ω) :
    ω ∈ Gev C n0 j t ↔
      ∀ (s : Fin n0) (x : Fin r), C.h x (C.xi (t + ((s : ℕ) : ℤ)) x ω) = nextF C n0 j s x := by
  simp only [Gev, Set.mem_iInter, Set.mem_ofPred_eq, Prod.forall]

lemma Gev_path (n0 : ℕ) (j : Fin r) (t : ℤ) (ω : Ω) (hω : ω ∈ Gev C n0 j t) (i : Fin r) :
    ∀ s, s ≤ n0 → C.X t s i ω = pathF C n0 j s i := by
  rw [mem_Gev] at hω
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hs
    rw [X_succ, ih (by omega)]
    exact hω ⟨s, by omega⟩ _

lemma Gev_coal (n0 : ℕ) (j : Fin r) (hn0 : ∀ x, 0 < (C.IP ^ n0) x j) (t : ℤ) (ω : Ω)
    (hω : ω ∈ Gev C n0 j t) (i : Fin r) : C.X t n0 i ω = j := by
  rw [Gev_path C n0 j t ω hω i n0 le_rfl, pathF_end C n0 j hn0]

lemma measurableSet_Gev (n0 : ℕ) (j : Fin r) (t : ℤ) : MeasurableSet (Gev C n0 j t) :=
  MeasurableSet.iInter fun p =>
    ((C.measurable_h p.2).comp (C.measurable_xi _ _)) (measurableSet_singleton _)

/-- the block probability -/
noncomputable def delta (n0 : ℕ) (j : Fin r) : ENNReal :=
  ∏ p : Fin n0 × Fin r, ENNReal.ofReal (C.IP p.2 (nextF C n0 j p.1 p.2))

lemma prob_Gev (n0 : ℕ) (j : Fin r) (t : ℤ) : C.P (Gev C n0 j t) = delta C n0 j := by
  have hind : iIndepFun (fun p : Fin n0 × Fin r => C.xi (t + ((p.1 : ℕ) : ℤ)) p.2) C.P := by
    have hinj : Function.Injective (fun p : Fin n0 × Fin r => (t + ((p.1 : ℕ) : ℤ), p.2)) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      have := add_left_cancel hab.1
      exact Prod.ext (Fin.ext (by exact_mod_cast this)) hab.2
    exact C.indep_xi.precomp hinj
  unfold Gev delta
  rw [hind.meas_iInter]
  · congr 1
    funext p
    exact C.implements _ _ _
  · intro p
    rw [MeasurableSpace.measurableSet_comap]
    exact ⟨C.h p.2 ⁻¹' {nextF C n0 j p.1 p.2},
      (C.measurable_h p.2) (measurableSet_singleton _), rfl⟩

lemma delta_pos (n0 : ℕ) (j : Fin r) : 0 < delta C n0 j := by
  unfold delta
  rw [CanonicallyOrderedAdd.prod_pos]
  intro p _
  exact ENNReal.ofReal_pos.mpr (nextF_pos C n0 j p.1 p.2)

lemma delta_le_one (n0 : ℕ) (j : Fin r) : delta C n0 j ≤ 1 := by
  haveI := C.isProb
  rw [← prob_Gev C n0 j 0]
  exact prob_le_one

/-- block start times -/
def tb (n0 : ℕ) (b : ℕ) : ℤ := -(((b + 1) * n0 : ℕ) : ℤ)

/-- the bad event for the first `N` blocks -/
def Abad (n0 : ℕ) (j : Fin r) (N : ℕ) : Set Ω := ⋂ b ∈ Finset.range N, (Gev C n0 j (tb n0 b))ᶜ

noncomputable def SN (n0 N : ℕ) : Finset (ℤ × Fin r) :=
  (Finset.Ico (-((N * n0 : ℕ) : ℤ)) 0) ×ˢ Finset.univ

noncomputable def TN (n0 N : ℕ) : Finset (ℤ × Fin r) :=
  (Finset.Ico (tb n0 N) (tb n0 N + n0)) ×ˢ Finset.univ

lemma mem_TN (n0 N : ℕ) (s : Fin n0) (x : Fin r) : (tb n0 N + ((s : ℕ) : ℤ), x) ∈ TN (r := r) n0 N := by
  simp only [TN, Finset.mem_product, Finset.mem_Ico, Finset.mem_univ, and_true]
  omega

lemma mem_SN (n0 N : ℕ) (b : ℕ) (hb : b < N) (s : Fin n0) (x : Fin r) :
    (tb n0 b + ((s : ℕ) : ℤ), x) ∈ SN (r := r) n0 N := by
  simp only [SN, tb, Finset.mem_product, Finset.mem_Ico, Finset.mem_univ, and_true]
  have h1 : (b + 1) * n0 ≤ N * n0 := Nat.mul_le_mul_right n0 hb
  have h2 : n0 ≤ (b + 1) * n0 := Nat.le_mul_of_pos_left n0 (by omega)
  have h3 := s.isLt
  generalize (b + 1) * n0 = Mb at *
  generalize N * n0 = MN at *
  omega

lemma SN_TN_disjoint (n0 N : ℕ) : Disjoint (SN (r := r) n0 N) (TN n0 N) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  simp only [SN, TN, tb, Finset.mem_product, Finset.mem_Ico] at hp hq
  have e : (((N + 1) * n0 : ℕ) : ℤ) = ((N * n0 : ℕ) : ℤ) + n0 := by push_cast; ring
  rw [e] at hq
  generalize ((N * n0 : ℕ) : ℤ) = MN at *
  omega

/-- the bad event as a set in the coordinates of the first `N` blocks -/
def BS (n0 : ℕ) (j : Fin r) (N : ℕ) : Set (↥(SN (r := r) n0 N) → ℝ) :=
  ⋂ b, ⋂ (hb : b < N), (⋂ s : Fin n0, ⋂ x : Fin r,
    {w | C.h x (w ⟨(tb n0 b + ((s : ℕ) : ℤ), x), mem_SN n0 N b hb s x⟩) = nextF C n0 j s x})ᶜ

/-- the good event of block `N` as a set in the coordinates of block `N` -/
def BT (n0 : ℕ) (j : Fin r) (N : ℕ) : Set (↥(TN (r := r) n0 N) → ℝ) :=
  ⋂ s : Fin n0, ⋂ x : Fin r,
    {w | C.h x (w ⟨(tb n0 N + ((s : ℕ) : ℤ), x), mem_TN n0 N s x⟩) = nextF C n0 j s x}

lemma measurableSet_BS (n0 : ℕ) (j : Fin r) (N : ℕ) : MeasurableSet (BS C n0 j N) :=
  MeasurableSet.iInter fun b => MeasurableSet.iInter fun _ =>
    (MeasurableSet.iInter fun s => MeasurableSet.iInter fun x =>
      ((C.measurable_h x).comp (measurable_pi_apply _)) (measurableSet_singleton _)).compl

lemma measurableSet_BT (n0 : ℕ) (j : Fin r) (N : ℕ) : MeasurableSet (BT C n0 j N) :=
  MeasurableSet.iInter fun s => MeasurableSet.iInter fun x =>
    ((C.measurable_h x).comp (measurable_pi_apply _)) (measurableSet_singleton _)

lemma Abad_eq (n0 : ℕ) (j : Fin r) (N : ℕ) :
    Abad C n0 j N = (fun ω (q : ↥(SN (r := r) n0 N)) => C.xi q.1.1 q.1.2 ω) ⁻¹' BS C n0 j N := by
  ext ω
  simp only [Abad, BS, Set.mem_preimage, Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range,
    mem_Gev, Set.mem_ofPred_eq]

lemma Gev_eq (n0 : ℕ) (j : Fin r) (N : ℕ) :
    Gev C n0 j (tb n0 N) =
      (fun ω (q : ↥(TN (r := r) n0 N)) => C.xi q.1.1 q.1.2 ω) ⁻¹' BT C n0 j N := by
  ext ω
  simp only [BT, Set.mem_preimage, Set.mem_iInter, mem_Gev, Set.mem_ofPred_eq]

lemma Abad_succ (n0 : ℕ) (j : Fin r) (N : ℕ) :
    Abad C n0 j (N + 1) = Abad C n0 j N ∩ (Gev C n0 j (tb n0 N))ᶜ := by
  unfold Abad
  rw [Finset.range_add_one, Finset.set_biInter_insert, Set.inter_comm]

lemma prob_Abad (n0 : ℕ) (j : Fin r) (N : ℕ) :
    C.P (Abad C n0 j N) ≤ (1 - delta C n0 j) ^ N := by
  haveI := C.isProb
  induction N with
  | zero =>
    simp [Abad]
  | succ N ih =>
    rw [Abad_succ, pow_succ]
    have hind := C.indep_xi.indepFun_finset (SN n0 N) (TN n0 N) (SN_TN_disjoint n0 N)
      (fun p => C.measurable_xi p.1 p.2)
    rw [Abad_eq, Gev_eq, ← Set.preimage_compl,
      hind.measure_inter_preimage_eq_mul _ _ (measurableSet_BS C n0 j N)
        (measurableSet_BT C n0 j N).compl, Set.preimage_compl, ← Gev_eq, ← Abad_eq,
      prob_compl_eq_one_sub (measurableSet_Gev C n0 j _), prob_Gev]
    exact mul_le_mul' ih le_rfl

lemma Gev_subset_coal (n0 : ℕ) (j : Fin r) (hn0 : ∀ x, 0 < (C.IP ^ n0) x j) (N b : ℕ)
    (hb : b < N) : Gev C n0 j (tb n0 b) ⊆ {ω | C.Coalesced (N * n0) ω} := by
  intro ω hω
  obtain ⟨c, rfl⟩ : ∃ c, N = b + 1 + c := ⟨N - (b + 1), by omega⟩
  have key : ∀ i, C.X (-(((b + 1 + c) * n0 : ℕ) : ℤ)) ((b + 1 + c) * n0) i ω
      = C.X (-((b * n0 : ℕ) : ℤ)) (b * n0) j ω := by
    intro i
    have e1 : (b + 1 + c) * n0 = c * n0 + (n0 + b * n0) := by ring
    rw [e1, X_comp]
    have e2 : -(((c * n0 + (n0 + b * n0)) : ℕ) : ℤ) + ((c * n0 : ℕ) : ℤ) = tb n0 b := by
      unfold tb; push_cast; ring
    rw [e2, X_comp, Gev_coal C n0 j hn0 _ ω hω]
    have e3 : tb n0 b + (n0 : ℤ) = -((b * n0 : ℕ) : ℤ) := by
      unfold tb; push_cast; ring
    rw [e3]
  intro i i'
  show C.X (-(((b + 1 + c) * n0 : ℕ) : ℤ)) ((b + 1 + c) * n0) i ω
      = C.X (-(((b + 1 + c) * n0 : ℕ) : ℤ)) ((b + 1 + c) * n0) i' ω
  rw [key i, key i']

lemma coal_compl_le (n0 : ℕ) (j : Fin r) (hn0 : ∀ x, 0 < (C.IP ^ n0) x j) (N : ℕ) :
    C.P {ω | C.Coalesced (N * n0) ω}ᶜ ≤ (1 - delta C n0 j) ^ N := by
  refine le_trans (measure_mono ?_) (prob_Abad C n0 j N)
  intro ω hω
  simp only [Abad, Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range]
  intro b hb hG
  exact hω (Gev_subset_coal C n0 j hn0 N b hb hG)

lemma pow_tendsto (n0 : ℕ) (j : Fin r) :
    Tendsto (fun N : ℕ => (1 - delta C n0 j) ^ N) atTop (𝓝 0) := by
  have hne : 1 - delta C n0 j ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have hlt : 1 - delta C n0 j < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (delta_pos C n0 j).ne'
  set q : ℝ := (1 - delta C n0 j).toReal with hq
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hq1 : q < 1 := by
    have := (ENNReal.toReal_lt_toReal hne ENNReal.one_ne_top).mpr hlt
    simpa using this
  have e : ∀ N : ℕ, (1 - delta C n0 j) ^ N = ENNReal.ofReal (q ^ N) := by
    intro N
    rw [ENNReal.ofReal_pow hq0, hq, ENNReal.ofReal_toReal hne]
  simp_rw [e]
  have := ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
  simpa using this

lemma coal_union_full (n0 : ℕ) (j : Fin r) (hn0 : ∀ x, 0 < (C.IP ^ n0) x j) :
    C.P (⋃ n, {ω | C.Coalesced n ω}) = 1 := by
  haveI := C.isProb
  rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion fun n => measurableSet_coalesced C n)]
  have hle : ∀ N : ℕ, C.P (⋃ n, {ω | C.Coalesced n ω})ᶜ ≤ (1 - delta C n0 j) ^ N := by
    intro N
    refine le_trans (measure_mono ?_) (coal_compl_le C n0 j hn0 N)
    rw [Set.compl_subset_compl]
    exact Set.subset_iUnion (fun n => {ω | C.Coalesced n ω}) (N * n0)
  exact le_antisymm (ge_of_tendsto' (pow_tendsto C n0 j) hle) zero_le'

lemma coal_tendsto : Tendsto (fun n => C.P {ω | C.Coalesced n ω}) atTop (𝓝 1) := by
  haveI := C.isProb
  have hmono : Monotone fun n => {ω | C.Coalesced n ω} :=
    monotone_nat_of_le_succ fun n ω h => coalesced_mono C n ω h
  have := tendsto_measure_iUnion_atTop (μ := C.P) hmono
  obtain ⟨j⟩ : Nonempty (Fin r) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := C.pi_sum
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact zero_ne_one this
  obtain ⟨n0, _, hn0⟩ := exists_n0 C j
  rw [coal_union_full C n0 j hn0] at this
  exact this

end CFTPCoal

section CFTPMain

variable {r : ℕ} (C : CFTP Ω r)

theorem ae_of_tendsto_one'' (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (T : Set Ω) (Cs : ℕ → Set Ω) (hC : ∀ n, MeasurableSet (Cs n))
    (hsub : ∀ n, Cs n ⊆ T) (hlim : Tendsto (fun n => P0 (Cs n)) atTop (𝓝 1)) :
    ∀ᵐ ω ∂P0, ω ∈ T := by
  rw [ae_iff]
  have hle : ∀ n, P0 {ω | ¬ ω ∈ T} + P0 (Cs n) ≤ 1 := by
    intro n
    have h1 : P0 {ω | ¬ ω ∈ T} ≤ P0 (Cs n)ᶜ := by
      apply measure_mono
      intro ω hω hc
      exact hω (hsub n hc)
    calc P0 {ω | ¬ ω ∈ T} + P0 (Cs n) ≤ P0 (Cs n)ᶜ + P0 (Cs n) := add_le_add h1 le_rfl
      _ = 1 := by rw [add_comm, measure_add_measure_compl (hC n), measure_univ]
  have hlim2 : Tendsto (fun n => P0 {ω | ¬ ω ∈ T} + P0 (Cs n)) atTop
      (𝓝 (P0 {ω | ¬ ω ∈ T} + 1)) := hlim.const_add _
  have := le_of_tendsto' hlim2 hle
  have h2 : P0 {ω | ¬ ω ∈ T} + 1 ≤ 0 + 1 := by simpa using this
  exact le_antisymm ((ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp h2) zero_le'

theorem propp_wilson_core (i₀ : Fin r) :
    (∀ᵐ ω ∂C.P, ∃ n : ℕ, 1 ≤ n ∧ C.Coalesced n ω) ∧
    ∀ Z : Ω → Fin r, Measurable Z →
      (∀ᵐ ω ∂C.P, ∀ n : ℕ, 1 ≤ n → C.Coalesced n ω → Z ω = C.X (-(n : ℤ)) n i₀ ω) →
      ∀ j : Fin r, (C.P {ω | Z ω = j}).toReal = C.pi j := by
  haveI := C.isProb
  set E : ℕ → Set Ω := fun n => {ω | C.Coalesced (n + 1) ω} with hE
  have hEm : ∀ n, MeasurableSet (E n) := fun n => measurableSet_coalesced C (n + 1)
  have hElim : Tendsto (fun n => C.P (E n)) atTop (𝓝 1) :=
    (coal_tendsto C).comp (tendsto_add_atTop_nat 1)
  have hEc : Tendsto (fun n => C.P (E n)ᶜ) atTop (𝓝 0) := by
    have hc : ∀ n, C.P (E n)ᶜ = 1 - C.P (E n) := fun n => prob_compl_eq_one_sub (hEm n)
    simp only [hc]
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ENNReal))) hElim
      (Or.inl ENNReal.one_ne_top)
    simpa using this
  refine ⟨?_, ?_⟩
  · apply ae_of_tendsto_one'' C.P _ E hEm _ hElim
    intro n ω hω
    exact ⟨n + 1, by omega, hω⟩
  · intro Z hZ hZcoal j
    set G : Set Ω := {ω | ∀ n : ℕ, 1 ≤ n → C.Coalesced n ω →
      Z ω = C.X (-(n : ℤ)) n i₀ ω} with hG
    have hGc : C.P Gᶜ = 0 := ae_iff.mp hZcoal
    have hup : ∀ n, C.P {ω | Z ω = j} ≤
        C.P {ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) i₀ ω = j} + C.P (E n)ᶜ := by
      intro n
      calc C.P {ω | Z ω = j}
          ≤ C.P ({ω | Z ω = j} ∩ E n) + C.P ({ω | Z ω = j} \ E n) :=
            measure_le_inter_add_sdiff _ _ _
        _ ≤ (C.P {ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) i₀ ω = j} + C.P Gᶜ) + C.P (E n)ᶜ := by
            gcongr
            · calc C.P ({ω | Z ω = j} ∩ E n)
                  ≤ C.P ({ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) i₀ ω = j} ∪ Gᶜ) := by
                    apply measure_mono
                    rintro ω ⟨h1, h2⟩
                    by_cases hg : ω ∈ G
                    · left
                      have := hg (n + 1) (by omega) h2
                      simp only [Set.mem_ofPred_eq] at h1 ⊢
                      rw [← this]; exact h1
                    · right; exact hg
                _ ≤ _ := measure_union_le _ _
            · exact Set.sdiff_subset_compl _ _
        _ = _ := by rw [hGc, add_zero]
    have hlow : ∀ n, C.P {ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) i₀ ω = j} ≤
        C.P {ω | Z ω = j} + C.P (E n)ᶜ := by
      intro n
      calc C.P {ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) i₀ ω = j}
          ≤ C.P ({ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) i₀ ω = j} ∩ E n)
            + C.P ({ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) i₀ ω = j} \ E n) :=
            measure_le_inter_add_sdiff _ _ _
        _ ≤ (C.P {ω | Z ω = j} + C.P Gᶜ) + C.P (E n)ᶜ := by
            gcongr
            · calc C.P ({ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) i₀ ω = j} ∩ E n)
                  ≤ C.P ({ω | Z ω = j} ∪ Gᶜ) := by
                    apply measure_mono
                    rintro ω ⟨h1, h2⟩
                    by_cases hg : ω ∈ G
                    · left
                      have := hg (n + 1) (by omega) h2
                      simp only [Set.mem_ofPred_eq] at h1 ⊢
                      rw [this]; exact h1
                    · right; exact hg
                _ ≤ _ := measure_union_le _ _
            · exact Set.sdiff_subset_compl _ _
        _ = _ := by rw [hGc, add_zero]
    have hXlim : Tendsto (fun n => C.P {ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) i₀ ω = j}) atTop
        (𝓝 (ENNReal.ofReal (C.pi j))) := by
      have h1 : ∀ n, C.P {ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) i₀ ω = j}
          = ENNReal.ofReal ((C.IP ^ (n + 1)) i₀ j) := fun n => by
        rw [prob_X_eq_invariant C _ 0, markov]
      simp only [h1]
      apply ENNReal.tendsto_ofReal
      exact (C.ergodic i₀ j).comp (tendsto_add_atTop_nat 1)
    have hle : C.P {ω | Z ω = j} ≤ ENNReal.ofReal (C.pi j) := by
      have := ge_of_tendsto' (hXlim.add hEc) hup
      simpa using this
    have hge : ENNReal.ofReal (C.pi j) ≤ C.P {ω | Z ω = j} := by
      have := le_of_tendsto_of_tendsto' hXlim (tendsto_const_nhds.add hEc) hlow
      simpa using this
    rw [le_antisymm hle hge, ENNReal.toReal_ofReal (C.pi_nonneg j)]

end CFTPMain

end PalmQueueing.Recurrence

open PalmQueueing.Recurrence
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution {r : ℕ} (C : CFTP Ω r) (i₀ : Fin r) :
    (∀ᵐ ω ∂C.P, ∃ n : ℕ, 1 ≤ n ∧ C.Coalesced n ω) ∧
    ∀ Z : Ω → Fin r, Measurable Z →
      (∀ᵐ ω ∂C.P, ∀ n : ℕ, 1 ≤ n → C.Coalesced n ω → Z ω = C.X (-(n : ℤ)) n i₀ ω) →
      ∀ j : Fin r, (C.P {ω | Z ω = j}).toReal = C.pi j := by
  exact propp_wilson_core C i₀
