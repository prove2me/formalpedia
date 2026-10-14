-- Prove2me | solution 1 for SimpsonInv.Vertex.vertices_model
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:15:42.693224+00:00
-- url     : https://prove2.me/submissions/1e4e7961-b66c-43bd-90dd-48df5448521f

import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting



namespace SimpsonInv.Vertex

lemma sv_ext_affine {m : ℕ} (S0 Sn a b : ℝ) (hab : a + b = 1) (x y : Fin m → ℝ) (i : ℕ) :
    extVec S0 Sn (a • x + b • y) i = a * extVec S0 Sn x i + b * extVec S0 Sn y i := by
  unfold extVec
  split_ifs
  · linear_combination (-S0) * hab
  · simp
  · linear_combination (-Sn) * hab

lemma sv_rad_affine {m : ℕ} (T : ℕ → ℝ) (S0 Sn a b : ℝ) (hab : a + b = 1) (x y : Fin m → ℝ) (i : ℕ) :
    radicand T S0 Sn (a • x + b • y) i
      = a * radicand T S0 Sn x i + b * radicand T S0 Sn y i := by
  unfold radicand
  rw [sv_ext_affine S0 Sn a b hab, sv_ext_affine S0 Sn a b hab]
  linear_combination (-(T i)) * hab

lemma sv_ext_shift {m : ℕ} (S0 Sn t : ℝ) (v d : Fin m → ℝ) (i : ℕ) :
    extVec S0 Sn (v + t • d) i = extVec S0 Sn v i + t * extVec 0 0 d i := by
  unfold extVec
  split_ifs <;> simp

lemma sv_rad_shift {m : ℕ} (T : ℕ → ℝ) (S0 Sn t : ℝ) (v d : Fin m → ℝ) (i : ℕ) :
    radicand T S0 Sn (v + t • d) i
      = radicand T S0 Sn v i + t * (extVec 0 0 d (i - 1) - extVec 0 0 d i) := by
  unfold radicand
  rw [sv_ext_shift, sv_ext_shift]
  ring


lemma vm_e_zero {m : ℕ} (S : Fin m → ℝ) : extVec 0 0 S 0 = 0 := by simp [extVec]

lemma vm_e_succ {m : ℕ} (S : Fin m → ℝ) (j : Fin m) : extVec 0 0 S (j.val + 1) = S j := by
  simp [extVec]

lemma vm_e_big {m : ℕ} (S : Fin m → ℝ) (i : ℕ) (h : m < i) : extVec 0 0 S i = 0 := by
  have : i ≠ 0 := by omega
  have h2 : ¬ i ≤ m := by omega
  simp [extVec, this, h2]

lemma vm_e_nonneg {m : ℕ} (S : Fin m → ℝ) (hS : ∀ j, 0 ≤ S j) (i : ℕ) : 0 ≤ extVec 0 0 S i := by
  unfold extVec
  split_ifs
  · exact le_rfl
  · exact hS _
  · exact le_rfl

lemma vm_ev_dom {m : ℕ} (T : ℕ → ℝ) (S w : Fin m → ℝ) (hS : S ∈ dom (m := m) T 0 0)
    (h1 : ∀ j, w j ≠ 0 → 0 < S j)
    (h2 : ∀ i ∈ Finset.Icc 1 (m + 1), extVec 0 0 w (i - 1) - extVec 0 0 w i ≠ 0 →
      0 < radicand T 0 0 S i) :
    ∀ᶠ t in nhds (0:ℝ), S + t • w ∈ dom (m := m) T 0 0 := by
  have e1 : ∀ᶠ t in nhds (0:ℝ), ∀ j : Fin m, 0 ≤ (S + t • w) j := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : w j = 0
    · exact Filter.Eventually.of_forall (fun t => by simp [hj, hS.1 j])
    · have hpos : 0 < S j := h1 j hj
      have hc : ContinuousAt (fun t : ℝ => (S + t • w) j) 0 := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        fun_prop
      exact ((continuousAt_const (y := (0:ℝ))).eventually_lt hc (by simpa using hpos)).mono
        (fun t ht => ht.le)
  have e2 : ∀ᶠ t in nhds (0:ℝ), ∀ i ∈ Finset.Icc 1 (m + 1), 0 ≤ radicand T 0 0 (S + t • w) i := by
    rw [Filter.eventually_all_finset]
    intro i hi
    by_cases hri : extVec 0 0 w (i - 1) - extVec 0 0 w i = 0
    · exact Filter.Eventually.of_forall (fun t => by
        rw [sv_rad_shift, hri]; simpa using hS.2 i hi)
    · have hpos : 0 < radicand T 0 0 S i := h2 i hi hri
      have hc : ContinuousAt (fun t : ℝ => radicand T 0 0 (S + t • w) i) 0 := by
        have : (fun t : ℝ => radicand T 0 0 (S + t • w) i) = fun t => radicand T 0 0 S i + t * (extVec 0 0 w (i - 1) - extVec 0 0 w i) := by
          funext t; exact sv_rad_shift T 0 0 t S w i
        rw [this]; fun_prop
      exact ((continuousAt_const (y := (0:ℝ))).eventually_lt hc (by simpa [sv_rad_shift] using hpos)).mono
        (fun t ht => ht.le)
  exact (e1.and e2).mono (fun t ht => ⟨ht.1, ht.2⟩)

lemma vm_ext_of_pattern {m : ℕ} (T : ℕ → ℝ) (S : Fin m → ℝ) (hS : S ∈ dom (m := m) T 0 0)
    (hp : ∀ j : Fin m, S j = 0 ∨ S j = extVec 0 0 S j.val + T (j.val + 1)) :
    S ∈ Set.extremePoints ℝ (dom (m := m) T 0 0) := by
  refine ⟨hS, ?_⟩
  intro x1 hx1 x2 hx2 hseg
  obtain ⟨a, b, ha, hb, hab, hS_eq⟩ := hseg
  have key : ∀ i, i ≤ m → extVec 0 0 x1 i = extVec 0 0 S i ∧ extVec 0 0 x2 i = extVec 0 0 S i := by
    intro i
    induction i with
    | zero => intro _; simp [vm_e_zero]
    | succ n ih =>
      intro hn
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      let j : Fin m := ⟨n, by omega⟩
      have hSj : S j = a * x1 j + b * x2 j := by rw [← hS_eq]; simp
      have e1 : extVec 0 0 x1 (n + 1) = x1 j := vm_e_succ x1 j
      have e2 : extVec 0 0 x2 (n + 1) = x2 j := vm_e_succ x2 j
      have e3 : extVec 0 0 S (n + 1) = S j := vm_e_succ S j
      rw [e1, e2, e3]
      have p1 : 0 ≤ x1 j := hx1.1 j
      have p2 : 0 ≤ x2 j := hx2.1 j
      rcases hp j with h0 | h1
      · have q1 : a * x1 j = 0 := by nlinarith [mul_nonneg ha.le p1, mul_nonneg hb.le p2]
        have q2 : b * x2 j = 0 := by nlinarith [mul_nonneg ha.le p1, mul_nonneg hb.le p2]
        exact ⟨by rw [h0]; exact (mul_eq_zero.1 q1).resolve_left ha.ne',
          by rw [h0]; exact (mul_eq_zero.1 q2).resolve_left hb.ne'⟩
      · have r1 := hx1.2 (n + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
        have r2 := hx2.2 (n + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
        unfold radicand at r1 r2
        simp only [Nat.add_sub_cancel] at r1 r2
        rw [e1, ih1] at r1
        rw [e2, ih2] at r2
        have h1' : S j = extVec 0 0 S n + T (n + 1) := h1
        have s1 : x1 j ≤ S j := by linarith
        have s2 : x2 j ≤ S j := by linarith
        have q1 : a * (S j - x1 j) = 0 := by
          nlinarith [mul_nonneg ha.le (sub_nonneg.2 s1), mul_nonneg hb.le (sub_nonneg.2 s2)]
        have q2 : b * (S j - x2 j) = 0 := by
          nlinarith [mul_nonneg ha.le (sub_nonneg.2 s1), mul_nonneg hb.le (sub_nonneg.2 s2)]
        have t1 := (mul_eq_zero.1 q1).resolve_left ha.ne'
        have t2 := (mul_eq_zero.1 q2).resolve_left hb.ne'
        exact ⟨by linarith, by linarith⟩
  have fin : ∀ x : Fin m → ℝ, (∀ i, i ≤ m → extVec 0 0 x i = extVec 0 0 S i) → x = S := by
    intro x hx
    funext j
    have := hx (j.val + 1) (by omega)
    rwa [vm_e_succ, vm_e_succ] at this
  exact fin x1 (fun i hi => (key i hi).1)

lemma vm_pattern_of_extreme {m : ℕ} (T : ℕ → ℝ) (hT : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < T i)
    (S : Fin m → ℝ) (hS : S ∈ Set.extremePoints ℝ (dom (m := m) T 0 0)) :
    ∀ j : Fin m, S j = 0 ∨ S j = extVec 0 0 S j.val + T (j.val + 1) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j0, h0, h1⟩ := hcon
  have hSD := hS.1
  have hnn : ∀ i, 0 ≤ extVec 0 0 S i := vm_e_nonneg S hSD.1
  obtain ⟨a, ha⟩ : ∃ a, a = j0.val + 1 := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by omega
  have ha2 : a ≤ m := by omega
  have hea : 0 < extVec 0 0 S a := by
    rw [ha, vm_e_succ]; exact lt_of_le_of_ne (hSD.1 j0) (Ne.symm h0)
  have hra : 0 < radicand T 0 0 S a := by
    have := hSD.2 a (Finset.mem_Icc.2 ⟨ha1, by omega⟩)
    unfold radicand at this ⊢
    have e1 : a - 1 = j0.val := by omega
    rw [e1]
    have e2 : extVec 0 0 S a = S j0 := by rw [ha]; exact vm_e_succ S j0
    rw [e1, e2] at this
    rw [e2]
    rw [← ha] at h1
    rcases lt_or_eq_of_le this with h | h
    · exact h
    · exfalso; apply h1; linarith
  classical
  have hQm : a ≤ m ∧ 0 < radicand T 0 0 S (m + 1) := by
    refine ⟨ha2, ?_⟩
    unfold radicand
    simp only [Nat.add_sub_cancel]
    rw [vm_e_big S (m + 1) (by omega)]
    have := hT (m + 1) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩)
    have := hnn m
    linarith
  have hex : ∃ b, a ≤ b ∧ 0 < radicand T 0 0 S (b + 1) := ⟨m, hQm⟩
  obtain ⟨b, ⟨hab, hrb⟩, hbmin⟩ : ∃ b, (a ≤ b ∧ 0 < radicand T 0 0 S (b + 1)) ∧
      ∀ k, k < b → ¬ (a ≤ k ∧ 0 < radicand T 0 0 S (k + 1)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hbm : b ≤ m := by
    by_contra h
    exact hbmin m (by omega) hQm
  -- chain equalities
  have hchain : ∀ k, a ≤ k → k < b → extVec 0 0 S (k + 1) = extVec 0 0 S k + T (k + 1) := by
    intro k hk hkb
    have h := hSD.2 (k + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have h' := hbmin k hkb
    have : ¬ 0 < radicand T 0 0 S (k + 1) := fun hh => h' ⟨hk, hh⟩
    have h0' : radicand T 0 0 S (k + 1) = 0 := le_antisymm (not_lt.1 this) h
    unfold radicand at h0'
    simp only [Nat.add_sub_cancel] at h0'
    linarith
  have hpos : ∀ k, a ≤ k → k ≤ b → 0 < extVec 0 0 S k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; exact hea
    | succ k hk ih =>
      intro hkb
      rw [hchain k hk (by omega)]
      have := hT (k + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      have := ih (by omega)
      linarith
  -- direction
  let d : ℕ → ℝ := fun i => if a ≤ i ∧ i ≤ b then 1 else 0
  let w : Fin m → ℝ := fun j => d (j.val + 1)
  have hew : ∀ i, extVec 0 0 w i = d i := by
    intro i
    by_cases h0i : i = 0
    · subst h0i; simp [vm_e_zero, d]; omega
    · by_cases him : i ≤ m
      · have : i = (⟨i - 1, by omega⟩ : Fin m).val + 1 := by simp; omega
        conv_lhs => rw [this, vm_e_succ]
        simp only [w]
        rw [← this]
      · rw [vm_e_big w i (by omega)]
        simp only [d]
        rw [if_neg (by omega)]
  have h1' : ∀ j, w j ≠ 0 → 0 < S j := by
    intro j hj
    simp only [w, d] at hj
    split_ifs at hj with hh
    · have := hpos (j.val + 1) hh.1 hh.2
      rwa [vm_e_succ] at this
    · exact absurd rfl hj
  have h2' : ∀ i ∈ Finset.Icc 1 (m + 1), extVec 0 0 w (i - 1) - extVec 0 0 w i ≠ 0 →
      0 < radicand T 0 0 S i := by
    intro i hi hne
    rw [hew, hew] at hne
    have : i = a ∨ i = b + 1 := by
      by_contra hh
      push Not at hh
      apply hne
      rw [Finset.mem_Icc] at hi
      simp only [d]
      split_ifs <;> first | (exfalso; omega) | norm_num
    rcases this with rfl | rfl
    · exact hra
    · exact hrb
  have hev := vm_ev_dom T S w hSD h1' h2'
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hx : S + (ε / 2) • w ∈ dom (m := m) T 0 0 := hball (by simp [abs_of_pos hε]; linarith)
  have hy : S + (-(ε / 2)) • w ∈ dom (m := m) T 0 0 := hball (by simp [abs_of_pos hε]; linarith)
  have hmid : (1 / 2 : ℝ) • (S + (ε / 2) • w) + (1 / 2 : ℝ) • (S + (-(ε / 2)) • w) = S := by
    ext k; simp; ring
  have hseg : S ∈ openSegment ℝ (S + (ε / 2) • w) (S + (-(ε / 2)) • w) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, hmid⟩
  have := hS.2 hx hy hseg
  have hj := congrFun this ⟨a - 1, by omega⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj
  have hwa : w ⟨a - 1, by omega⟩ = 1 := by
    simp only [w, d]
    rw [if_pos (by simp; omega)]
  rw [hwa] at hj
  linarith

noncomputable def vmSeq (T : ℕ → ℝ) (σ : ℕ → Bool) : ℕ → ℝ
  | 0 => 0
  | k + 1 => if σ k then vmSeq T σ k + T (k + 1) else 0

def vmExt {m : ℕ} (σ : Fin m → Bool) : ℕ → Bool := fun k => if h : k < m then σ ⟨k, h⟩ else false

noncomputable def vmG {m : ℕ} (T : ℕ → ℝ) (σ : Fin m → Bool) : Fin m → ℝ :=
  fun j => vmSeq T (vmExt σ) (j.val + 1)

lemma vm_seq_nonneg {m : ℕ} (T : ℕ → ℝ) (hT : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < T i)
    (σ : Fin m → Bool) : ∀ k, k ≤ m → 0 ≤ vmSeq T (vmExt σ) k := by
  intro k
  induction k with
  | zero => intro _; simp [vmSeq]
  | succ n ih =>
    intro hn
    have := ih (by omega)
    have hTn := hT (n + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    simp only [vmSeq]
    split_ifs
    · linarith
    · exact le_rfl

lemma vm_g_eq {m : ℕ} (T : ℕ → ℝ) (σ : Fin m → Bool) (j : Fin m) :
    vmG T σ j = if σ j then vmSeq T (vmExt σ) j.val + T (j.val + 1) else 0 := by
  have : vmExt σ j.val = σ j := by simp [vmExt]
  simp only [vmG, vmSeq, this]

lemma vm_e_g {m : ℕ} (T : ℕ → ℝ) (σ : Fin m → Bool) : ∀ k, k ≤ m →
    extVec 0 0 (vmG T σ) k = vmSeq T (vmExt σ) k := by
  intro k hk
  by_cases h0 : k = 0
  · subst h0; simp [vm_e_zero, vmSeq]
  · have : k = (⟨k - 1, by omega⟩ : Fin m).val + 1 := by simp; omega
    conv_lhs => rw [this, vm_e_succ]
    simp only [vmG]
    rw [← this]

lemma vm_g_iff {m : ℕ} (T : ℕ → ℝ) (hT : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < T i)
    (σ : Fin m → Bool) (j : Fin m) : σ j = true ↔ 0 < vmG T σ j := by
  rw [vm_g_eq]
  have h1 := vm_seq_nonneg T hT σ j.val (by omega)
  have h2 := hT (j.val + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  cases hs : σ j
  · simp
  · simp only [if_true, true_iff]; linarith

lemma vm_g_inj {m : ℕ} (T : ℕ → ℝ) (hT : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < T i) :
    Function.Injective (vmG (m := m) T) := by
  intro σ τ h
  funext j
  have e1 := vm_g_iff T hT σ j
  have e2 := vm_g_iff T hT τ j
  rw [h] at e1
  have : (σ j = true) ↔ (τ j = true) := e1.trans e2.symm
  simpa using this

lemma vm_g_mem {m : ℕ} (T : ℕ → ℝ) (hT : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < T i)
    (σ : Fin m → Bool) :
    vmG T σ ∈ {S : Fin m → ℝ | ∀ j : Fin m, S j = 0 ∨ S j = extVec 0 0 S j.val + T (j.val + 1)} ∩
          dom (m := m) T 0 0 := by
  have hnn : ∀ j, 0 ≤ vmG T σ j := by
    intro j
    rw [vm_g_eq]
    have h1 := vm_seq_nonneg T hT σ j.val (by omega)
    have h2 := hT (j.val + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    split_ifs
    · linarith
    · exact le_rfl
  refine ⟨fun j => ?_, hnn, fun i hi => ?_⟩
  · rw [vm_e_g T σ j.val (by omega), vm_g_eq]
    cases hs : σ j
    · left; simp
    · right; simp
  · rw [Finset.mem_Icc] at hi
    have hTi := hT i (Finset.mem_Icc.2 hi)
    unfold radicand
    by_cases him : i ≤ m
    · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [vm_e_g T σ n (by omega), vm_e_g T σ (n + 1) him]
      have := vm_seq_nonneg T hT σ n (by omega)
      simp only [vmSeq]
      split_ifs <;> linarith
    · have : i = m + 1 := by omega
      subst this
      simp only [Nat.add_sub_cancel]
      rw [vm_e_big _ (m + 1) (by omega)]
      have := hnn
      have h3 := vm_e_nonneg (vmG T σ) hnn m
      linarith

lemma vm_range {m : ℕ} (T : ℕ → ℝ) (hT : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < T i) :
    {S : Fin m → ℝ | ∀ j : Fin m, S j = 0 ∨ S j = extVec 0 0 S j.val + T (j.val + 1)} ∩
          dom (m := m) T 0 0 = Set.range (vmG (m := m) T) := by
  apply Set.Subset.antisymm
  · rintro S ⟨hp, hD⟩
    refine ⟨fun j => decide (S j ≠ 0), ?_⟩
    have key : ∀ k, k ≤ m → vmSeq T (vmExt (fun j : Fin m => decide (S j ≠ 0))) k = extVec 0 0 S k := by
      intro k
      induction k with
      | zero => intro _; simp [vmSeq, vm_e_zero]
      | succ n ih =>
        intro hn
        have ih' := ih (by omega)
        let j : Fin m := ⟨n, by omega⟩
        have e3 : extVec 0 0 S (n + 1) = S j := vm_e_succ S j
        have hv : vmExt (fun j : Fin m => decide (S j ≠ 0)) n = decide (S j ≠ 0) := by
          simp [vmExt, j, hn, show n < m by omega]
        simp only [vmSeq, hv, e3]
        by_cases h0 : S j = 0
        · simp [h0]
        · have := (hp j).resolve_left h0
          simp only [ne_eq, h0, not_false_eq_true, decide_true, if_true]
          rw [ih']
          exact this.symm
    funext j
    rw [vmG]
    have := key (j.val + 1) (by omega)
    rw [this, vm_e_succ]
  · rintro _ ⟨σ, rfl⟩
    exact vm_g_mem T hT σ

theorem vertices_model_core {m : ℕ} (T : ℕ → ℝ) (hT : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < T i) :
    Set.extremePoints ℝ (dom (m := m) T 0 0) =
        {S : Fin m → ℝ | ∀ j : Fin m, S j = 0 ∨ S j = extVec 0 0 S j.val + T (j.val + 1)} ∩
          dom (m := m) T 0 0 ∧
      (Set.extremePoints ℝ (dom (m := m) T 0 0)).ncard = 2 ^ m := by
  have hext : Set.extremePoints ℝ (dom (m := m) T 0 0) =
      {S : Fin m → ℝ | ∀ j : Fin m, S j = 0 ∨ S j = extVec 0 0 S j.val + T (j.val + 1)} ∩
          dom (m := m) T 0 0 :=
    Set.Subset.antisymm (fun S hS => ⟨vm_pattern_of_extreme T hT S hS, hS.1⟩)
      (fun S hS => vm_ext_of_pattern T S hS.2 hS.1)
  refine ⟨hext, ?_⟩
  rw [hext, vm_range T hT, ← Set.image_univ, Set.ncard_image_of_injective _ (vm_g_inj T hT),
    Set.ncard_univ]
  simp [Nat.card_eq_fintype_card]

end SimpsonInv.Vertex

open SimpsonInv.Vertex


theorem solution {m : ℕ} (T : ℕ → ℝ) (hT : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < T i) :
    Set.extremePoints ℝ (dom (m := m) T 0 0) =
        {S : Fin m → ℝ | ∀ j : Fin m, S j = 0 ∨ S j = extVec 0 0 S j.val + T (j.val + 1)} ∩
          dom (m := m) T 0 0 ∧
      (Set.extremePoints ℝ (dom (m := m) T 0 0)).ncard = 2 ^ m := by
  exact vertices_model_core T hT
