-- Prove2me | solution 1 for ShadowTomography.QuantumLB.theorem_19
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T03:44:33.405063+00:00
-- url     : https://prove2.me/submissions/e42e1671-62ff-4c11-99a8-5954213871ba

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_ClassicalLB_tensorPow
import Definitions.Def_ShadowTomography_QuantumLB_POVM
import Definitions.Def_ShadowTomography_QuantumLB_IsHalfProjector
import Definitions.Def_ShadowTomography_QuantumLB_rhoState
import Theorems.Thm_ShadowTomography_QuantumLB_eq_2

set_option autoImplicit false

open scoped ComplexOrder Matrix

lemma t19_tp_herm {n : Type} [Fintype n] (σ : Matrix n n ℂ) (hσ : σ.IsHermitian) (k : ℕ) :
    (ShadowTomography.ClassicalLB.tensorPow σ k).IsHermitian := by
  refine Matrix.IsHermitian.ext fun x y => ?_
  simp only [ShadowTomography.ClassicalLB.tensorPow]
  rw [star_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact hσ.apply (x j) (y j)

lemma t19_tp_trace_mul {n : Type} [Fintype n] (ρ σ : Matrix n n ℂ) (k : ℕ) :
    (ShadowTomography.ClassicalLB.tensorPow ρ k *
      ShadowTomography.ClassicalLB.tensorPow σ k).trace = (ρ * σ).trace ^ k := by
  have h1 : (ShadowTomography.ClassicalLB.tensorPow ρ k *
      ShadowTomography.ClassicalLB.tensorPow σ k).trace
      = ∑ p : (Fin k → n) × (Fin k → n), ∏ j, (ρ (p.1 j) (p.2 j) * σ (p.2 j) (p.1 j)) := by
    rw [Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
      ShadowTomography.ClassicalLB.tensorPow, Finset.prod_mul_distrib]
  have h2 : ∑ p : (Fin k → n) × (Fin k → n), ∏ j, (ρ (p.1 j) (p.2 j) * σ (p.2 j) (p.1 j))
      = ∑ z : Fin k → n × n, ∏ j, (ρ (z j).1 (z j).2 * σ (z j).2 (z j).1) :=
    (Equiv.sum_comp (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => n) (fun _ => n))
      (fun p : (Fin k → n) × (Fin k → n) => ∏ j, (ρ (p.1 j) (p.2 j) * σ (p.2 j) (p.1 j)))).symm
  have h3 : (ρ * σ).trace = ∑ q : n × n, ρ q.1 q.2 * σ q.2 q.1 := by
    rw [Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [h1, h2, h3, Fintype.sum_pow]

lemma t19_re_nonneg {Y : Type} [Fintype Y] {A : Matrix Y Y ℂ} (hA : A.PosSemidef) :
    0 ≤ A.trace.re := by
  have h := hA.trace_nonneg
  exact (Complex.le_def.mp h).1

/-- Pointwise AM-GM in the Hilbert–Schmidt form: `0 ≤ Tr((tS-1) Π (tS-1))`. -/
lemma t19_key {Y : Type} [Fintype Y] [DecidableEq Y] (S : Matrix Y Y ℂ) (hS : S.IsHermitian)
    (Q : Matrix Y Y ℂ) (hQ : Q.PosSemidef) (t : ℝ) :
    2 * t * (Q * S).trace.re ≤ t ^ 2 * (S * Q * S).trace.re + Q.trace.re := by
  set B : Matrix Y Y ℂ := (t : ℂ) • S - 1 with hBdef
  have hB : Bᴴ = B := by
    rw [hBdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      hS.eq, Complex.star_def, Complex.conj_ofReal]
  have h := t19_re_nonneg (hQ.mul_mul_conjTranspose_same B)
  rw [hB] at h
  have hexp : (B * Q * B).trace = ((t : ℂ) ^ 2) * (S * Q * S).trace
      - 2 * (t : ℂ) * (Q * S).trace + Q.trace := by
    have hc : (S * Q).trace = (Q * S).trace := Matrix.trace_mul_comm S Q
    simp only [hBdef, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, smul_sub,
      smul_smul, smul_eq_mul, hc]
    ring
  rw [hexp] at h
  have e1 : (((t : ℂ) ^ 2) * (S * Q * S).trace).re = t ^ 2 * (S * Q * S).trace.re := by
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have e2 : (2 * (t : ℂ) * (Q * S).trace).re = 2 * t * (Q * S).trace.re := by
    rw [show (2 : ℂ) * (t : ℂ) = ((2 * t : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  rw [Complex.add_re, Complex.sub_re, e1, e2] at h
  linarith

/-- Change of measure for quantum hypotheses with pairwise disjoint success events. -/
lemma t19_core {Y Ω ι : Type} [Fintype Y] [DecidableEq Y] [Fintype Ω] [Fintype ι]
    (P : ShadowTomography.QuantumLB.POVM Ω Y) (T : ι → Matrix Y Y ℂ)
    (hT : ∀ j, (T j).IsHermitian) (γ : ℝ) (hγ : 0 < γ)
    (hTT : ∀ j, (T j * T j).trace.re ≤ γ)
    (A : ι → Ω → Prop) (hdisj : ∀ j l ω, A j ω → A l ω → j = l)
    (hp : ∀ j, (2 / 3 : ℝ) ≤ P.prob (T j) (A j)) :
    (4 / 9 : ℝ) * Fintype.card ι ≤ γ * Fintype.card Y := by
  classical
  set t : ℝ := 2 / (3 * γ) with htdef
  have ht0 : 0 < t := by positivity
  have htg : t * γ = 2 / 3 := by rw [htdef]; field_simp
  have hh0 : ∀ ω, 0 ≤ (P.op ω).trace.re := fun ω => t19_re_nonneg (P.positive ω)
  have hg0 : ∀ j ω, 0 ≤ (T j * P.op ω * T j).trace.re := by
    intro j ω
    have := t19_re_nonneg ((P.positive ω).conjTranspose_mul_mul_same (T j))
    rwa [(hT j).eq] at this
  have hgall : ∀ j, ∑ ω, (T j * P.op ω * T j).trace.re = (T j * T j).trace.re := by
    intro j
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, P.complete,
      Matrix.mul_one]
  have hhall : ∑ ω, (P.op ω).trace.re = (Fintype.card Y : ℝ) := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, P.complete, Matrix.trace_one]
    exact Complex.natCast_re _
  have hj : ∀ j, 2 * t * P.prob (T j) (A j)
      ≤ t ^ 2 * γ + ∑ ω ∈ Finset.univ.filter (A j), (P.op ω).trace.re := by
    intro j
    have hprob : P.prob (T j) (A j)
        = ∑ ω ∈ Finset.univ.filter (A j), (P.op ω * T j).trace.re := by
      simp only [ShadowTomography.QuantumLB.POVM.prob]
    rw [hprob, Finset.mul_sum]
    calc ∑ ω ∈ Finset.univ.filter (A j), 2 * t * (P.op ω * T j).trace.re
        ≤ ∑ ω ∈ Finset.univ.filter (A j),
            (t ^ 2 * (T j * P.op ω * T j).trace.re + (P.op ω).trace.re) :=
          Finset.sum_le_sum fun ω _ => t19_key (T j) (hT j) (P.op ω) (P.positive ω) t
      _ = t ^ 2 * ∑ ω ∈ Finset.univ.filter (A j), (T j * P.op ω * T j).trace.re
            + ∑ ω ∈ Finset.univ.filter (A j), (P.op ω).trace.re := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ t ^ 2 * γ + ∑ ω ∈ Finset.univ.filter (A j), (P.op ω).trace.re := by
          gcongr
          calc ∑ ω ∈ Finset.univ.filter (A j), (T j * P.op ω * T j).trace.re
              ≤ ∑ ω, (T j * P.op ω * T j).trace.re :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  (fun ω _ _ => hg0 j ω)
            _ = (T j * T j).trace.re := hgall j
            _ ≤ γ := hTT j
  have hsumh : ∑ j, ∑ ω ∈ Finset.univ.filter (A j), (P.op ω).trace.re
      ≤ (Fintype.card Y : ℝ) := by
    rw [← hhall]
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun ω _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : (Finset.univ.filter (fun j => A j ω)).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun j hj l hl => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hl
      exact hdisj j l ω hj hl
    have hc' : ((Finset.univ.filter (fun j => A j ω)).card : ℝ) ≤ 1 := by exact_mod_cast hc
    exact mul_le_of_le_one_left (hh0 ω) hc'
  have htot : ∑ j : ι, 2 * t * P.prob (T j) (A j)
      ≤ (Fintype.card ι : ℝ) * (t ^ 2 * γ) + Fintype.card Y := by
    calc ∑ j : ι, 2 * t * P.prob (T j) (A j)
        ≤ ∑ j : ι, (t ^ 2 * γ + ∑ ω ∈ Finset.univ.filter (A j), (P.op ω).trace.re) :=
          Finset.sum_le_sum fun j _ => hj j
      _ = (Fintype.card ι : ℝ) * (t ^ 2 * γ)
            + ∑ j, ∑ ω ∈ Finset.univ.filter (A j), (P.op ω).trace.re := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ ≤ _ := by linarith
  have hlow : (Fintype.card ι : ℝ) * (2 * t * (2 / 3)) ≤ ∑ j : ι, 2 * t * P.prob (T j) (A j) := by
    calc (Fintype.card ι : ℝ) * (2 * t * (2 / 3)) = ∑ _j : ι, 2 * t * (2 / 3) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ ≤ _ := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hp j) (by positivity)
  have h1 : (Fintype.card ι : ℝ) * (2 / 3 * t) ≤ Fintype.card Y := by
    have e : (Fintype.card ι : ℝ) * (t ^ 2 * γ) = (Fintype.card ι : ℝ) * (2 / 3 * t) := by
      rw [show t ^ 2 * γ = t * (t * γ) by ring, htg]; ring
    rw [e] at htot
    linarith
  have h2 : (Fintype.card ι : ℝ) * (2 / 3 * t) * γ = 4 / 9 * Fintype.card ι := by
    rw [show (Fintype.card ι : ℝ) * (2 / 3 * t) * γ = (Fintype.card ι : ℝ) * (2 / 3) * (t * γ)
      by ring, htg]; ring
  have h3 := mul_le_mul_of_nonneg_right h1 hγ.le
  rw [h2] at h3
  linarith

/-! ### Embedding `Fin n` into `Fin D` -/

noncomputable def t19_V {n D : ℕ} (h : n ≤ D) : Matrix (Fin D) (Fin n) ℂ :=
  (1 : Matrix (Fin D) (Fin D) ℂ).submatrix id (Fin.castLE h)

lemma t19_VhV {n D : ℕ} (h : n ≤ D) : (t19_V h)ᴴ * t19_V h = 1 := by
  ext a c
  simp only [t19_V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
    id, Matrix.one_apply]
  by_cases hac : a = c
  · subst hac
    rw [Finset.sum_eq_single (Fin.castLE h a)]
    · simp
    · intro x _ hx; simp [hx]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [hac]
    · intro x _
      by_cases hx : Fin.castLE h a = x
      · subst hx
        have : Fin.castLE h a ≠ Fin.castLE h c := fun e => hac (Fin.castLE_injective h e)
        simp [this]
      · simp [Ne.symm hx]

noncomputable def t19_emb {n D : ℕ} (h : n ≤ D) (P : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  t19_V h * P * (t19_V h)ᴴ

lemma t19_emb_herm {n D : ℕ} (h : n ≤ D) (P : Matrix (Fin n) (Fin n) ℂ) (hP : P.IsHermitian) :
    (t19_emb h P).IsHermitian := by
  unfold Matrix.IsHermitian t19_emb
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hP.eq, Matrix.mul_assoc]

lemma t19_emb_mul {n D : ℕ} (h : n ≤ D) (P Q : Matrix (Fin n) (Fin n) ℂ) :
    t19_emb h P * t19_emb h Q = t19_emb h (P * Q) := by
  unfold t19_emb
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (t19_V h)ᴴ (t19_V h), t19_VhV, Matrix.one_mul]

lemma t19_emb_trace {n D : ℕ} (h : n ≤ D) (P : Matrix (Fin n) (Fin n) ℂ) :
    (t19_emb h P).trace = P.trace := by
  unfold t19_emb
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, t19_VhV, Matrix.one_mul]

lemma t19_proj_psd {Y : Type} [Fintype Y] [DecidableEq Y] (X : Matrix Y Y ℂ)
    (hX : X.IsHermitian) (hXX : X * X = X) : X.PosSemidef ∧ (1 - X).PosSemidef := by
  constructor
  · have := Matrix.posSemidef_conjTranspose_mul_self X
    rwa [hX.eq, hXX] at this
  · have h1 : (1 - X)ᴴ = 1 - X := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hX.eq]
    have h2 : (1 - X) * (1 - X) = 1 - X := by
      rw [sub_mul, mul_sub, mul_sub, hXX, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
      abel
    have := Matrix.posSemidef_conjTranspose_mul_self (1 - X)
    rwa [h1, h2] at this

/-! ### The states `u • 1 + v • X` -/

noncomputable def t19_sig {Y : Type} [Fintype Y] [DecidableEq Y] (X : Matrix Y Y ℂ) (u v : ℝ) :
    Matrix Y Y ℂ :=
  (u : ℂ) • (1 : Matrix Y Y ℂ) + (v : ℂ) • X

lemma t19_trace_mul_sig {Y : Type} [Fintype Y] [DecidableEq Y] (Z X : Matrix Y Y ℂ) (u v : ℝ) :
    (Z * t19_sig X u v).trace = (u : ℂ) * Z.trace + (v : ℂ) * (Z * X).trace := by
  simp only [t19_sig, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul]

lemma t19_sig_herm {Y : Type} [Fintype Y] [DecidableEq Y] (X : Matrix Y Y ℂ)
    (hX : X.IsHermitian) (u v : ℝ) : (t19_sig X u v).IsHermitian := by
  unfold Matrix.IsHermitian t19_sig
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, hX.eq]
  simp only [Complex.star_def, Complex.conj_ofReal]

lemma t19_sig_psd {Y : Type} [Fintype Y] [DecidableEq Y] (X : Matrix Y Y ℂ)
    (hX : X.PosSemidef) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : (t19_sig X u v).PosSemidef := by
  unfold t19_sig
  exact (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hu)).add
    (hX.smul (Complex.zero_le_real.mpr hv))

/-! ### Assembly from the packing statement (eq_2) -/

lemma t19_le_sq (x : ℝ) (h : 1 ≤ x) : x ≤ x ^ 2 := by nlinarith

lemma t19_nL (n D L : ℝ) (hL : 0 < L) (hL1 : L < 1) (hDL : 32 ≤ L * D) (hnD : D ≤ n + 1)
    (hn : 7 ≤ n) : 31 ≤ n ^ 2 * L := by
  have h1 : L * D ≤ L * (n + 1) := mul_le_mul_of_nonneg_left hnD hL.le
  have h2 : n * L ≤ n ^ 2 * L := mul_le_mul_of_nonneg_right (t19_le_sq n (by linarith)) hL.le
  nlinarith

lemma t19_logK_arith (n D L c₁ : ℝ) (hL : 0 < L) (hc₁L : c₁ ≤ L / 16) (hDL : 32 ≤ L * D)
    (hD : 8 ≤ D) (hnD : D ≤ n + 1) (hn : 7 ≤ n) (l2 : Real.log 2 < 1) :
    2 * c₁ * D ^ 2 ≤ n ^ 2 * L - Real.log 2 := by
  have hD2 : D ^ 2 ≤ 2 * n ^ 2 := by nlinarith
  have hX1 : L * D ^ 2 ≤ L * (2 * n ^ 2) := mul_le_mul_of_nonneg_left hD2 hL.le
  have hX2 : 32 * D ≤ L * D * D := by nlinarith
  have hX3 : c₁ * D ^ 2 ≤ L / 16 * D ^ 2 := mul_le_mul_of_nonneg_right hc₁L (sq_nonneg D)
  have e : L * D * D = L * D ^ 2 := by ring
  nlinarith

lemma t19_sD (u v ε D n s : ℝ) (hDpos : 0 < D) (hnpos : 0 < n) (hnD1 : D ≤ n + 1) (hn7 : 7 ≤ n)
    (huD : u * D = 1 - 6 * ε) (hvn : v * (n / 2) = 6 * ε) (hv : v = 12 * ε / n)
    (hs : s = u * 1 + v * (u * (n / 2) + v * (n / 2))) : s * D ≤ 1 + 48 * ε ^ 2 := by
  have e : s * D = 1 - 36 * ε ^ 2 + 72 * ε ^ 2 * (D / n) := by
    have e3 : s * D = u * D + (v * (n / 2)) * (u * D) + (v * (n / 2)) * (v * D) := by
      rw [hs]; ring
    rw [e3, hvn, huD, hv]
    field_simp
    ring
  have hDn : D / n ≤ 8 / 7 := by
    rw [div_le_iff₀ hnpos]; linarith
  have h2 : 72 * ε ^ 2 * (D / n) ≤ 72 * ε ^ 2 * (8 / 7) :=
    mul_le_mul_of_nonneg_left hDn (by positivity)
  have h3 := sq_nonneg ε
  rw [e]
  linarith


set_option maxHeartbeats 1000000 in
theorem t19_main (heq2 : ∃ c : ℝ, 1 < c ∧ c < 2 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ P : Fin ⌊c ^ (N ^ 2)⌋₊ → Matrix (Fin N) (Fin N) ℂ,
        (∀ i, ShadowTomography.QuantumLB.IsHalfProjector (P i)) ∧
        ∀ i j, i ≠ j →
          |(P i * ShadowTomography.QuantumLB.rhoState (P j)).trace.re - 1 / 2| ≤ 1 / 12) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ (D M : ℕ) (ε : ℝ),
      N₀ ≤ D → (N₀ : ℝ) ^ 2 ≤ Real.logb 2 M → 0 < ε → ε ≤ 1 / 6 →
      ∃ E : Fin M → Matrix (Fin D) (Fin D) ℂ,
        (∀ i, ShadowTomography.UpperBound.IsEffect (E i)) ∧
        ∀ (k : ℕ) (Ω : Type) [Fintype Ω]
          (P : ShadowTomography.QuantumLB.POVM Ω (Fin k → Fin D)) (b : Ω → Fin M → ℝ),
          (∀ ρ : Matrix (Fin D) (Fin D) ℂ, WildeQIT.IsDensityOperator ρ →
            (2 / 3 : ℝ) ≤ P.prob (ShadowTomography.ClassicalLB.tensorPow ρ k)
              (fun ω => ∀ i, |b ω i - ((E i) * ρ).trace.re| ≤ ε)) →
          c * min ((D : ℝ) ^ 2) (Real.logb 2 M) / ε ^ 2 ≤ (k : ℝ) := by
  obtain ⟨c₀, hc1, hc2, N₁, hN₁⟩ := heq2
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log c₀ := ⟨_, rfl⟩
  have hL0 : 0 < L := hLdef ▸ Real.log_pos hc1
  have hL1 : L < 1 := by
    rw [hLdef]
    have := Real.log_lt_sub_one_of_pos (by linarith) (by linarith : c₀ ≠ 1)
    linarith
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁ : ℝ, c₁ = min (L / 16) (1 / 4) := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁def]; exact lt_min (by positivity) (by norm_num)
  have hc₁L : c₁ ≤ L / 16 := hc₁def ▸ min_le_left _ _
  have hc₁4 : c₁ ≤ 1 / 4 := hc₁def ▸ min_le_right _ _
  have hc₁32 : 2 ≤ c₁ * (32 / L) := by
    rw [hc₁def]
    rcases min_cases (L / 16) (1 / 4) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; field_simp; norm_num
    · rw [h]
      have : 32 < 32 / L := by rw [lt_div_iff₀ hL0]; linarith
      linarith
  refine ⟨c₁ / 48, by positivity, ⌈32 / L⌉₊ + N₁ + 8, ?_⟩
  intro D M ε hD hM hε hε6
  have hDc : ⌈32 / L⌉₊ ≤ D := by omega
  have hDL : 32 / L ≤ (D : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hDc)
  have hD8 : 8 ≤ D := by omega
  have hDr : (8 : ℝ) ≤ D := by exact_mod_cast hD8
  have hDpos : (0 : ℝ) < D := by linarith
  have hDLr : 32 ≤ L * D := by rw [div_le_iff₀ hL0] at hDL; linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = 2 * (D / 2) := ⟨_, rfl⟩
  have hnD : n ≤ D := by omega
  have hnD1 : D ≤ n + 1 := by omega
  have hnev : Even n := ⟨D / 2, by omega⟩
  have hnN : N₁ ≤ n := by omega
  have hn7 : 7 ≤ n := by omega
  have hnr : (7 : ℝ) ≤ n := by exact_mod_cast hn7
  have hnpos : (0 : ℝ) < n := by linarith
  have hnD1r : (D : ℝ) ≤ n + 1 := by exact_mod_cast hnD1
  obtain ⟨Pf, hPh, hPo⟩ := hN₁ n hnN hnev
  -- the logarithmic size of the family
  have hN0r : (32 / L : ℝ) ≤ ((⌈32 / L⌉₊ + N₁ + 8 : ℕ) : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : ⌈32 / L⌉₊ ≤ ⌈32 / L⌉₊ + N₁ + 8))
  have hN0one : (1 : ℝ) ≤ ((⌈32 / L⌉₊ + N₁ + 8 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ ⌈32 / L⌉₊ + N₁ + 8)
  have hlogbM : 32 / L ≤ Real.logb 2 M := by
    exact le_trans hN0r (le_trans (t19_le_sq _ hN0one) hM)
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, Real.logb_zero] at hlogbM
    have : 0 < 32 / L := by positivity
    linarith
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM0
  have hx : Real.log (c₀ ^ (n ^ 2)) = (n : ℝ) ^ 2 * L := by
    rw [Real.log_pow, hLdef]; push_cast; ring
  have hn2L : 31 ≤ (n : ℝ) ^ 2 * L := t19_nL n D L hL0 hL1 hDLr hnD1r hnr
  have hx2 : (2 : ℝ) ≤ c₀ ^ (n ^ 2) := by
    have h2 : Real.log 2 < Real.log (c₀ ^ (n ^ 2)) := by
      rw [hx]; have := Real.log_two_lt_d9; linarith
    have hpos : 0 < c₀ ^ (n ^ 2) := by positivity
    exact ((Real.log_lt_log_iff (by norm_num) hpos).mp h2).le
  have hKx : c₀ ^ (n ^ 2) / 2 ≤ (⌊c₀ ^ (n ^ 2)⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (c₀ ^ (n ^ 2))
    linarith
  have hK1 : (1 : ℝ) ≤ ⌊c₀ ^ (n ^ 2)⌋₊ := by linarith
  have hlogK : 2 * c₁ * (D : ℝ) ^ 2 ≤ Real.log ⌊c₀ ^ (n ^ 2)⌋₊ := by
    have h1 : Real.log (c₀ ^ (n ^ 2) / 2) ≤ Real.log ⌊c₀ ^ (n ^ 2)⌋₊ :=
      Real.log_le_log (by positivity) hKx
    rw [Real.log_div (by positivity) (by norm_num), hx] at h1
    have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have := t19_logK_arith n D L c₁ hL0 hc₁L hDLr hDr hnD1r hnr hl2
    linarith
  have hlogM : 2 * c₁ * Real.logb 2 M ≤ Real.log M := by
    have hl2 := Real.log_two_gt_d9
    have hlb : Real.logb 2 M * Real.log 2 = Real.log M := by
      rw [Real.logb, div_mul_cancel₀ _ (by positivity)]
    have hb0 : 0 ≤ Real.logb 2 M := le_trans (by positivity) hlogbM
    have h1 : c₁ * Real.logb 2 M ≤ 1 / 4 * Real.logb 2 M := mul_le_mul_of_nonneg_right hc₁4 hb0
    have h2 : Real.logb 2 M * (1 / 2) ≤ Real.logb 2 M * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) hb0
    linarith
  obtain ⟨Nf, hNf⟩ : ∃ Nf : ℕ, Nf = min ⌊c₀ ^ (n ^ 2)⌋₊ M := ⟨_, rfl⟩
  have hNfK : Nf ≤ ⌊c₀ ^ (n ^ 2)⌋₊ := hNf ▸ min_le_left _ _
  have hNfM : Nf ≤ M := hNf ▸ min_le_right _ _
  set m := min ((D : ℝ) ^ 2) (Real.logb 2 M) with hm
  have hm1 : m ≤ (D : ℝ) ^ 2 := min_le_left _ _
  have hm2 : m ≤ Real.logb 2 M := min_le_right _ _
  have hm32 : 32 / L ≤ m := by
    exact le_min (le_trans hDL (t19_le_sq _ (by linarith))) hlogbM
  have hc₁m : 2 ≤ c₁ * m := le_trans hc₁32 (mul_le_mul_of_nonneg_left hm32 hc₁0.le)
  have hNf1 : (1 : ℝ) ≤ Nf := by
    rcases min_choice ⌊c₀ ^ (n ^ 2)⌋₊ M with h | h <;> rw [hNf, h] <;> assumption
  have hlogNf : 2 * c₁ * m ≤ Real.log Nf := by
    rcases min_choice ⌊c₀ ^ (n ^ 2)⌋₊ M with h | h
    · rw [hNf, h]
      exact le_trans (mul_le_mul_of_nonneg_left hm1 (by positivity)) hlogK
    · rw [hNf, h]
      exact le_trans (mul_le_mul_of_nonneg_left hm2 (by positivity)) hlogM
  -- the projectors and states
  set Pt : Fin Nf → Matrix (Fin D) (Fin D) ℂ :=
    fun j => t19_emb hnD (Pf (Fin.castLE hNfK j)) with hPtdef
  have hPtH : ∀ j, (Pt j).IsHermitian := fun j => t19_emb_herm hnD _ (hPh _).1
  have hPtI : ∀ j, Pt j * Pt j = Pt j := by
    intro j; simp only [hPtdef]; rw [t19_emb_mul, (hPh _).2.1]
  have hPtT : ∀ j, (Pt j).trace = ((n : ℝ) / 2 : ℝ) := by
    intro j; simp only [hPtdef]; rw [t19_emb_trace, (hPh _).2.2]; push_cast; ring
  have hPtP : ∀ j, (Pt j).PosSemidef ∧ (1 - Pt j).PosSemidef :=
    fun j => t19_proj_psd _ (hPtH j) (hPtI j)
  refine ⟨fun i => if h : i.val < Nf then Pt ⟨i.val, h⟩ else 0, ?_, ?_⟩
  · intro i
    by_cases h : i.val < Nf
    · simp only [h, dif_pos]
      exact hPtP _
    · simp only [h, dif_neg, not_false_eq_true]
      refine ⟨Matrix.PosSemidef.zero, ?_⟩
      rw [sub_zero]; exact Matrix.PosSemidef.one
  intro k Ω _ P b hP
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 - 6 * ε) / D := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = 12 * ε / n := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; apply div_nonneg <;> linarith
  have hv0 : 0 < v := by rw [hv]; positivity
  have huD : u * D = 1 - 6 * ε := by rw [hu]; field_simp
  have hvn : v * ((n : ℝ) / 2) = 6 * ε := by rw [hv]; field_simp; ring
  set σ : Fin Nf → Matrix (Fin D) (Fin D) ℂ := fun j => t19_sig (Pt j) u v with hσdef
  have hA2 : ∀ j l, (Pt j * σ l).trace = ((u * ((n : ℝ) / 2) : ℝ) : ℂ)
      + (v : ℂ) * (Pt j * Pt l).trace := by
    intro j l
    simp only [hσdef]
    rw [t19_trace_mul_sig, hPtT]; push_cast; ring
  have hA1 : ∀ j, (σ j).trace = ((1 : ℝ) : ℂ) := by
    intro j
    have := t19_trace_mul_sig (1 : Matrix (Fin D) (Fin D) ℂ) (Pt j) u v
    rw [Matrix.one_mul, Matrix.one_mul, Matrix.trace_one, hPtT, Fintype.card_fin] at this
    simp only [hσdef]
    rw [this]
    have e : (1 : ℝ) = u * D + v * ((n : ℝ) / 2) := by rw [huD, hvn]; ring
    rw [e]; push_cast; ring
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = u * 1 + v * (u * ((n : ℝ) / 2) + v * ((n : ℝ) / 2)) := ⟨_, rfl⟩
  have hA3 : ∀ j, (σ j * σ j).trace = (s : ℂ) := by
    intro j
    have h1 : (σ j * σ j).trace = (u : ℂ) * (σ j).trace + (v : ℂ) * (σ j * Pt j).trace := by
      simp only [hσdef]; exact t19_trace_mul_sig _ _ u v
    rw [h1, hA1, Matrix.trace_mul_comm, hA2, hPtI, hPtT, hs]
    push_cast; ring
  have hs0 : 0 < s := by
    rw [hs]
    have h1 : 0 < v * ((n : ℝ) / 2) := by positivity
    have h2 : 0 ≤ u * ((n : ℝ) / 2) := by positivity
    have h3 : 0 < v * (u * ((n : ℝ) / 2) + v * ((n : ℝ) / 2)) := mul_pos hv0 (by linarith)
    linarith
  have hsD : s * D ≤ 1 + 48 * ε ^ 2 := t19_sD u v ε D n s hDpos hnpos hnD1r hnr huD hvn hv hs
  have hdens : ∀ j, WildeQIT.IsDensityOperator (σ j) := by
    intro j
    refine ⟨?_, ?_⟩
    · simp only [hσdef]; exact t19_sig_psd _ (hPtP j).1 u v hu0 hv0.le
    · rw [hA1]; simp
  have hEj : ∀ j : Fin Nf,
      (fun i : Fin M => if h : i.val < Nf then Pt ⟨i.val, h⟩ else 0)
        ⟨j.val, lt_of_lt_of_le j.2 hNfM⟩ = Pt j := by
    intro j
    simp only [j.2, dif_pos]
  have hself : ∀ j, (Pt j * σ j).trace.re = u * ((n : ℝ) / 2) + 6 * ε := by
    intro j
    rw [hA2, hPtI, hPtT, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re, hvn]
  have hother : ∀ j l, j ≠ l → (Pt j * σ l).trace.re ≤ u * ((n : ℝ) / 2) + 7 / 2 * ε := by
    intro j l hjl
    have hne : Fin.castLE hNfK j ≠ Fin.castLE hNfK l :=
      fun e => hjl (Fin.castLE_injective hNfK e)
    have h0 := hPo _ _ hne
    have hrho : (Pf (Fin.castLE hNfK j) *
        ShadowTomography.QuantumLB.rhoState (Pf (Fin.castLE hNfK l))).trace.re
        = 2 / n * (Pt j * Pt l).trace.re := by
      simp only [hPtdef]
      rw [t19_emb_mul, t19_emb_trace]
      simp only [ShadowTomography.QuantumLB.rhoState, Matrix.mul_smul, Matrix.trace_smul,
        smul_eq_mul]
      rw [show (2 : ℂ) / (n : ℂ) = ((2 / n : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    rw [hrho] at h0
    have h1 : 2 / n * (Pt j * Pt l).trace.re ≤ 7 / 12 := by
      have := (abs_le.mp h0).2; linarith
    rw [hA2, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
    have h2 : v * (Pt j * Pt l).trace.re = 6 * ε * (2 / n * (Pt j * Pt l).trace.re) := by
      rw [hv]; field_simp; ring
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 6 * ε)
    linarith
  have hcore := t19_core P (fun j => ShadowTomography.ClassicalLB.tensorPow (σ j) k)
    (fun j => t19_tp_herm _ (t19_sig_herm _ (hPtH j) u v) k) (s ^ k) (by positivity)
    (fun j => by
      rw [t19_tp_trace_mul, hA3, ← Complex.ofReal_pow, Complex.ofReal_re])
    (fun j ω => ∀ i, |b ω i - ((fun i : Fin M => if h : i.val < Nf then Pt ⟨i.val, h⟩ else 0) i
        * σ j).trace.re| ≤ ε)
    (by
      intro j l ω hj hl
      by_contra hjl
      have a1 := hj ⟨j.val, lt_of_lt_of_le j.2 hNfM⟩
      have a2 := hl ⟨j.val, lt_of_lt_of_le j.2 hNfM⟩
      rw [hEj] at a1 a2
      rw [hself] at a1
      have a3 := hother j l hjl
      have := (abs_le.mp a1); have := (abs_le.mp a2)
      linarith)
    (fun j => hP (σ j) (hdens j))
  simp only [Fintype.card_fin, Fintype.card_pi, Finset.prod_const, Finset.card_univ] at hcore
  push_cast at hcore
  have hfin : 4 / 9 * (Nf : ℝ) ≤ (1 + 48 * ε ^ 2) ^ k := by
    calc 4 / 9 * (Nf : ℝ) ≤ s ^ k * (D : ℝ) ^ k := hcore
      _ = (s * D) ^ k := by rw [mul_pow]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hsD k
  have hl := Real.log_le_log (by positivity) hfin
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hl
  have l1 : Real.log (1 + 48 * ε ^ 2) ≤ 48 * ε ^ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 48 * ε ^ 2 by positivity); linarith
  have l3 : -(5 / 4 : ℝ) ≤ Real.log (4 / 9) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 / 9 by norm_num)
    norm_num at this; linarith
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have m2 : (k : ℝ) * Real.log (1 + 48 * ε ^ 2) ≤ k * (48 * ε ^ 2) :=
    mul_le_mul_of_nonneg_left l1 hk0
  rw [div_le_iff₀ (by positivity)]
  linarith

open ShadowTomography.QuantumLB in
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ (D M : ℕ) (ε : ℝ),
      N₀ ≤ D → (N₀ : ℝ) ^ 2 ≤ Real.logb 2 M → 0 < ε → ε ≤ 1 / 6 →
      ∃ E : Fin M → Matrix (Fin D) (Fin D) ℂ, (∀ i, ShadowTomography.UpperBound.IsEffect (E i)) ∧
        ∀ (k : ℕ) (Ω : Type) [Fintype Ω]
          (P : POVM Ω (Fin k → Fin D)) (b : Ω → Fin M → ℝ),
          (∀ ρ : Matrix (Fin D) (Fin D) ℂ, WildeQIT.IsDensityOperator ρ →
            (2 / 3 : ℝ) ≤ P.prob (ShadowTomography.ClassicalLB.tensorPow ρ k)
              (fun ω => ∀ i, |b ω i - ((E i) * ρ).trace.re| ≤ ε)) →
          c * min ((D : ℝ) ^ 2) (Real.logb 2 M) / ε ^ 2 ≤ (k : ℝ) := by
  exact t19_main ShadowTomography.QuantumLB.eq_2
