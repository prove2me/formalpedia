-- Prove2me | solution 1 for ParamSDO.Transition.strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:48:32.886137+00:00
-- url     : https://prove2.me/submissions/12dbb685-5380-4f28-bc0d-331a921875af

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting

open ParamSDO.Transition Matrix MatrixOrder

lemma psdo_trace_mul_psd {ι : Type} [Fintype ι] [DecidableEq ι] {S X : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hX : X.PosSemidef) : 0 ≤ (S * X).trace ∧ ((S * X).trace = 0 → X * S = 0) := by
  obtain ⟨G, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hS.nonneg
  obtain ⟨H, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  simp only [star_eq_conjTranspose]
  have htr : (Gᴴ * G * (Hᴴ * H)).trace = ((G * Hᴴ) * (G * Hᴴ)ᴴ).trace := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [show Gᴴ * G * (Hᴴ * H) = Gᴴ * (G * Hᴴ * H) by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [htr]
  refine ⟨(posSemidef_self_mul_conjTranspose (G * Hᴴ)).trace_nonneg, fun h0 => ?_⟩
  have hz : G * Hᴴ = 0 := trace_mul_conjTranspose_self_eq_zero_iff.1 h0
  have hz' : H * Gᴴ = 0 := by
    have := congrArg conjTranspose hz
    simpa [conjTranspose_mul] using this
  calc Hᴴ * H * (Gᴴ * G) = Hᴴ * (H * Gᴴ) * G := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hz']; simp

/-- PD times nonzero PSD has positive trace. -/
lemma psdo_trace_pos {ι : Type} [Fintype ι] [DecidableEq ι] {S Z : Matrix ι ι ℝ}
    (hS : S.PosDef) (hZ : Z.PosSemidef) (hZ0 : Z ≠ 0) : 0 < (S * Z).trace := by
  obtain ⟨h0, h1⟩ := psdo_trace_mul_psd hS.posSemidef hZ
  refine lt_of_le_of_ne h0 fun h => hZ0 ?_
  have hZS := h1 h.symm
  have hu := hS.isUnit
  calc Z = Z * S * S⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det S).1 hu),
          Matrix.mul_one]
    _ = 0 := by rw [hZS, Matrix.zero_mul]

/-- Uniformly positive matrices (not necessarily symmetric). -/
def psdoUPos {ι : Type} [Fintype ι] (P : Matrix ι ι ℝ) : Prop :=
  ∃ δ > 0, ∀ v : ι → ℝ, δ * (v ⬝ᵥ v) ≤ v ⬝ᵥ P *ᵥ v

lemma psdo_quad_expand {ι : Type} [Fintype ι] (P : Matrix ι ι ℝ) (v : ι → ℝ) :
    v ⬝ᵥ P *ᵥ v = ∑ i, ∑ j, v i * P i j * v j := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma psdo_quad_bound {ι : Type} [Fintype ι] (E : Matrix ι ι ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hE : ∀ i j, |E i j| ≤ ε) (v : ι → ℝ) :
    |v ⬝ᵥ E *ᵥ v| ≤ ε * (Fintype.card ι) * (v ⬝ᵥ v) := by
  rw [psdo_quad_expand]
  calc |∑ i, ∑ j, v i * E i j * v j| ≤ ∑ i, ∑ j, |v i * E i j * v j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, (ε / 2 * v i ^ 2 + ε / 2 * v j ^ 2) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul]
        have h1 : |v i| * |v j| ≤ (v i ^ 2 + v j ^ 2) / 2 := by
          nlinarith [sq_nonneg (|v i| - |v j|), sq_abs (v i), sq_abs (v j)]
        have h2 := hE i j
        calc |v i| * |E i j| * |v j| = |E i j| * (|v i| * |v j|) := by ring
          _ ≤ ε * ((v i ^ 2 + v j ^ 2) / 2) :=
            mul_le_mul h2 h1 (by positivity) hε
          _ = _ := by ring
    _ = ε * (Fintype.card ι) * (v ⬝ᵥ v) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.mul_sum, dotProduct, pow_two]
        ring

lemma psdo_dot_self_nonneg {ι : Type} [Fintype ι] (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

lemma psdo_upos_isOpen {ι : Type} [Fintype ι] : IsOpen {P : Matrix ι ι ℝ | psdoUPos P} := by
  rw [isOpen_iff_mem_nhds]
  rintro P ⟨δ, hδ, hP⟩
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  set ε : ℝ := δ / (2 * (N + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hloc : ∀ i j, ∀ᶠ P' in nhds P, |P' i j - P i j| < ε := by
    intro i j
    have hc : Continuous fun P' : Matrix ι ι ℝ => |P' i j - P i j| := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
  have hall : ∀ᶠ P' in nhds P, ∀ i j, |P' i j - P i j| < ε :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hloc i j
  filter_upwards [hall] with P' hP'
  refine ⟨δ / 2, by positivity, fun v => ?_⟩
  have hb := psdo_quad_bound (P' - P) ε hε.le (fun i j => (hP' i j).le) v
  have hsplit : v ⬝ᵥ P' *ᵥ v = v ⬝ᵥ P *ᵥ v + v ⬝ᵥ (P' - P) *ᵥ v := by
    rw [Matrix.sub_mulVec, dotProduct_sub]; ring
  have hvv := psdo_dot_self_nonneg v
  have hεN : ε * N ≤ δ / 2 := by
    rw [hεdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have := hP v
  have h3 : ε * N * (v ⬝ᵥ v) ≤ δ / 2 * (v ⬝ᵥ v) := mul_le_mul_of_nonneg_right hεN hvv
  have h4 := neg_abs_le (v ⬝ᵥ (P' - P) *ᵥ v)
  rw [hsplit]
  nlinarith

lemma psdo_upos_convex {ι : Type} [Fintype ι] : Convex ℝ {P : Matrix ι ι ℝ | psdoUPos P} := by
  rintro P ⟨δ1, hδ1, h1⟩ Q ⟨δ2, hδ2, h2⟩ a c ha hc hac
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun v => ?_⟩
  have e : v ⬝ᵥ (a • P + c • Q) *ᵥ v = a * (v ⬝ᵥ P *ᵥ v) + c * (v ⬝ᵥ Q *ᵥ v) := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [e]
  have hvv := psdo_dot_self_nonneg v
  have := h1 v
  have := h2 v
  have hm1 : min δ1 δ2 * (v ⬝ᵥ v) ≤ δ1 * (v ⬝ᵥ v) :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hvv
  have hm2 : min δ1 δ2 * (v ⬝ᵥ v) ≤ δ2 * (v ⬝ᵥ v) :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hvv
  have k1 := mul_le_mul_of_nonneg_left (hm1.trans (h1 v)) ha
  have k2 := mul_le_mul_of_nonneg_left (hm2.trans (h2 v)) hc
  have k3 : min δ1 δ2 * (v ⬝ᵥ v) = a * (min δ1 δ2 * (v ⬝ᵥ v)) + c * (min δ1 δ2 * (v ⬝ᵥ v)) := by
    rw [← add_mul, hac, one_mul]
  linarith

lemma psdo_upos_posDef {ι : Type} [Fintype ι] {P : Matrix ι ι ℝ} (hH : P.IsHermitian)
    (hP : psdoUPos P) : P.PosDef := by
  obtain ⟨δ, hδ, h⟩ := hP
  refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have hxx : 0 < x ⬝ᵥ x :=
    lt_of_le_of_ne (psdo_dot_self_nonneg x) (fun h0 => hx (dotProduct_self_eq_zero.1 h0.symm))
  simp only [star_trivial]
  exact lt_of_lt_of_le (mul_pos hδ hxx) (h x)

lemma psdo_upos_smul_one_add {ι : Type} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}
    (hQ : Q.PosSemidef) {r : ℝ} (hr : 0 < r) : psdoUPos (r • (1 : Matrix ι ι ℝ) + Q) := by
  refine ⟨r, hr, fun v => ?_⟩
  have := hQ.dotProduct_mulVec_nonneg v
  simp only [star_trivial] at this
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  linarith

lemma psdo_functional_expand {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : Matrix ι ι ℝ →L[ℝ] ℝ) (Q : Matrix ι ι ℝ) :
    f Q = ∑ i, ∑ j, Q i j * f (single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Q]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : single i j (Q i j) = Q i j • single i j (1 : ℝ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul]

lemma psdo_herm_comb {ι : Type} [Fintype ι] {m : ℕ} (A : Fin m → Matrix ι ι ℝ)
    (M : Matrix ι ι ℝ) (hA : ∀ i, (A i).IsHermitian) (hM : M.IsHermitian) (y : Fin m → ℝ) :
    (M - ∑ i, y i • A i).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_sub, conjTranspose_sum, hM.eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_smul, (hA i).eq, star_trivial]

/-- Theorem of the alternative for strict LMI feasibility. -/
lemma psdo_alt {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (A : Fin m → Matrix ι ι ℝ)
    (M : Matrix ι ι ℝ) (hA : ∀ i, (A i).IsHermitian) (hM : M.IsHermitian)
    (h : ¬ ∃ y : Fin m → ℝ, (M - ∑ i, y i • A i).PosDef) :
    ∃ Z : Matrix ι ι ℝ, Z.PosSemidef ∧ Z ≠ 0 ∧ (∀ i, (A i * Z).trace = 0) ∧
      (M * Z).trace ≤ 0 := by
  set s := {P : Matrix ι ι ℝ | psdoUPos P}
  set t := Set.range fun y : Fin m → ℝ => M - ∑ i, y i • A i
  have ht : Convex ℝ t := by
    rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩ a c ha hc hac
    refine ⟨a • y + c • y', ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
      Finset.sum_add_distrib, smul_sub, ← Finset.smul_sum]
    have hM' : M = a • M + c • M := by rw [← add_smul, hac, one_smul]
    nth_rewrite 1 [hM']
    abel
  have hdisj : Disjoint s t := by
    rw [Set.disjoint_left]
    rintro P hPs ⟨y, rfl⟩
    refine h ⟨y, psdo_upos_posDef ?_ hPs⟩
    exact psdo_herm_comb A M hA hM y
  obtain ⟨f, u, hfs, hft⟩ :=
    geometric_hahn_banach_open psdo_upos_convex psdo_upos_isOpen ht hdisj
  -- (F1) f ≤ 0 on s
  have F1 : ∀ P ∈ s, f P ≤ 0 := by
    intro P hP
    by_contra hpos
    push_neg at hpos
    obtain ⟨δ, hδ, hPδ⟩ := hP
    set r : ℝ := (|u| + 1) / f P
    have hr : 0 < r := by positivity
    have hrs : r • P ∈ s := ⟨r * δ, by positivity, fun v => by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hPδ v) hr.le⟩
    have := hfs _ hrs
    rw [map_smul, smul_eq_mul, show r * f P = |u| + 1 by
      rw [div_mul_cancel₀ _ hpos.ne']] at this
    linarith [le_abs_self u]
  have hone : ∀ r : ℝ, 0 < r → r • (1 : Matrix ι ι ℝ) ∈ s := fun r hr => by
    have := psdo_upos_smul_one_add (PosSemidef.zero (n := ι) (R := ℝ)) hr
    rw [add_zero] at this
    exact this
  -- (F2) 0 ≤ u
  have F2 : 0 ≤ u := by
    by_contra hu
    push_neg at hu
    have h1 := F1 _ (hone 1 one_pos)
    rw [one_smul] at h1
    rcases h1.lt_or_eq with h1 | h1
    · have := hfs _ (hone (u / (2 * f 1)) (div_pos_of_neg_of_neg hu (by linarith)))
      have hval : f ((u / (2 * f 1)) • (1 : Matrix ι ι ℝ)) = u / 2 := by
        have := h1.ne; rw [map_smul, smul_eq_mul]; field_simp
      rw [hval] at this
      linarith
    · have := hfs _ (hone 1 one_pos)
      rw [one_smul, h1] at this
      linarith
  -- (F3) f ≤ 0 on PSD
  have F3 : ∀ Q : Matrix ι ι ℝ, Q.PosSemidef → f Q ≤ 0 := by
    intro Q hQ
    have hf1 : f 1 ≤ 0 := by simpa using F1 _ (hone 1 one_pos)
    by_contra hpos
    push_neg at hpos
    set r : ℝ := f Q / (2 * (|f 1| + 1))
    have hr : 0 < r := by positivity
    have := F1 _ (psdo_upos_smul_one_add hQ hr)
    rw [map_add, map_smul, smul_eq_mul] at this
    have hb : r * |f 1| < f Q := by
      have : r * (|f 1| + 1) = f Q / 2 := by
        simp only [r]; field_simp
      nlinarith [abs_nonneg (f 1)]
    have : r * f 1 ≥ - (r * |f 1|) := by
      rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_abs_le _) hr.le
    linarith
  -- (F4) f (A i) = 0
  have F4 : ∀ i, f (A i) = 0 := by
    intro i
    have key : ∀ r : ℝ, u ≤ f M - r * f (A i) := by
      intro r
      have := hft _ ⟨Pi.single i r, rfl⟩
      simpa [Pi.single_apply, map_sub, map_sum, ite_smul, Finset.sum_ite_eq'] using this
    by_contra hne
    have := key ((f M - u + 1) / f (A i))
    rw [div_mul_cancel₀ _ hne] at this
    linarith
  -- (F5) u ≤ f M
  have F5 : u ≤ f M := by
    have := hft _ ⟨0, rfl⟩
    simpa using this
  -- the matrix of `-f`
  let Z : Matrix ι ι ℝ := fun i j => -(f (single i j 1) + f (single j i 1)) / 2
  have hZsym : Z.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Z, star_trivial]
    ring
  have hZf : ∀ Q : Matrix ι ι ℝ, Q.IsHermitian → (Z * Q).trace = - f Q := by
    intro Q hQ
    have hQs : ∀ i j, Q j i = Q i j := fun i j => by
      have := congrFun (congrFun hQ i) j
      simpa using this
    have hswap : ∑ i, ∑ j, Q i j * f (single j i 1) = ∑ i, ∑ j, Q i j * f (single i j 1) := by
      rw [Finset.sum_comm]
      simp only [hQs]
    rw [psdo_functional_expand f Q]
    calc (Z * Q).trace = ∑ i, ∑ j, Z i j * Q j i := by simp [Matrix.trace, Matrix.mul_apply]
      _ = ∑ i, ∑ j, (-(1/2) * (Q i j * f (single i j 1)) - (1/2) * (Q i j * f (single j i 1))) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          simp only [Z, hQs]; ring
      _ = -(1/2) * (∑ i, ∑ j, Q i j * f (single i j 1))
            - (1/2) * (∑ i, ∑ j, Q i j * f (single j i 1)) := by
          simp only [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := by rw [hswap]; ring
  have hquad : ∀ v : ι → ℝ, v ⬝ᵥ Z *ᵥ v = (Z * vecMulVec v v).trace := by
    intro v
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct,
      mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hZpsd : Z.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg hZsym fun v => ?_
    have hvv : (vecMulVec v v).PosSemidef := by
      simpa using posSemidef_vecMulVec_self_star v
    simp only [star_trivial]
    rw [hquad, hZf _ hvv.isHermitian]
    linarith [F3 _ hvv]
  refine ⟨Z, hZpsd, fun hZ0 => ?_, fun i => ?_, ?_⟩
  · have e1 := hZf 1 isHermitian_one
    have e2 := hZf M hM
    rw [hZ0, Matrix.zero_mul, Matrix.trace_zero] at e1 e2
    have := hfs _ (hone 1 one_pos)
    rw [one_smul] at this
    linarith
  · rw [Matrix.trace_mul_comm, hZf _ (hA i), F4 i, neg_zero]
  · rw [Matrix.trace_mul_comm, hZf _ hM]
    linarith

lemma psdo_pair_add_smul {n : ℕ} (M X Z : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    pair M (X + t • Z) = pair M X + t * pair M Z := by
  unfold pair
  rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

lemma psdo_trace_comb_mul {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (y : Fin m → ℝ)
    (S Z : Matrix (Fin n) (Fin n) ℝ) :
    ((∑ i, y i • A i + S) * Z).trace = ∑ i, y i * (A i * Z).trace + (S * Z).trace := by
  simp only [Matrix.add_mul, Matrix.sum_mul, Matrix.trace_add, Matrix.trace_sum,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- A feasible point plus a PSD recession direction of negative cost forces `v = ⊥`. -/
lemma psdo_v_bot {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) (ϵ : ℝ) (X0 : Matrix (Fin n) (Fin n) ℝ)
    (hX0 : X0 ∈ Pfeas A b) (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosSemidef)
    (hAZ : ∀ i, pair (A i) Z = 0) (hκ : pair (C + ϵ • Cbar) Z < 0) :
    v A b C Cbar ϵ = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro y
  set κ := pair (C + ϵ • Cbar) Z
  set t : ℝ := max 0 ((pair (C + ϵ • Cbar) X0 - y + 1) / (-κ))
  have ht : 0 ≤ t := le_max_left _ _
  have hfeas : X0 + t • Z ∈ Pfeas A b :=
    ⟨hX0.1.add (hZ.smul ht), fun i => by rw [psdo_pair_add_smul, hX0.2 i, hAZ i, mul_zero,
      add_zero]⟩
  have hval : pair (C + ϵ • Cbar) (X0 + t • Z) < y := by
    rw [psdo_pair_add_smul]
    have h1 : (pair (C + ϵ • Cbar) X0 - y + 1) / (-κ) ≤ t := le_max_right _ _
    rw [div_le_iff₀ (by linarith)] at h1
    nlinarith
  calc v A b C Cbar ϵ ≤ ((pair (C + ϵ • Cbar) (X0 + t • Z) : ℝ) : EReal) :=
        iInf₂_le (X0 + t • Z) hfeas
    _ < y := by exact_mod_cast hval

lemma psdo_herm_C {n : ℕ} (C Cbar : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsHermitian)
    (hCbar : Cbar.IsHermitian) (ϵ : ℝ) : (C + ϵ • Cbar).IsHermitian :=
  hC.add (hCbar.smul (IsSelfAdjoint.all ϵ))

/-- Remark 1 (dual part): a strictly feasible dual solution exists at every `ϵ ∈ int 𝓔`. -/
lemma psdo_dual_slater {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h2 : Assumption2 A b C Cbar) :
    ∀ ϵ ∈ interior (domE A b C Cbar), ∃ p ∈ Dfeas A C Cbar ϵ, p.2.PosDef := by
  intro ϵ hϵ
  by_contra hno
  have hno' : ¬ ∃ y : Fin m → ℝ, (C + ϵ • Cbar - ∑ i, y i • A i).PosDef := by
    rintro ⟨y, hy⟩
    exact hno ⟨(y, C + ϵ • Cbar - ∑ i, y i • A i), ⟨add_sub_cancel _ _, hy.posSemidef⟩, hy⟩
  obtain ⟨Z, hZ, hZ0, hAZ, hCZ⟩ := psdo_alt A (C + ϵ • Cbar) hA (psdo_herm_C C Cbar hC hCbar ϵ) hno'
  obtain ⟨X0, hX0, -⟩ := h2.1
  obtain ⟨⟨y0, S0⟩, hD0, hS0⟩ := h2.2
  have hC0 : C = ∑ i, y0 i • A i + S0 := by
    have := hD0.1; simp only [zero_smul, add_zero] at this; exact this.symm
  have hpos : 0 < (C * Z).trace := by
    rw [hC0, psdo_trace_comb_mul]
    simp only [hAZ, mul_zero, Finset.sum_const_zero, zero_add]
    exact psdo_trace_pos hS0 hZ hZ0
  have hsplit : ∀ e : ℝ, ((C + e • Cbar) * Z).trace = (C * Z).trace + e * (Cbar * Z).trace := by
    intro e; rw [Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.trace_smul,
      smul_eq_mul]
  have hneg : ϵ * (Cbar * Z).trace < 0 := by
    have := hsplit ϵ; linarith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hϵ)
  set η : ℝ := r / (2 * (|ϵ| + 1))
  have hη : 0 < η := by positivity
  have hmem : ϵ + η * ϵ ∈ domE A b C Cbar := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_mul, abs_of_pos hη]
    have : η * (|ϵ| + 1) = r / 2 := by simp only [η]; field_simp
    nlinarith [abs_nonneg ϵ]
  have hκ : pair (C + (ϵ + η * ϵ) • Cbar) Z < 0 := by
    unfold pair
    rw [hsplit]
    have := hsplit ϵ
    nlinarith
  have hbot := psdo_v_bot A b C Cbar (ϵ + η * ϵ) X0 hX0 Z hZ hAZ hκ
  have := hmem
  unfold domE at this
  rw [Set.mem_setOf_eq, hbot] at this
  exact lt_irrefl _ this

lemma psdo_quad_smul {ι : Type} [Fintype ι] (P : Matrix ι ι ℝ) (r : ℝ) (v : ι → ℝ) :
    (r • v) ⬝ᵥ P *ᵥ (r • v) = r ^ 2 * (v ⬝ᵥ P *ᵥ v) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]; ring

/-- A positive definite matrix is uniformly positive. -/
lemma psdo_upos_of_posDef {ι : Type} [Fintype ι] {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    psdoUPos P := by
  set K : Set (ι → ℝ) := {v | v ⬝ᵥ v = 1}
  have hnorm : ∀ v : ι → ℝ, v ≠ 0 →
      (Real.sqrt (v ⬝ᵥ v))⁻¹ • v ∈ K ∧ Real.sqrt (v ⬝ᵥ v) ^ 2 = v ⬝ᵥ v ∧
        0 < Real.sqrt (v ⬝ᵥ v) := by
    intro v hv
    have hpos : 0 < v ⬝ᵥ v :=
      lt_of_le_of_ne (psdo_dot_self_nonneg v) (fun h0 => hv (dotProduct_self_eq_zero.1 h0.symm))
    have hs := Real.sq_sqrt hpos.le
    have hr := Real.sqrt_pos.2 hpos
    refine ⟨?_, hs, hr⟩
    show _ = _
    set r := Real.sqrt (v ⬝ᵥ v)
    clear_value r
    rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← hs]
    field_simp
  have hq : ∀ v : ι → ℝ, v ≠ 0 → v ⬝ᵥ P *ᵥ v = (v ⬝ᵥ v) *
      (((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) ⬝ᵥ P *ᵥ ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v)) := by
    intro v hv
    obtain ⟨-, hs, hr⟩ := hnorm v hv
    set r := Real.sqrt (v ⬝ᵥ v)
    clear_value r
    rw [psdo_quad_smul, ← hs]
    field_simp
  by_cases hK : K.Nonempty
  · have hKc : IsCompact K := by
      have hcl : IsClosed K := isClosed_eq (by fun_prop) continuous_const
      refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (-1 : ℝ)) (b := 1)).of_isClosed_subset
        hcl fun v hv => ?_
      intro i _
      have h1 : v i * v i ≤ v ⬝ᵥ v :=
        Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
          (Finset.mem_univ i)
      have hv1 : v ⬝ᵥ v = 1 := hv
      rw [hv1] at h1
      constructor <;> nlinarith
    have hcont : Continuous fun v : ι → ℝ => v ⬝ᵥ P *ᵥ v := by fun_prop
    obtain ⟨v0, hv0K, hmin⟩ := hKc.exists_isMinOn hK hcont.continuousOn
    have hv0 : v0 ≠ 0 := by
      rintro rfl
      have : (0 : ι → ℝ) ⬝ᵥ 0 = 1 := hv0K
      simp at this
    have hm : 0 < v0 ⬝ᵥ P *ᵥ v0 := by simpa using hP.dotProduct_mulVec_pos hv0
    refine ⟨_, hm, fun v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    · rw [hq v hv, mul_comm]
      exact mul_le_mul_of_nonneg_left (hmin (hnorm v hv).1) (psdo_dot_self_nonneg v)
  · refine ⟨1, one_pos, fun v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    · exact absurd ⟨_, (hnorm v hv).1⟩ hK

/-- `tr(S X) ≥ δ tr X` for `S` uniformly positive with constant `δ` and `X ⪰ 0`. -/
lemma psdo_trace_lower {ι : Type} [Fintype ι] [DecidableEq ι] {S X : Matrix ι ι ℝ}
    (hS : S.IsHermitian) {δ : ℝ} (hδ : ∀ v : ι → ℝ, δ * (v ⬝ᵥ v) ≤ v ⬝ᵥ S *ᵥ v)
    (hX : X.PosSemidef) : δ * X.trace ≤ (S * X).trace := by
  have hSd : (S - δ • (1 : Matrix ι ι ℝ)).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg
      (hS.sub (isHermitian_one.smul (IsSelfAdjoint.all δ))) fun v => ?_
    simp only [star_trivial]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
    linarith [hδ v]
  have := (psdo_trace_mul_psd hSd hX).1
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    smul_eq_mul] at this
  linarith

lemma psdo_entry_le_trace {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℝ}
    (hX : X.PosSemidef) (i j : ι) : |X i j| ≤ X.trace := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  simp only [star_eq_conjTranspose, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    conjTranspose_apply, star_trivial]
  calc |∑ k, B k i * B k j| ≤ ∑ k, |B k i * B k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (B k i * B k i + B k j * B k j) / 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        nlinarith [sq_nonneg (|B k i| - |B k j|), abs_mul_abs_self (B k i),
          abs_mul_abs_self (B k j), abs_nonneg (B k i), abs_nonneg (B k j)]
    _ = (∑ k, B k i * B k i + ∑ k, B k j * B k j) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ ∑ l, ∑ k, B k l * B k l := by
        have hnn : ∀ l, 0 ≤ ∑ k, B k l * B k l := fun l =>
          Finset.sum_nonneg fun k _ => mul_self_nonneg (B k l)
        by_cases hij : i = j
        · subst hij
          have := Finset.single_le_sum (f := fun l => ∑ k, B k l * B k l)
            (fun l _ => hnn l) (Finset.mem_univ i)
          linarith
        · have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun l => ∑ k, B k l * B k l)
            (Finset.subset_univ {i, j}) (fun l _ _ => hnn l)
          rw [Finset.sum_pair hij] at this
          linarith [hnn i, hnn j]

lemma psdo_isClosed_psd {ι : Type} [Fintype ι] :
    IsClosed {X : Matrix ι ι ℝ | X.PosSemidef} := by
  have : {X : Matrix ι ι ℝ | X.PosSemidef} =
      {X | Xᴴ = X} ∩ ⋂ v : ι → ℝ, {X | 0 ≤ star v ⬝ᵥ X *ᵥ v} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact posSemidef_iff_dotProduct_mulVec
  rw [this]
  refine IsClosed.inter (isClosed_eq (by fun_prop) continuous_id) (isClosed_iInter fun v => ?_)
  exact isClosed_le continuous_const (by fun_prop)

lemma psdo_isCompact_of_bound {ι : Type} [Fintype ι] {K : Set (Matrix ι ι ℝ)}
    (hK : IsClosed K) (R : ℝ) (hR : ∀ X ∈ K, ∀ i j, |X i j| ≤ R) : IsCompact K := by
  refine (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_Icc (a := -R) (b := R)).of_isClosed_subset hK fun X hX => ?_
  intro i _ j _
  exact abs_le.1 (hR X hX i j)

lemma psdo_pair_split {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) (ϵ : ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin m → ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (hX : X ∈ Pfeas A b)
    (hD : (y, S) ∈ Dfeas A C Cbar ϵ) :
    pair (C + ϵ • Cbar) X = b ⬝ᵥ y + (S * X).trace := by
  unfold pair
  rw [← hD.1]
  simp only [Matrix.add_mul, Matrix.sum_mul, Matrix.trace_add, Matrix.trace_sum,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hX.2 i
  unfold pair at this
  rw [this, mul_comm]

lemma psdo_pair_continuous {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Continuous fun X : Matrix (Fin n) (Fin n) ℝ => pair M X := by
  unfold pair; fun_prop

lemma psdo_Pfeas_closed {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) :
    IsClosed (Pfeas A b) := by
  have : Pfeas A b = {X | X.PosSemidef} ∩ ⋂ i, {X | pair (A i) X = b i} := by
    ext X; simp [Pfeas]
  rw [this]
  exact psdo_isClosed_psd.inter (isClosed_iInter fun i =>
    isClosed_eq (psdo_pair_continuous _) continuous_const)

/-- Primal attainment at `ϵ ∈ int 𝓔`, with a compact sublevel set. -/
lemma psdo_primal {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h2 : Assumption2 A b C Cbar) (ϵ : ℝ) (hϵ : ϵ ∈ interior (domE A b C Cbar)) :
    ∃ Xs ∈ Pfeas A b, (∀ X ∈ Pfeas A b, pair (C + ϵ • Cbar) Xs ≤ pair (C + ϵ • Cbar) X) ∧
      v A b C Cbar ϵ = ((pair (C + ϵ • Cbar) Xs : ℝ) : EReal) ∧
      IsCompact (Pstar A b C Cbar ϵ) := by
  obtain ⟨⟨y1, S1⟩, hD1, hS1⟩ := psdo_dual_slater A b C Cbar hA hC hCbar h2 ϵ hϵ
  obtain ⟨δ1, hδ1, hu1⟩ := psdo_upos_of_posDef hS1
  obtain ⟨X0, hX0, -⟩ := h2.1
  set c0 := pair (C + ϵ • Cbar) X0
  set K := {X | X ∈ Pfeas A b ∧ pair (C + ϵ • Cbar) X ≤ c0}
  have hKcl : IsClosed K :=
    (psdo_Pfeas_closed A b).inter (isClosed_le (psdo_pair_continuous _) continuous_const)
  have hKc : IsCompact K := by
    refine psdo_isCompact_of_bound hKcl ((c0 - b ⬝ᵥ y1) / δ1) fun X hX i j => ?_
    have hsp := psdo_pair_split A b C Cbar ϵ X y1 S1 hX.1 hD1
    have hlow := psdo_trace_lower hS1.isHermitian hu1 hX.1.1
    refine (psdo_entry_le_trace hX.1.1 i j).trans ?_
    rw [le_div_iff₀ hδ1]
    linarith [hX.2]
  obtain ⟨Xs, hXsK, hmin⟩ := hKc.exists_isMinOn ⟨X0, hX0, le_rfl⟩
    (psdo_pair_continuous _).continuousOn
  have hall : ∀ X ∈ Pfeas A b, pair (C + ϵ • Cbar) Xs ≤ pair (C + ϵ • Cbar) X := by
    intro X hX
    by_cases hXc : pair (C + ϵ • Cbar) X ≤ c0
    · exact hmin ⟨hX, hXc⟩
    · push_neg at hXc; linarith [hXsK.2]
  have hv : v A b C Cbar ϵ = ((pair (C + ϵ • Cbar) Xs : ℝ) : EReal) := by
    apply le_antisymm (iInf₂_le Xs hXsK.1)
    exact le_iInf₂ fun X hX => by exact_mod_cast hall X hX
  refine ⟨Xs, hXsK.1, hall, hv, ?_⟩
  have hPs : Pstar A b C Cbar ϵ =
      {X | X ∈ Pfeas A b ∧ pair (C + ϵ • Cbar) X = pair (C + ϵ • Cbar) Xs} := by
    ext X; simp only [Pstar, hv, Set.mem_setOf_eq, EReal.coe_eq_coe_iff]
  rw [hPs]
  refine hKc.of_isClosed_subset ((psdo_Pfeas_closed A b).inter
    (isClosed_eq (psdo_pair_continuous _) continuous_const)) fun X hX => ⟨hX.1, ?_⟩
  rw [hX.2]; exact hXsK.2

/-- Block-diagonal embedding `diag(P, d)` on `Fin n ⊕ Unit`. -/
def psdoBlk {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (d : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks P 0 0 (fun _ _ => d)

lemma psdo_blk_herm {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.IsHermitian) (d : ℝ) :
    (psdoBlk P d).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  rcases i with i | i <;> rcases j with j | j <;>
    simp [psdoBlk, Matrix.fromBlocks, Matrix.of_apply]
  simpa using hP.apply i j

lemma psdo_blk_comb {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (d : ℝ) (y : Fin m → ℝ) :
    psdoBlk M d - ∑ i, y i • psdoBlk (A i) (-b i) =
      psdoBlk (M - ∑ i, y i • A i) (b ⬝ᵥ y + d) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [psdoBlk, Matrix.fromBlocks, Matrix.of_apply, Matrix.sum_apply, dotProduct, mul_comm]
  ring

lemma psdo_blk_posDef {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} {d : ℝ}
    (h : (psdoBlk P d).PosDef) : P.PosDef ∧ 0 < d := by
  constructor
  · have := h.submatrix (e := (Sum.inl : Fin n → Fin n ⊕ Unit)) Sum.inl_injective
    convert this using 1
    ext i j; simp [psdoBlk, Matrix.fromBlocks, Matrix.of_apply]
  · have := h.diag_pos (i := Sum.inr ())
    simpa [psdoBlk, Matrix.fromBlocks] using this

lemma psdo_blk_trace {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (d : ℝ)
    (W : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ) :
    (psdoBlk P d * W).trace = (P * W.submatrix Sum.inl Sum.inl).trace +
      d * W (Sum.inr ()) (Sum.inr ()) := by
  simp [psdoBlk, Matrix.fromBlocks, Matrix.of_apply, Matrix.trace, Matrix.mul_apply, Fintype.sum_sum_type]

/-- Near-optimal strictly feasible dual solutions exist (zero duality gap). -/
lemma psdo_dual_strict {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (ϵ : ℝ) (y1 : Fin m → ℝ) (S1 : Matrix (Fin n) (Fin n) ℝ)
    (hD1 : (y1, S1) ∈ Dfeas A C Cbar ϵ) (hS1 : S1.PosDef)
    (p : ℝ) (hp : ∀ X ∈ Pfeas A b, p ≤ pair (C + ϵ • Cbar) X) (δ : ℝ) (hδ : 0 < δ) :
    ∃ y : Fin m → ℝ, (C + ϵ • Cbar - ∑ i, y i • A i).PosDef ∧ p - δ < b ⬝ᵥ y := by
  by_contra hno
  have hno' : ¬ ∃ y : Fin m → ℝ,
      (psdoBlk (C + ϵ • Cbar) (-(p - δ)) - ∑ i, y i • psdoBlk (A i) (-b i)).PosDef := by
    rintro ⟨y, hy⟩
    rw [psdo_blk_comb] at hy
    obtain ⟨h1, h2⟩ := psdo_blk_posDef hy
    exact hno ⟨y, h1, by linarith⟩
  obtain ⟨W, hW, hW0, hAW, hMW⟩ := psdo_alt (fun i => psdoBlk (A i) (-b i))
    (psdoBlk (C + ϵ • Cbar) (-(p - δ))) (fun i => psdo_blk_herm (hA i) _)
    (psdo_blk_herm (psdo_herm_C C Cbar hC hCbar ϵ) _) hno'
  set Z := W.submatrix Sum.inl Sum.inl
  set z := W (Sum.inr ()) (Sum.inr ())
  have hZ : Z.PosSemidef := hW.submatrix _
  have hz : 0 ≤ z := hW.diag_nonneg
  have hAZ : ∀ i, (A i * Z).trace = b i * z := by
    intro i; have := hAW i; simp only [psdo_blk_trace] at this; linarith
  have hCZ : ((C + ϵ • Cbar) * Z).trace ≤ (p - δ) * z := by
    have := hMW; rw [psdo_blk_trace] at this; linarith
  rcases hz.lt_or_eq with hz | hz
  · -- a primal feasible point with value below `p`
    have hX : z⁻¹ • Z ∈ Pfeas A b := by
      refine ⟨hZ.smul (inv_nonneg.2 hz.le), fun i => ?_⟩
      unfold pair
      rw [Matrix.mul_smul, Matrix.trace_smul, hAZ i, smul_eq_mul]
      field_simp
    have := hp _ hX
    unfold pair at this
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at this
    have h3 : z⁻¹ * ((C + ϵ • Cbar) * Z).trace ≤ p - δ := by
      rw [inv_mul_le_iff₀ hz]; linarith
    linarith
  · -- a recession direction contradicting dual strict feasibility
    have hZ0 : Z ≠ 0 := by
      intro hZ0
      apply hW0
      obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hW.nonneg
      have htr : W.trace = 0 := by
        have e : W.trace = Z.trace + z := by
          simp [Matrix.trace, Fintype.sum_sum_type, Z, z]
        rw [e, hZ0, ← hz]; simp
      rw [hB, star_eq_conjTranspose] at htr ⊢
      rw [trace_conjTranspose_mul_self_eq_zero_iff.1 htr]; simp
    have hpos : 0 < ((C + ϵ • Cbar) * Z).trace := by
      rw [← hD1.1, psdo_trace_comb_mul]
      simp only [hAZ, ← hz, mul_zero, Finset.sum_const_zero, zero_add]
      exact psdo_trace_pos hS1 hZ hZ0
    rw [← hz, mul_zero] at hCZ
    linarith

/-- Entry bound on dual slacks with objective at least `c`, via `X0 ≻ 0`. -/
lemma psdo_dual_bound {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) (ϵ : ℝ) (X0 : Matrix (Fin n) (Fin n) ℝ)
    (hX0 : X0 ∈ Pfeas A b) {δ0 : ℝ} (hδ0 : 0 < δ0)
    (hu0 : ∀ v : Fin n → ℝ, δ0 * (v ⬝ᵥ v) ≤ v ⬝ᵥ X0 *ᵥ v) (c : ℝ)
    (y : Fin m → ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (hD : (y, S) ∈ Dfeas A C Cbar ϵ)
    (hc : c ≤ b ⬝ᵥ y) :
    ∀ i j, |S i j| ≤ (pair (C + ϵ • Cbar) X0 - c) / δ0 := by
  intro i j
  have hsp := psdo_pair_split A b C Cbar ϵ X0 y S hX0 hD
  have hlow := psdo_trace_lower hX0.1.isHermitian hu0 hD.2
  rw [Matrix.trace_mul_comm] at hlow
  refine (psdo_entry_le_trace hD.2 i j).trans ?_
  rw [le_div_iff₀ hδ0]
  linarith

lemma psdo_strong_duality {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    ∀ ϵ ∈ interior (domE A b C Cbar),
      (Pstar A b C Cbar ϵ).Nonempty ∧ IsCompact (Pstar A b C Cbar ϵ) ∧
        (Dstar A b C Cbar ϵ).Nonempty ∧ IsCompact (Dstar A b C Cbar ϵ) := by
  intro ϵ hϵ
  obtain ⟨Xs, hXs, hall, hv, hPc⟩ := psdo_primal A b C Cbar hA hC hCbar h2 ϵ hϵ
  set C' := C + ϵ • Cbar
  set p := pair C' Xs
  obtain ⟨⟨y1, S1⟩, hD1, hS1⟩ := psdo_dual_slater A b C Cbar hA hC hCbar h2 ϵ hϵ
  obtain ⟨X0, hX0, hX0pd⟩ := h2.1
  obtain ⟨δ0, hδ0, hu0⟩ := psdo_upos_of_posDef hX0pd
  have hstrict := psdo_dual_strict A b C Cbar hA hC hCbar ϵ y1 S1 hD1 hS1 p hall
  -- left inverse of `y ↦ ∑ yᵢ Aᵢ`
  set T := Fintype.linearCombination ℝ A
  have hTinj : Function.Injective T :=
    (linearIndependent_iff_injective_fintypeLinearCombination).1 h1
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective T (LinearMap.ker_eq_bot.2 hTinj)
  have hgc : Continuous g := LinearMap.continuous_of_finiteDimensional g
  have hgT : ∀ y, g (∑ i, y i • A i) = y := fun y => by
    have := LinearMap.congr_fun hg y
    simpa [T, Fintype.linearCombination_apply] using this
  set c := p - 1
  set R0 := (pair C' X0 - c) / δ0
  set Ks := {S : Matrix (Fin n) (Fin n) ℝ | S.PosSemidef ∧ ∀ i j, |S i j| ≤ R0}
  have hKcl : IsClosed Ks := by
    have : Ks = {S : Matrix (Fin n) (Fin n) ℝ | S.PosSemidef} ∩
        ⋂ i, ⋂ j, {S : Matrix (Fin n) (Fin n) ℝ | |S i j| ≤ R0} := by
      ext S; simp [Ks]
    rw [this]
    exact psdo_isClosed_psd.inter (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (by fun_prop) continuous_const)
  have hKs : IsCompact Ks := psdo_isCompact_of_bound hKcl R0 fun S hS => hS.2
  set Dc := {y : Fin m → ℝ | (C' - ∑ i, y i • A i).PosSemidef ∧ c ≤ b ⬝ᵥ y}
  have hDcl : IsClosed Dc := by
    have hcont : Continuous fun y : Fin m → ℝ => C' - ∑ i, y i • A i := by fun_prop
    have : Dc = (fun y : Fin m → ℝ => C' - ∑ i, y i • A i) ⁻¹'
        {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} ∩ {y | c ≤ b ⬝ᵥ y} := rfl
    rw [this]
    exact (psdo_isClosed_psd.preimage hcont).inter
      (isClosed_le continuous_const (continuous_const.dotProduct continuous_id))
  have hDfe : ∀ y : Fin m → ℝ, (y, C' - ∑ i, y i • A i) ∈ Dfeas A C Cbar ϵ ↔
      (C' - ∑ i, y i • A i).PosSemidef := fun y =>
    ⟨fun h => h.2, fun h => ⟨add_sub_cancel _ _, h⟩⟩
  have hDc : IsCompact Dc := by
    have hcg : Continuous fun S : Matrix (Fin n) (Fin n) ℝ => g (C' - S) :=
      hgc.comp (continuous_const.sub continuous_id)
    refine (hKs.image hcg).of_isClosed_subset hDcl
      fun y hy => ⟨C' - ∑ i, y i • A i, ⟨hy.1, psdo_dual_bound A b C Cbar ϵ X0 hX0 hδ0 hu0 c y
        _ ((hDfe y).2 hy.1) hy.2⟩, ?_⟩
    simp [hgT]
  obtain ⟨y₁, hy₁pd, hy₁⟩ := hstrict 1 one_pos
  obtain ⟨ys, hysD, hmax⟩ := hDc.exists_isMaxOn ⟨y₁, hy₁pd.posSemidef, hy₁.le⟩
    (continuous_const.dotProduct continuous_id).continuousOn
  have hge : p ≤ b ⬝ᵥ ys := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨yd, hydpd, hyd⟩ := hstrict (min 1 (p - b ⬝ᵥ ys)) (lt_min one_pos (by linarith))
    have hyd' : b ⬝ᵥ yd ≤ b ⬝ᵥ ys :=
      hmax ⟨hydpd.posSemidef, by linarith [min_le_left 1 (p - b ⬝ᵥ ys)]⟩
    linarith [min_le_right 1 (p - b ⬝ᵥ ys)]
  have hle : b ⬝ᵥ ys ≤ p := by
    have hsp := psdo_pair_split A b C Cbar ϵ Xs ys _ hXs ((hDfe ys).2 hysD.1)
    linarith [(psdo_trace_mul_psd hysD.1 hXs.1).1]
  have hDs : Dstar A b C Cbar ϵ = {q | q ∈ Dfeas A C Cbar ϵ ∧ b ⬝ᵥ q.1 = p} := by
    ext q; simp only [Dstar, hv, Set.mem_setOf_eq, EReal.coe_eq_coe_iff]
  refine ⟨⟨Xs, hXs, hv.symm⟩, hPc, ⟨(ys, C' - ∑ i, ys i • A i), ?_⟩, ?_⟩
  · rw [hDs]; exact ⟨(hDfe ys).2 hysD.1, le_antisymm hle hge⟩
  · rw [hDs]
    have hcl : IsClosed {q : (Fin m → ℝ) × Matrix (Fin n) (Fin n) ℝ |
        q ∈ Dfeas A C Cbar ϵ ∧ b ⬝ᵥ q.1 = p} := by
      refine IsClosed.inter (IsClosed.inter (isClosed_eq (by fun_prop) continuous_const)
        (psdo_isClosed_psd.preimage continuous_snd)) (isClosed_eq (by fun_prop) continuous_const)
    refine (hDc.prod hKs).of_isClosed_subset hcl fun q hq => ?_
    have hS : q.2 = C' - ∑ i, q.1 i • A i := eq_sub_of_add_eq' hq.1.1
    have hqD : (q.1, q.2) ∈ Dfeas A C Cbar ϵ := hq.1
    refine ⟨⟨by rw [← hS]; exact hq.1.2, by linarith [hq.2]⟩, hq.1.2,
      psdo_dual_bound A b C Cbar ϵ X0 hX0 hδ0 hu0 c q.1 q.2 hqD (by linarith [hq.2])⟩

theorem solution {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    ∀ ϵ ∈ interior (domE A b C Cbar),
      (Pstar A b C Cbar ϵ).Nonempty ∧ IsCompact (Pstar A b C Cbar ϵ) ∧
        (Dstar A b C Cbar ϵ).Nonempty ∧ IsCompact (Dstar A b C Cbar ϵ) :=
  psdo_strong_duality A b C Cbar hA hC hCbar h1 h2
