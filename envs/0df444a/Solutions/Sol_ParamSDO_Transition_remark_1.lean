-- Prove2me | solution 1 for ParamSDO.Transition.remark_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:38:38.464026+00:00
-- url     : https://prove2.me/submissions/fa4d532e-7deb-4fe4-becd-c0fbbceb5154

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

theorem solution {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    ∀ ϵ ∈ interior (domE A b C Cbar),
      (∃ X ∈ Pfeas A b, X.PosDef) ∧ ∃ p ∈ Dfeas A C Cbar ϵ, p.2.PosDef :=
  fun ϵ hϵ => ⟨h2.1, psdo_dual_slater A b C Cbar hA hC hCbar h2 ϵ hϵ⟩
