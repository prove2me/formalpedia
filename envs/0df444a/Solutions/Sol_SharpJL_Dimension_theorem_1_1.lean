-- Prove2me | solution 1 for SharpJL.Dimension.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:38:35.01068+00:00
-- url     : https://prove2.me/submissions/c23ac556-db5c-4d2c-8a91-e1276cd1c483

import Mathlib
import Theorems.Thm_SharpJL_Dimension_corollary_2_1

section
namespace SharpJL.Dev.Thm11

theorem embed_nonempty {s N : ℕ} (h : s ≤ N) :
    Nonempty (EuclideanSpace ℝ (Fin s) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) := by
  classical
  refine ⟨{ toFun := fun v => WithLp.toLp 2
              (fun i : Fin N => if hi : i.val < s then v.ofLp ⟨i.val, hi⟩ else 0)
            map_add' := ?_
            map_smul' := ?_
            norm_map' := ?_ }⟩
  · intro a b
    ext i
    by_cases hi : i.val < s <;> simp [hi]
  · intro c a
    ext i
    by_cases hi : i.val < s <;> simp [hi]
  · intro v
    simp only
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    symm
    refine Finset.sum_of_injOn (Fin.castLE h) (fun a _ b _ hab => Fin.castLE_injective h hab)
      (fun a _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_ ?_
    · intro i _ hi
      have : ¬ i.val < s := by
        intro hlt
        exact hi ⟨⟨i.val, hlt⟩, Finset.mem_coe.mpr (Finset.mem_univ _), Fin.ext rfl⟩
      simp [this]
    · intro a _
      simp [Fin.castLE]

theorem exists_iso {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {k : ℕ} (h : Module.finrank ℝ E = k) :
    Nonempty (E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :=
  ⟨((stdOrthonormalBasis ℝ E).reindex (finCongr h)).repr⟩

theorem exists_embed {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (h : Module.finrank ℝ E ≤ N) :
    Nonempty (E →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) := by
  obtain ⟨T⟩ := exists_iso (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  obtain ⟨f⟩ := embed_nonempty h
  exact ⟨f.comp T.toLinearIsometry⟩


noncomputable def δf (C0 : ℝ) (n R : ℕ) : ℝ :=
  C0 * Real.sqrt (Real.log (2 + (n : ℝ) / (R : ℝ)) / (R : ℝ))

noncomputable def Sj (C0 : ℝ) (n r0 j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, δf C0 n (2 ^ i * r0)

theorem δf_nonneg {C0 : ℝ} (hC0 : 0 < C0) (n R : ℕ) : 0 ≤ δf C0 n R :=
  mul_nonneg hC0.le (Real.sqrt_nonneg _)

theorem Sj_nonneg {C0 : ℝ} (hC0 : 0 < C0) (n r0 j : ℕ) : 0 ≤ Sj C0 n r0 j :=
  Finset.sum_nonneg fun i _ => δf_nonneg hC0 _ _

theorem Sj_mono {C0 : ℝ} (hC0 : 0 < C0) (n r0 : ℕ) {j J : ℕ} (h : j ≤ J) :
    Sj C0 n r0 j ≤ Sj C0 n r0 J :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    (fun i _ _ => δf_nonneg hC0 _ _)

theorem iter (C0 : ℝ) (hC0 : 0 < C0)
    (hcor : ∀ (n r : ℕ), 2 ≤ n → 1 ≤ r →
      ∀ (X : Finset (EuclideanSpace ℝ (Fin (2 * r)))), 2 ≤ X.card → X.card ≤ n →
        ∃ L : EuclideanSpace ℝ (Fin (2 * r)) →ₗ[ℝ] EuclideanSpace ℝ (Fin r),
          ∀ x ∈ X, ∀ y ∈ X,
            (1 - δf C0 n r) * ‖x - y‖ ^ 2 ≤ ‖L x - L y‖ ^ 2 ∧
              ‖L x - L y‖ ^ 2 ≤ (1 + δf C0 n r) * ‖x - y‖ ^ 2)
    (n r0 : ℕ) (hn : 2 ≤ n) (hr0 : 1 ≤ r0) (J : ℕ) (hS : Sj C0 n r0 J < 1) :
    ∀ j, j ≤ J → ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E], Module.finrank ℝ E = 2 ^ j * r0 →
      ∀ X : Finset E, 2 ≤ X.card → X.card ≤ n →
      ∃ L : E →ₗ[ℝ] EuclideanSpace ℝ (Fin r0),
        ∀ x ∈ X, ∀ y ∈ X,
          (1 - Sj C0 n r0 j) * ‖x - y‖ ^ 2 ≤ ‖L x - L y‖ ^ 2 ∧
            ‖L x - L y‖ ^ 2 ≤ (1 - Sj C0 n r0 j)⁻¹ * ‖x - y‖ ^ 2 := by
  classical
  intro j
  induction j with
  | zero =>
    intro _ E _ _ _ hE X _ _
    obtain ⟨T⟩ := exists_iso (E := E) (k := r0) (by simpa using hE)
    refine ⟨T.toLinearEquiv.toLinearMap, fun x hx y hy => ?_⟩
    have : ‖T x - T y‖ = ‖x - y‖ := by rw [← map_sub, T.norm_map]
    simp [Sj, this]
  | succ j ih =>
    intro hj E _ _ _ hE X hX2 hXn
    have hjJ : j ≤ J := Nat.le_of_succ_le hj
    have hR : 1 ≤ 2 ^ j * r0 := Nat.mul_pos (by positivity) hr0
    set R := 2 ^ j * r0 with hRdef
    have hE2 : Module.finrank ℝ E = 2 * R := by rw [hE, hRdef]; ring
    obtain ⟨T⟩ := exists_iso hE2
    have hcard' : (X.image T).card = X.card := Finset.card_image_of_injective _ T.injective
    obtain ⟨L1', hL1'⟩ := hcor n R hn hR (X.image T) (by omega) (by omega)
    set δ := δf C0 n R with hδdef
    have hδ0 : 0 ≤ δ := δf_nonneg hC0 _ _
    have hSj : Sj C0 n r0 (j + 1) = Sj C0 n r0 j + δ := by
      simp [Sj, Finset.sum_range_succ, hδdef, hRdef]
    have ha0 : 0 ≤ Sj C0 n r0 j := Sj_nonneg hC0 _ _ _
    have hSJ : Sj C0 n r0 (j + 1) < 1 := lt_of_le_of_lt (Sj_mono hC0 n r0 hj) hS
    have hδ1 : δ < 1 := by linarith
    let L1 : E →ₗ[ℝ] EuclideanSpace ℝ (Fin R) := L1'.comp T.toLinearEquiv.toLinearMap
    have hb : ∀ x ∈ X, ∀ y ∈ X,
        (1 - δ) * ‖x - y‖ ^ 2 ≤ ‖L1 x - L1 y‖ ^ 2 ∧
          ‖L1 x - L1 y‖ ^ 2 ≤ (1 + δ) * ‖x - y‖ ^ 2 := by
      intro x hx y hy
      have h := hL1' (T x) (Finset.mem_image_of_mem _ hx) (T y) (Finset.mem_image_of_mem _ hy)
      have e : ‖T x - T y‖ = ‖x - y‖ := by rw [← map_sub, T.norm_map]
      rw [e] at h
      exact h
    have hinj : Set.InjOn L1 (X : Set E) := by
      intro x hx y hy hxy
      by_contra hne
      have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have h1 := (hb x hx y hy).1
      rw [hxy, sub_self, norm_zero] at h1
      have : 0 < (1 - δ) * ‖x - y‖ ^ 2 := by
        apply mul_pos (by linarith) (by positivity)
      linarith
    have hcard1 : (X.image L1).card = X.card := Finset.card_image_of_injOn hinj
    obtain ⟨L2, hL2⟩ := ih hjJ (EuclideanSpace ℝ (Fin R)) (by simp [hRdef])
      (X.image L1) (by omega) (by omega)
    refine ⟨L2.comp L1, fun x hx y hy => ?_⟩
    have h2 := hL2 (L1 x) (Finset.mem_image_of_mem _ hx) (L1 y) (Finset.mem_image_of_mem _ hy)
    obtain ⟨hb1, hb2⟩ := hb x hx y hy
    rw [hSj]
    simp only [LinearMap.comp_apply]
    obtain ⟨h21, h22⟩ := h2
    have hq : 0 ≤ ‖x - y‖ ^ 2 := by positivity
    have ha1 : 0 < 1 - Sj C0 n r0 j := by linarith
    have hs1 : 0 < 1 - (Sj C0 n r0 j + δ) := by linarith
    constructor
    · have : (1 - (Sj C0 n r0 j + δ)) * ‖x - y‖ ^ 2 ≤
          (1 - Sj C0 n r0 j) * ((1 - δ) * ‖x - y‖ ^ 2) := by
        nlinarith [mul_nonneg (mul_nonneg ha0 hδ0) hq]
      have h3 := mul_le_mul_of_nonneg_left hb1 ha1.le
      linarith
    · have h3 := mul_le_mul_of_nonneg_left hb2 (inv_nonneg.mpr ha1.le)
      have h4 : (1 - Sj C0 n r0 j)⁻¹ * (1 + δ) ≤ (1 - (Sj C0 n r0 j + δ))⁻¹ := by
        rw [← div_eq_inv_mul, ← one_div, div_le_div_iff₀ ha1 hs1]
        nlinarith [mul_nonneg ha0 hδ0, mul_nonneg hδ0 hδ0]
      have h5 := mul_le_mul_of_nonneg_right h4 hq
      have h6 := mul_le_mul_of_nonneg_left h21 (inv_nonneg.mpr ha1.le)
      nlinarith [h22, h3, h5]


theorem est (C0 : ℝ) (hC0 : 0 < C0) (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 2)
    (n : ℕ) (r0 : ℕ) (k : ℝ) (hk : 2 ≤ k) (hk16 : 16 * C0 ≤ k)
    (hr0 : k ^ 2 * (Real.log (2 + ε ^ 2 * (n : ℝ)) / ε ^ 2) ≤ (r0 : ℝ)) (J : ℕ) :
    Sj C0 n r0 J ≤ ε / 4 := by
  set Λ := Real.log (2 + ε ^ 2 * (n : ℝ)) with hΛ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hΛ2 : 1 / 2 ≤ Λ := by
    have h1 : Real.log 2 ≤ Λ := Real.log_le_log (by norm_num) (by nlinarith [sq_nonneg ε])
    have := Real.log_two_gt_d9
    linarith
  have hε2 : 0 < ε ^ 2 := by positivity
  have hr0pos : 2 / ε ^ 2 ≤ (r0 : ℝ) := by
    refine le_trans ?_ hr0
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hε2]
    nlinarith
  have hr0p : 0 < (r0 : ℝ) := lt_of_lt_of_le (by positivity) hr0pos
  have hε2r : 1 ≤ ε ^ 2 * (r0 : ℝ) := by
    rw [div_le_iff₀ hε2] at hr0pos; linarith
  set q := Real.sqrt (1 / 2) with hqdef
  have hq2 : q ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hq0 : 0 < q := Real.sqrt_pos.mpr (by norm_num)
  have hq1 : q < 3 / 4 := by nlinarith
  have hk0 : 0 < k := by linarith
  have hterm : ∀ i : ℕ, δf C0 n (2 ^ i * r0) ≤ C0 * (ε / k) * q ^ i := by
    intro i
    have hRc : (((2 ^ i * r0 : ℕ)) : ℝ) = 2 ^ i * (r0 : ℝ) := by push_cast; ring
    have hRp : 0 < (2 : ℝ) ^ i * (r0 : ℝ) := by positivity
    have h2i : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    have hRge : (r0 : ℝ) ≤ 2 ^ i * (r0 : ℝ) := by nlinarith
    have hnr : (n : ℝ) / (2 ^ i * (r0 : ℝ)) ≤ ε ^ 2 * n := by
      calc (n : ℝ) / (2 ^ i * (r0 : ℝ)) ≤ (n : ℝ) / r0 :=
            div_le_div_of_nonneg_left hn0 hr0p hRge
        _ ≤ ε ^ 2 * n := by
            rw [div_le_iff₀ hr0p]; nlinarith
    have hlog : Real.log (2 + (n : ℝ) / (2 ^ i * (r0 : ℝ))) ≤ Λ :=
      Real.log_le_log (by positivity) (by linarith)
    have harg : Real.log (2 + (n : ℝ) / (2 ^ i * (r0 : ℝ))) / (2 ^ i * (r0 : ℝ))
        ≤ (ε / k * q ^ i) ^ 2 := by
      have e1 : (ε / k * q ^ i) ^ 2 = ε ^ 2 / k ^ 2 * (1 / 2) ^ i := by
        rw [mul_pow, div_pow, ← pow_mul, mul_comm i 2, pow_mul, hq2]
      rw [e1]
      calc Real.log (2 + (n : ℝ) / (2 ^ i * (r0 : ℝ))) / (2 ^ i * (r0 : ℝ))
          ≤ Λ / (2 ^ i * (r0 : ℝ)) := div_le_div_of_nonneg_right hlog hRp.le
        _ ≤ ε ^ 2 / k ^ 2 * (1 / 2) ^ i := by
            rw [div_le_iff₀ hRp]
            have e2 : ε ^ 2 / k ^ 2 * (1 / 2) ^ i * (2 ^ i * (r0 : ℝ))
                = ε ^ 2 / k ^ 2 * (r0 : ℝ) := by
              have h12 : (1 / 2 : ℝ) ^ i * 2 ^ i = 1 := by rw [← mul_pow]; norm_num
              calc ε ^ 2 / k ^ 2 * (1 / 2) ^ i * (2 ^ i * (r0 : ℝ))
                  = ε ^ 2 / k ^ 2 * (((1 / 2 : ℝ) ^ i * 2 ^ i) * (r0 : ℝ)) := by ring
                _ = ε ^ 2 / k ^ 2 * (r0 : ℝ) := by rw [h12]; ring
            rw [e2]
            have : Λ ≤ ε ^ 2 / k ^ 2 * (r0 : ℝ) := by
              rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
              have h : k ^ 2 * Λ ≤ ε ^ 2 * (r0 : ℝ) := by
                have := hr0
                rw [← mul_div_assoc, div_le_iff₀ hε2] at this
                linarith
              linarith
            exact this
    unfold δf
    rw [hRc]
    have hs : Real.sqrt (Real.log (2 + (n : ℝ) / (2 ^ i * (r0 : ℝ))) / (2 ^ i * (r0 : ℝ)))
        ≤ ε / k * q ^ i :=
      Real.sqrt_le_iff.mpr ⟨by positivity, harg⟩
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hs hC0.le
  calc Sj C0 n r0 J ≤ ∑ i ∈ Finset.range J, C0 * (ε / k) * q ^ i :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = C0 * (ε / k) * ∑ i ∈ Finset.range J, q ^ i := by rw [Finset.mul_sum]
    _ ≤ C0 * (ε / k) * 4 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h1 := mul_neg_geom_sum q J
        have h0 : 0 ≤ ∑ i ∈ Finset.range J, q ^ i :=
          Finset.sum_nonneg fun i _ => by positivity
        have h3 : 0 ≤ q ^ J := by positivity
        nlinarith
    _ ≤ ε / 4 := by
        have : C0 * (ε / k) * 4 = 4 * C0 * ε / k := by ring
        rw [this, div_le_iff₀ hk0]
        nlinarith


theorem rbound (r a b c C : ℝ) (hC : 1 ≤ C) (ha : r ≤ a) (hb : r ≤ b) (hc : r ≤ C * c)
    (hr : 0 ≤ r) : r ≤ C * min a (min b c) := by
  rcases min_choice a (min b c) with h | h
  · rw [h]; nlinarith
  · rw [h]
    rcases min_choice b c with h' | h'
    · rw [h']; nlinarith
    · rw [h']; exact hc

theorem main (C0 : ℝ) (hC0 : 0 < C0)
    (hcor : ∀ (n r : ℕ), 2 ≤ n → 1 ≤ r →
      ∀ (X : Finset (EuclideanSpace ℝ (Fin (2 * r)))), 2 ≤ X.card → X.card ≤ n →
        ∃ L : EuclideanSpace ℝ (Fin (2 * r)) →ₗ[ℝ] EuclideanSpace ℝ (Fin r),
          ∀ x ∈ X, ∀ y ∈ X,
            (1 - δf C0 n r) * ‖x - y‖ ^ 2 ≤ ‖L x - L y‖ ^ 2 ∧
              ‖L x - L y‖ ^ 2 ≤ (1 + δf C0 n r) * ‖x - y‖ ^ 2)
    (n d : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 2)
    (X : Finset (EuclideanSpace ℝ (Fin d))) (hX : X.card = n) :
    ∃ (r : ℕ) (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin r)) (lam : ℝ),
      (r : ℝ) ≤ (max (16 * C0) 2 ^ 2 + 1) * min (d : ℝ)
        (min ((n : ℝ) - 1) (Real.log (2 + ε ^ 2 * (n : ℝ)) / ε ^ 2)) ∧
      0 < lam ∧
      ∀ x ∈ X, ∀ y ∈ X,
        lam * ‖x - y‖ ≤ ‖L x - L y‖ ∧ ‖L x - L y‖ ≤ (1 + ε) * lam * ‖x - y‖ := by
  classical
  set k : ℝ := max (16 * C0) 2 with hkdef
  have hk : 2 ≤ k := le_max_right _ _
  have hk16 : 16 * C0 ≤ k := le_max_left _ _
  set Λ := Real.log (2 + ε ^ 2 * (n : ℝ)) with hΛ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hΛ2 : 1 / 2 ≤ Λ := by
    have h1 : Real.log 2 ≤ Λ := Real.log_le_log (by norm_num) (by nlinarith [sq_nonneg ε])
    have := Real.log_two_gt_d9
    linarith
  have hε2 : 0 < ε ^ 2 := by positivity
  have hD : 1 ≤ Λ / ε ^ 2 := by
    rw [le_div_iff₀ hε2]; nlinarith
  set D := Λ / ε ^ 2 with hDdef
  have hk2 : 4 ≤ k ^ 2 := by nlinarith
  set r0 : ℕ := ⌈k ^ 2 * D⌉₊ with hr0def
  have hr0le : k ^ 2 * D ≤ (r0 : ℝ) := Nat.le_ceil _
  have hr01 : 1 ≤ r0 := Nat.ceil_pos.mpr (by positivity)
  have hr0up : (r0 : ℝ) ≤ (k ^ 2 + 1) * D := by
    have := Nat.ceil_lt_add_one (show 0 ≤ k ^ 2 * D by positivity)
    nlinarith
  set W := vectorSpan ℝ (X : Set (EuclideanSpace ℝ (Fin d))) with hW
  have hdiff : ∀ x ∈ X, ∀ y ∈ X, x - y ∈ W := by
    intro x hx y hy
    have := vsub_mem_vectorSpan ℝ (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy)
    simpa using this
  have hfd : Module.finrank ℝ W ≤ d := by
    have := Submodule.finrank_le W
    simpa using this
  have hfn : Module.finrank ℝ W ≤ n - 1 := by
    have := finrank_vectorSpan_image_finset_le ℝ (id : EuclideanSpace ℝ (Fin d) → _) X
      (n := n - 1) (by omega)
    have e : X.image (id : EuclideanSpace ℝ (Fin d) → _) = X := Finset.image_id
    rw [e] at this
    exact this
  set P : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] W := (W.orthogonalProjectionOnto : _ →L[ℝ] W).toLinearMap
    with hPdef
  have hP : ∀ x ∈ X, ∀ y ∈ X, ‖P x - P y‖ = ‖x - y‖ := by
    intro x hx y hy
    rw [show P x - P y = P (x - y) from (map_sub P x y).symm]
    have h := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := W)
      ⟨x - y, hdiff x hx y hy⟩
    have h2 : P (x - y) = ⟨x - y, hdiff x hx y hy⟩ := h
    rw [h2]
    rfl
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hC1 : (1 : ℝ) ≤ k ^ 2 + 1 := by nlinarith
  have hrfin : ∀ r : ℕ, r ≤ d → r ≤ n - 1 → r ≤ r0 →
      (r : ℝ) ≤ (k ^ 2 + 1) * min (d : ℝ) (min ((n : ℝ) - 1) D) := by
    intro r h1 h2 h3
    apply rbound _ _ _ _ _ hC1 (by exact_mod_cast h1) (by rw [← hn1]; exact_mod_cast h2)
      (le_trans (by exact_mod_cast h3) hr0up) (Nat.cast_nonneg _)
  by_cases hs : Module.finrank ℝ W ≤ r0
  · obtain ⟨T⟩ := exists_iso (E := W) (rfl : Module.finrank ℝ W = Module.finrank ℝ W)
    refine ⟨Module.finrank ℝ W, T.toLinearEquiv.toLinearMap ∘ₗ P, 1, hrfin _ hfd hfn hs,
      one_pos, fun x hx y hy => ?_⟩
    have : ‖T (P x) - T (P y)‖ = ‖x - y‖ := by rw [← map_sub, T.norm_map, hP x hx y hy]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    rw [this]
    constructor
    · linarith
    · have := norm_nonneg (x - y); nlinarith
  · rw [not_le] at hs
    set s := Module.finrank ℝ W with hsdef
    have hN : s ≤ 2 ^ s * r0 := by
      calc s ≤ 2 ^ s := (Nat.lt_two_pow_self (n := s)).le
        _ ≤ 2 ^ s * r0 := Nat.le_mul_of_pos_right _ hr01
    obtain ⟨f⟩ := exists_embed (E := W) hN
    set g : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 ^ s * r0)) :=
      f.toLinearMap ∘ₗ P with hgdef
    have hg : ∀ x ∈ X, ∀ y ∈ X, ‖g x - g y‖ = ‖x - y‖ := by
      intro x hx y hy
      simp only [hgdef, LinearMap.comp_apply, LinearIsometry.coe_toLinearMap]
      rw [← map_sub, f.norm_map, hP x hx y hy]
    have hginj : Set.InjOn g (X : Set _) := by
      intro x hx y hy hxy
      have := hg x hx y hy
      rw [hxy, sub_self, norm_zero] at this
      exact sub_eq_zero.mp (norm_eq_zero.mp this.symm)
    have hcardg : (X.image g).card = n := by
      rw [Finset.card_image_of_injOn hginj, hX]
    have hS4 := est C0 hC0 ε hε0 hε n r0 k hk hk16 hr0le s
    set S := Sj C0 n r0 s with hSdef
    have hS0 : 0 ≤ S := Sj_nonneg hC0 _ _ _
    have hS1 : S < 1 := by linarith
    obtain ⟨L', hL'⟩ := iter C0 hC0 hcor n r0 hn hr01 s hS1 s le_rfl
      (EuclideanSpace ℝ (Fin (2 ^ s * r0))) (by simp) (X.image g) (by omega) (by omega)
    refine ⟨r0, L' ∘ₗ g, Real.sqrt (1 - S), ?_, Real.sqrt_pos.mpr (by linarith), ?_⟩
    · exact hrfin r0 (by omega) (by omega) le_rfl
    · intro x hx y hy
      have h := hL' (g x) (Finset.mem_image_of_mem _ hx) (g y) (Finset.mem_image_of_mem _ hy)
      rw [hg x hx y hy] at h
      obtain ⟨h1, h2⟩ := h
      simp only [LinearMap.comp_apply, ← map_sub] at h1 h2 ⊢
      have hs1 : 0 < 1 - S := by linarith
      have hsq : Real.sqrt (1 - S) ^ 2 = 1 - S := Real.sq_sqrt hs1.le
      have hq0 : 0 ≤ Real.sqrt (1 - S) := Real.sqrt_nonneg _
      have hxy0 : 0 ≤ ‖x - y‖ := norm_nonneg _
      constructor
      · rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), mul_pow, hsq]
        exact h1
      · rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, mul_pow, hsq]
        refine le_trans h2 ?_
        have hkey : 1 ≤ (1 + ε) * (1 - S) := by nlinarith
        have : (1 - S)⁻¹ ≤ (1 + ε) ^ 2 * (1 - S) := by
          rw [inv_le_iff_one_le_mul₀ hs1]
          have h2 : 1 ≤ ((1 + ε) * (1 - S)) ^ 2 := one_le_pow₀ hkey
          calc (1 : ℝ) ≤ ((1 + ε) * (1 - S)) ^ 2 := h2
            _ = (1 + ε) ^ 2 * (1 - S) * (1 - S) := by ring
        nlinarith [sq_nonneg ‖x - y‖, mul_le_mul_of_nonneg_right this (sq_nonneg ‖x - y‖)]

end SharpJL.Dev.Thm11

namespace SharpJL.Dimension

theorem chk_theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ), 2 ≤ n → 2 ≤ d →
      ∀ (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ∀ (X : Finset (EuclideanSpace ℝ (Fin d))), X.card = n →
        ∃ (r : ℕ) (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin r))
          (lam : ℝ),
          (r : ℝ) ≤ C * min (d : ℝ)
            (min ((n : ℝ) - 1) (Real.log (2 + ε ^ 2 * (n : ℝ)) / ε ^ 2)) ∧
          0 < lam ∧
          ∀ x ∈ X, ∀ y ∈ X,
            lam * ‖x - y‖ ≤ ‖L x - L y‖ ∧
              ‖L x - L y‖ ≤ (1 + ε) * lam * ‖x - y‖ := by
  obtain ⟨C0, hC0, hc⟩ := SharpJL.Dimension.corollary_2_1
  refine ⟨max (16 * C0) 2 ^ 2 + 1, by positivity, ?_⟩
  intro n d hn _ ε hε0 hε X hX
  exact SharpJL.Dev.Thm11.main C0 hC0 (fun n r hn hr X h2 hn' => by
    obtain ⟨L, hL⟩ := hc n r hn hr X h2 hn'
    exact ⟨L, hL⟩) n d hn ε hε0 hε X hX

end SharpJL.Dimension
end

theorem solution : type_of% @SharpJL.Dimension.chk_theorem_1_1 := @SharpJL.Dimension.chk_theorem_1_1
