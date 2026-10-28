-- Prove2me | solution 1 for YeIPA.Asymptotic.theorem_7_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T05:40:21.069309+00:00
-- url     : https://prove2.me/submissions/7233ac12-2ef3-4b79-b45d-64dc8813fe9e

import Mathlib
import Definitions.Def_YeIPA_Asymptotic_LP
import Theorems.Thm_YeIPA_Asymptotic_lemma_7_3
import Theorems.Thm_YeIPA_Asymptotic_lemma_7_4
import Theorems.Thm_YeIPA_Asymptotic_eq_7_6

open Matrix

namespace YeIPA.Asymptotic.T75

lemma lin_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (M : E →ₗ[ℝ] F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v, ‖M v‖ ≤ K * ‖v‖ := by
  let M' : E →L[ℝ] F := ⟨M, LinearMap.continuous_of_finiteDimensional M⟩
  exact ⟨‖M'‖, norm_nonneg _, fun v => M'.le_opNorm v⟩

lemma preimage_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (L : E →ₗ[ℝ] F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u, ∃ u', L u' = L u ∧ ‖u'‖ ≤ K * ‖L u‖ := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective L.rangeRestrict
    (LinearMap.range_rangeRestrict L)
  obtain ⟨K, hK, hb⟩ := lin_bound g
  refine ⟨K, hK, fun u => ⟨g (L.rangeRestrict u), ?_, ?_⟩⟩
  · have := congrArg (fun w : LinearMap.range L => (w : F))
      (LinearMap.congr_fun hg (L.rangeRestrict u))
    simpa using this
  · have := hb (L.rangeRestrict u)
    simpa using this

lemma abs_le_sqrt_sum {k : ℕ} (v : Fin k → ℝ) (j : Fin k) : |v j| ≤ Real.sqrt (∑ i, v i ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (f := fun i => v i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)

lemma norm_le_sqrt_sum {k : ℕ} (v : Fin k → ℝ) : ‖v‖ ≤ Real.sqrt (∑ i, v i ^ 2) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
  rw [Real.norm_eq_abs]; exact abs_le_sqrt_sum v j

lemma sum_sq_le {k : ℕ} (v : Fin k → ℝ) : ∑ i, v i ^ 2 ≤ k * ‖v‖ ^ 2 := by
  calc ∑ i, v i ^ 2 ≤ ∑ _i : Fin k, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        rw [← sq_abs, ← Real.norm_eq_abs]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
    _ = k * ‖v‖ ^ 2 := by simp

lemma ratio_bounds (ξ μ p q : ℝ) (hξ : 0 < ξ) (hp : 0 < p) (hq : 0 < q) (h1 : ξ ≤ p)
    (h2 : p ≤ 1 / ξ) (h3 : 3 / 4 * μ ≤ p * q) (h4 : p * q ≤ 5 / 4 * μ) :
    3 / 4 * μ * ξ ^ 2 ≤ q / p ∧ q / p ≤ 5 / 4 * μ / ξ ^ 2 := by
  have hpξ : p * ξ ≤ 1 := by rwa [le_div_iff₀ hξ] at h2
  have hμ : 0 ≤ μ := by nlinarith
  constructor
  · rw [le_div_iff₀ hp]
    have : p * ξ * (p * ξ) ≤ 1 := by nlinarith [mul_pos hp hξ]
    nlinarith [mul_nonneg hμ (mul_pos hp hξ).le]
  · rw [div_le_div_iff₀ hp (by positivity)]
    nlinarith [mul_le_mul h1 h1 hξ.le hp.le]

lemma sq_div_sqrt (p q v : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (v / Real.sqrt (p / q)) ^ 2 = q / p * v ^ 2 := by
  rw [div_pow, Real.sq_sqrt (div_pos hp hq).le]; field_simp

lemma sq_sqrt_mul (p q v : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (Real.sqrt (p / q) * v) ^ 2 = p / q * v ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (div_pos hp hq).le]

lemma final_step (N μ ξ K' : ℝ) (n : ℕ) (hμ : 0 < μ) (hξ : 0 < ξ) (hK' : 0 ≤ K')
    (key : 3 / 4 * μ * ξ ^ 2 * N ≤ 5 / 4 * μ / ξ ^ 2 * (n * (K' * μ) ^ 2)) :
    Real.sqrt N ≤ Real.sqrt (5 / 3 * n / ξ ^ 4) * K' * μ := by
  have hc : 0 < 3 / 4 * μ * ξ ^ 2 := by positivity
  have h1 : N ≤ 5 / 3 * n / ξ ^ 4 * (K' * μ) ^ 2 := by
    refine le_of_mul_le_mul_left (key.trans_eq ?_) hc
    field_simp
  calc Real.sqrt N ≤ Real.sqrt (5 / 3 * n / ξ ^ 4 * (K' * μ) ^ 2) := Real.sqrt_le_sqrt h1
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]; ring

lemma indicator_norm_le {k : ℕ} (S : Set (Fin k)) (v : Fin k → ℝ) : ‖S.indicator v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  by_cases hj : j ∈ S
  · rw [Set.indicator_of_mem hj]; exact norm_le_pi_norm v j
  · rw [Set.indicator_of_notMem hj, norm_zero]; exact norm_nonneg _

end YeIPA.Asymptotic.T75

open YeIPA.Asymptotic YeIPA.Asymptotic.T75 in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : A.rank = m) (μ0 : ℝ) (hμ0 : 0 < μ0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ)
        (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ),
        InN2 A b c (1 / 4) x y s → mu x s ≤ μ0 →
        IsPredictorDirection A x s dx dy ds →
          normOn (Pstar A b c) dx ≤ C * mu x s ∧
          normOn (Zstar A b c) ds ≤ C * mu x s := by
  classical
  obtain ⟨C₃, hC₃, h73⟩ := lemma_7_3 A b c hA μ0 hμ0
  obtain ⟨ξ, hξ, hξ1, h76⟩ := eq_7_6 A b c hA μ0 hμ0
  set P := Pstar A b c with hPdef
  set Z := Zstar A b c with hZdef
  let Lp : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) := A.mulVecLin ∘ₗ (Matrix.diagonal (P.indicator 1)).mulVecLin
  let Lz : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) := (Matrix.diagonal (P.indicator 1)).mulVecLin ∘ₗ Aᵀ.mulVecLin
  have hind : ∀ u : Fin n → ℝ, (fun j => P.indicator 1 j * u j) = P.indicator u := by
    intro u; funext j; by_cases hj : j ∈ P <;> simp [hj]
  have hLp : ∀ u, Lp u = A *ᵥ P.indicator u := by
    intro u
    simp only [Lp, LinearMap.comp_apply, Matrix.mulVecLin_apply]
    congr 1; funext j; rw [Matrix.mulVec_diagonal]; exact congrFun (hind u) j
  have hLz : ∀ v, Lz v = P.indicator (Aᵀ *ᵥ v) := by
    intro v
    simp only [Lz, LinearMap.comp_apply, Matrix.mulVecLin_apply]
    funext j; rw [Matrix.mulVec_diagonal]; exact congrFun (hind _) j
  obtain ⟨K₁, hK₁, hp1⟩ := preimage_bound Lp
  obtain ⟨K₂, hK₂, hp2⟩ := preimage_bound Lz
  obtain ⟨KA, hKA, hA1⟩ := lin_bound A.mulVecLin
  obtain ⟨KT, hKT, hA2⟩ := lin_bound Aᵀ.mulVecLin
  set C₁ := Real.sqrt (5 / 3 * n / ξ ^ 4) * (K₁ * KA * C₃) with hC₁
  set C₂ := Real.sqrt (5 / 3 * n / ξ ^ 4) * (KT * K₂ * C₃) with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  refine ⟨C₁ + C₂ + 1, by positivity, ?_⟩
  intro x y s dx dy ds hN hμ hdir
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [normOn, mu]
  obtain ⟨hint, hres⟩ := hN
  have hx : ∀ j, 0 < x j := hint.2.1
  have hs : ∀ j, 0 < s j := hint.2.2.2
  set μ := mu x s with hμdef
  have hμpos : 0 < μ := by
    rw [hμdef, mu]
    apply div_pos _ (by exact_mod_cast hn)
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Finset.sum_pos (fun j _ => mul_pos (hx j) (hs j)) Finset.univ_nonempty
  have hxs : ∀ j, 3 / 4 * μ ≤ x j * s j ∧ x j * s j ≤ 5 / 4 * μ := by
    intro j
    have := (abs_le_sqrt_sum (fun j => x j * s j - μ) j).trans hres
    rw [abs_le] at this
    constructor <;> linarith
  obtain ⟨h73a, h73b⟩ := h73 x y s dx dy ds ⟨hint, hres⟩ hμ hdir
  obtain ⟨h76P, h76Z⟩ := h76 x y s ⟨hint, hres⟩ hμ
  have h74 := lemma_7_4 A b c hA x y s dx dy ds hint hdir
  simp only [Set.mem_ofPred_eq] at h74
  obtain ⟨⟨hU, hmin⟩, ⟨hV, hgmin, -⟩⟩ := h74
  have hCμ : ∀ C' : ℝ, C' ≤ C₁ + C₂ + 1 → C' * μ ≤ (C₁ + C₂ + 1) * μ := fun C' h =>
    mul_le_mul_of_nonneg_right h hμpos.le
  constructor
  · -- P part
    obtain ⟨u', hu'1, hu'2⟩ := hp1 dx
    set us := P.indicator u' with hus
    have hAus : A *ᵥ us = -(A *ᵥ Z.indicator dx) := by
      rw [← hLp, hu'1, hLp]; exact hU.2
    have husU : (∀ j, j ∉ P → us j = 0) ∧ A *ᵥ us = -(A *ᵥ Z.indicator dx) :=
      ⟨fun j hj => Set.indicator_of_notMem hj _, hAus⟩
    have hf : (1 / 2 : ℝ) * ∑ j, (P.indicator dx j / scaling x s j) ^ 2 ≤
        (1 / 2 : ℝ) * ∑ j, (us j / scaling x s j) ^ 2 := by
      by_cases he : us = P.indicator dx
      · rw [he]
      · exact (hmin us husU he).le
    have hnorm : ‖us‖ ≤ K₁ * KA * C₃ * μ := by
      calc ‖us‖ ≤ ‖u'‖ := indicator_norm_le _ _
        _ ≤ K₁ * ‖Lp dx‖ := hu'2
        _ ≤ K₁ * (KA * (C₃ * μ)) := by
          apply mul_le_mul_of_nonneg_left _ hK₁
          rw [hLp, hU.2, norm_neg]
          refine (hA1 _).trans (mul_le_mul_of_nonneg_left ?_ hKA)
          exact (norm_le_sqrt_sum _).trans h73a
        _ = _ := by ring
    have hlow : ∀ j, 3 / 4 * μ * ξ ^ 2 * (P.indicator dx j) ^ 2 ≤
        (P.indicator dx j / scaling x s j) ^ 2 := by
      intro j
      rw [scaling, sq_div_sqrt _ _ _ (hx j) (hs j)]
      by_cases hj : j ∈ P
      · have := (ratio_bounds ξ μ (x j) (s j) hξ (hx j) (hs j) (h76P j hj).1 (h76P j hj).2
          (hxs j).1 (hxs j).2).1
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      · simp [Set.indicator_of_notMem hj]
    have hup : ∀ j, (us j / scaling x s j) ^ 2 ≤ 5 / 4 * μ / ξ ^ 2 * (us j) ^ 2 := by
      intro j
      rw [scaling, sq_div_sqrt _ _ _ (hx j) (hs j)]
      by_cases hj : j ∈ P
      · have := (ratio_bounds ξ μ (x j) (s j) hξ (hx j) (hs j) (h76P j hj).1 (h76P j hj).2
          (hxs j).1 (hxs j).2).2
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      · simp [hus, Set.indicator_of_notMem hj]
    have key : 3 / 4 * μ * ξ ^ 2 * ∑ j, (P.indicator dx j) ^ 2 ≤
        5 / 4 * μ / ξ ^ 2 * (n * (K₁ * KA * C₃ * μ) ^ 2) := by
      rw [Finset.mul_sum]
      calc _ ≤ ∑ j, (P.indicator dx j / scaling x s j) ^ 2 := Finset.sum_le_sum fun j _ => hlow j
        _ ≤ ∑ j, (us j / scaling x s j) ^ 2 := by linarith
        _ ≤ ∑ j, 5 / 4 * μ / ξ ^ 2 * (us j) ^ 2 := Finset.sum_le_sum fun j _ => hup j
        _ = 5 / 4 * μ / ξ ^ 2 * ∑ j, (us j) ^ 2 := by rw [Finset.mul_sum]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine (sum_sq_le us).trans ?_
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have := final_step _ μ ξ (K₁ * KA * C₃) n hμpos hξ (by positivity) key
    rw [normOn]
    exact this.trans (hCμ C₁ (by linarith))
  · -- Z part
    obtain ⟨v', hv'1, hv'2⟩ := hp2 dy
    have hds : ∀ j, ds j = -(Aᵀ *ᵥ dy) j := by
      intro j
      have := congrFun hdir.2.2 j
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.zero_apply] at this
      linarith
    have hLzdy : Lz dy = -(P.indicator ds) := by
      rw [hLz]; funext j
      by_cases hj : j ∈ P
      · simp [Set.indicator_of_mem hj, hV j hj]
      · simp [Set.indicator_of_notMem hj]
    have hv'V : ∀ j ∈ P, (Aᵀ *ᵥ v') j = -ds j := by
      intro j hj
      have := congrFun hv'1 j
      rw [hLz, hLz, Set.indicator_of_mem hj, Set.indicator_of_mem hj] at this
      rw [this]; exact hV j hj
    have hg := hgmin v' hv'V
    have hnorm : ‖Aᵀ *ᵥ v'‖ ≤ KT * K₂ * C₃ * μ := by
      calc ‖Aᵀ *ᵥ v'‖ ≤ KT * ‖v'‖ := hA2 v'
        _ ≤ KT * (K₂ * (C₃ * μ)) := by
          apply mul_le_mul_of_nonneg_left _ hKT
          refine hv'2.trans (mul_le_mul_of_nonneg_left ?_ hK₂)
          rw [hLzdy, norm_neg]
          exact (norm_le_sqrt_sum _).trans h73b
        _ = _ := by ring
    have hlow : ∀ j, 3 / 4 * μ * ξ ^ 2 * (Z.indicator ds j) ^ 2 ≤
        (Z.indicator (fun i => scaling x s i * (Aᵀ *ᵥ dy) i) j) ^ 2 := by
      intro j
      by_cases hj : j ∈ Z
      · rw [Set.indicator_of_mem hj, Set.indicator_of_mem hj, scaling,
          sq_sqrt_mul _ _ _ (hx j) (hs j), hds j, neg_sq]
        have := (ratio_bounds ξ μ (s j) (x j) hξ (hs j) (hx j) (h76Z j hj).1 (h76Z j hj).2
          (by linarith [mul_comm (x j) (s j), (hxs j).1]) (by linarith [mul_comm (x j) (s j), (hxs j).2])).1
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      · simp [Set.indicator_of_notMem hj]
    have hup : ∀ j, (Z.indicator (fun i => scaling x s i * (Aᵀ *ᵥ v') i) j) ^ 2 ≤
        5 / 4 * μ / ξ ^ 2 * ((Aᵀ *ᵥ v') j) ^ 2 := by
      intro j
      by_cases hj : j ∈ Z
      · rw [Set.indicator_of_mem hj, scaling, sq_sqrt_mul _ _ _ (hx j) (hs j)]
        have := (ratio_bounds ξ μ (s j) (x j) hξ (hs j) (hx j) (h76Z j hj).1 (h76Z j hj).2
          (by linarith [mul_comm (x j) (s j), (hxs j).1]) (by linarith [mul_comm (x j) (s j), (hxs j).2])).2
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      · simp only [Set.indicator_of_notMem hj]
        have : 0 ≤ 5 / 4 * μ / ξ ^ 2 := by positivity
        nlinarith [sq_nonneg ((Aᵀ *ᵥ v') j)]
    have key : 3 / 4 * μ * ξ ^ 2 * ∑ j, (Z.indicator ds j) ^ 2 ≤
        5 / 4 * μ / ξ ^ 2 * (n * (KT * K₂ * C₃ * μ) ^ 2) := by
      rw [Finset.mul_sum]
      calc _ ≤ ∑ j, (Z.indicator (fun i => scaling x s i * (Aᵀ *ᵥ dy) i) j) ^ 2 :=
            Finset.sum_le_sum fun j _ => hlow j
        _ ≤ ∑ j, (Z.indicator (fun i => scaling x s i * (Aᵀ *ᵥ v') i) j) ^ 2 := by linarith
        _ ≤ ∑ j, 5 / 4 * μ / ξ ^ 2 * ((Aᵀ *ᵥ v') j) ^ 2 := Finset.sum_le_sum fun j _ => hup j
        _ = 5 / 4 * μ / ξ ^ 2 * ∑ j, ((Aᵀ *ᵥ v') j) ^ 2 := by rw [Finset.mul_sum]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine (sum_sq_le _).trans ?_
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have := final_step _ μ ξ (KT * K₂ * C₃) n hμpos hξ (by positivity) key
    rw [normOn]
    exact this.trans (hCμ C₂ (by linarith))
