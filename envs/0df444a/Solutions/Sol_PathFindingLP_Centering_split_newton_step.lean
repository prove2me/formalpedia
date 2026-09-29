-- Prove2me | solution 1 for PathFindingLP.Centering.split_newton_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:44:35.426472+00:00
-- url     : https://prove2.me/submissions/0c624eea-dd37-4f00-87b1-6dcf4cf57282

import Mathlib
import Definitions.Def_PathFindingLP_Centering_SlackSensitivity

open Matrix


namespace PathFindingLP.Centering

lemma pf_inj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) :
    Function.Injective A.mulVec := by
  have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h2 : Module.finrank ℝ (LinearMap.range A.mulVecLin) = n := hA
  rw [h2, Module.finrank_fin_fun] at h1
  have h3 : LinearMap.ker A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  exact LinearMap.ker_eq_bot.mp h3

lemma pf_quad {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ) (u v : Fin n → ℝ) :
    u ⬝ᵥ (weightedGram A s w *ᵥ v) =
      ∑ i, w i * ((A *ᵥ u) i / s i) * ((A *ᵥ v) i / s i) := by
  unfold weightedGram
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose]
  simp only [mulVec_diagonal, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]; ring

lemma pf_cs {m : ℕ} (w X Y : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * X i * Y i) ^ 2 ≤ (∑ i, w i * X i * X i) * (∑ i, w i * Y i * Y i) := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (w i) * X i)
    (fun i => Real.sqrt (w i) * Y i)
  have e : ∀ i, Real.sqrt (w i) * Real.sqrt (w i) = w i := fun i => Real.mul_self_sqrt (hw i)
  have e1 : ∑ i, w i * X i * Y i = ∑ i, Real.sqrt (w i) * X i * (Real.sqrt (w i) * Y i) :=
    Finset.sum_congr rfl fun i _ => by linear_combination (-(X i * Y i)) * e i
  have e2 : ∑ i, w i * X i * X i = ∑ i, (Real.sqrt (w i) * X i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by linear_combination (-(X i ^ 2)) * e i
  have e3 : ∑ i, w i * Y i * Y i = ∑ i, (Real.sqrt (w i) * Y i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by linear_combination (-(Y i ^ 2)) * e i
  rw [e1, e2, e3]; exact this

lemma pf_cs_abs {m : ℕ} (w X Y : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) :
    |∑ i, w i * X i * Y i| ≤
      Real.sqrt (∑ i, w i * X i * X i) * Real.sqrt (∑ i, w i * Y i * Y i) := by
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => by
    have := hw i; have := mul_self_nonneg (X i); nlinarith)]
  apply Real.abs_le_sqrt
  exact pf_cs w X Y hw

lemma pf_nonneg {m : ℕ} (w X : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ ∑ i, w i * X i * X i :=
  Finset.sum_nonneg fun i _ => by have := hw i; have := mul_self_nonneg (X i); nlinarith

lemma pf_tri {m : ℕ} (w X Y : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) :
    Real.sqrt (∑ i, w i * (X i + Y i) * (X i + Y i)) ≤
      Real.sqrt (∑ i, w i * X i * X i) + Real.sqrt (∑ i, w i * Y i * Y i) := by
  have ha := pf_nonneg w X hw
  have hb := pf_nonneg w Y hw
  have hc := le_trans (le_abs_self _) (pf_cs_abs w X Y hw)
  have e : ∑ i, w i * (X i + Y i) * (X i + Y i) =
      (∑ i, w i * X i * X i) + 2 * (∑ i, w i * X i * Y i) + ∑ i, w i * Y i * Y i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [e]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith

lemma pf_smul {m : ℕ} (w X : Fin m → ℝ) (c : ℝ) :
    Real.sqrt (∑ i, w i * (c * X i) * (c * X i)) = |c| * Real.sqrt (∑ i, w i * X i * X i) := by
  have e : ∑ i, w i * (c * X i) * (c * X i) = c ^ 2 * ∑ i, w i * X i * X i := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [e, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma pf_unit {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) (s w : Fin m → ℝ)
    (hs : ∀ i, 0 < s i) (hw : ∀ i, 0 < w i) : IsUnit (weightedGram A s w) := by
  rw [← mulVec_injective_iff_isUnit]
  intro u v huv
  have hsub : weightedGram A s w *ᵥ (u - v) = 0 := by rw [mulVec_sub, huv, sub_self]
  have hq := pf_quad A s w (u - v) (u - v)
  rw [hsub, dotProduct_zero] at hq
  have hz : ∀ i, (A *ᵥ (u - v)) i = 0 := by
    intro i
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by
      have := hw j; have := mul_self_nonneg ((A *ᵥ (u - v)) j / s j); nlinarith)).mp
        hq.symm i (Finset.mem_univ _)
    have h1 : (A *ᵥ (u - v)) i / s i * ((A *ᵥ (u - v)) i / s i) = 0 := by
      rw [mul_assoc] at hterm
      exact (mul_eq_zero.mp hterm).resolve_left (hw i).ne'
    have h2 := mul_self_eq_zero.mp h1
    rwa [div_eq_zero_iff, or_iff_left (hs i).ne'] at h2
  have h3 : A *ᵥ (u - v) = A *ᵥ 0 := by ext i; simp [hz i]
  exact sub_eq_zero.mp (pf_inj A hA h3)

lemma pf_inv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) (s w : Fin m → ℝ)
    (hs : ∀ i, 0 < s i) (hw : ∀ i, 0 < w i) (v : Fin n → ℝ) :
    weightedGram A s w *ᵥ ((weightedGram A s w)⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (pf_unit A hA s w hs hw)),
    one_mulVec]

lemma pf_mn {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ) (v : Fin n → ℝ) :
    matNorm (weightedGram A s w) v =
      Real.sqrt (∑ i, w i * ((A *ᵥ v) i / s i) * ((A *ᵥ v) i / s i)) := by
  rw [matNorm, pf_quad]

lemma pf_mn_add {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i)
    (u v : Fin n → ℝ) :
    matNorm (weightedGram A s w) (u + v) ≤
      matNorm (weightedGram A s w) u + matNorm (weightedGram A s w) v := by
  simp only [pf_mn]
  have e : ∀ i, (A *ᵥ (u + v)) i / s i = (A *ᵥ u) i / s i + (A *ᵥ v) i / s i := by
    intro i; rw [mulVec_add, Pi.add_apply, add_div]
  simp_rw [e]
  exact pf_tri w (fun i => (A *ᵥ u) i / s i) (fun i => (A *ᵥ v) i / s i) hw

lemma pf_mn_smul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ) (c : ℝ)
    (v : Fin n → ℝ) :
    matNorm (weightedGram A s w) (c • v) = |c| * matNorm (weightedGram A s w) v := by
  simp only [pf_mn]
  have e : ∀ i, (A *ᵥ (c • v)) i / s i = c * ((A *ᵥ v) i / s i) := by
    intro i; rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc]
  simp_rw [e]
  exact pf_smul w (fun i => (A *ᵥ v) i / s i) c

theorem cpp_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hA : A.rank = n) (x : Fin n → ℝ) (w : Fin m → ℝ)
    (hxw : IsFeasible A b x w) (α t : ℝ) (hα : 0 ≤ α) (ht : 0 ≤ t) :
    centrality A b c ((1 + α) * t) x w ≤
      (1 + α) * centrality A b c t x w + α * Real.sqrt (∑ i, |w i|) := by
  obtain ⟨hx, hw⟩ := hxw
  have hs : ∀ i, 0 < slack A b x i := hx
  have hwn : ∀ i, 0 ≤ w i := fun i => (hw i).le
  obtain ⟨s, hsd⟩ : ∃ s, s = slack A b x := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, H = weightedGram A s w := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin n → ℝ, q = Aᵀ *ᵥ (diagonal (fun i => (s i)⁻¹) *ᵥ w) := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = H⁻¹ *ᵥ q := ⟨_, rfl⟩
  have hsplit : newtonStep A b c ((1+α)*t) x w = (1+α) • newtonStep A b c t x w + α • k := by
    unfold newtonStep weightedGradient
    rw [hk, hH, hq, hsd, ← mulVec_smul, ← mulVec_smul, ← mulVec_add]
    congr 1
    ext j; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  unfold centrality
  rw [hsplit, ← hsd, ← hH]
  have hkb : matNorm H k ≤ Real.sqrt (∑ i, |w i|) := by
    have hs' : ∀ i, 0 < s i := by rw [hsd]; exact hs
    have hHk : H *ᵥ k = q := by rw [hk, hH]; exact pf_inv A hA s w hs' hw q
    have hT := pf_quad A s w k k
    rw [← hH, hHk] at hT
    have hT2 : k ⬝ᵥ q = ∑ i, w i * ((A *ᵥ k) i / s i) * 1 := by
      rw [hq, dotProduct_mulVec, vecMul_transpose]
      simp only [mulVec_diagonal, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [div_eq_mul_inv]; ring
    have hcs := pf_cs w (fun i => (A *ᵥ k) i / s i) (fun _ => 1) hwn
    rw [← hT2, ← hT] at hcs
    have hT0 : 0 ≤ k ⬝ᵥ q := by rw [hT]; exact pf_nonneg w _ hwn
    have hle : k ⬝ᵥ q ≤ ∑ i, |w i| := by
      have e : ∑ i, w i * 1 * 1 = ∑ i, |w i| :=
        Finset.sum_congr rfl fun i _ => by rw [abs_of_pos (hw i)]; ring
      rw [e] at hcs
      rcases hT0.lt_or_eq with h | h
      · nlinarith
      · rw [← h]; exact Finset.sum_nonneg fun i _ => abs_nonneg _
    rw [matNorm, hHk]
    exact Real.sqrt_le_sqrt hle
  calc matNorm H ((1 + α) • newtonStep A b c t x w + α • k)
      ≤ matNorm H ((1 + α) • newtonStep A b c t x w) + matNorm H (α • k) := by
        rw [hH]; exact pf_mn_add A s w hwn _ _
    _ = (1 + α) * matNorm H (newtonStep A b c t x w) + α * matNorm H k := by
        rw [hH, pf_mn_smul, pf_mn_smul, abs_of_nonneg (by linarith), abs_of_nonneg hα]
    _ ≤ _ := by gcongr


lemma pf_gamma {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) (s w : Fin m → ℝ)
    (hs : ∀ i, 0 < s i) (hw : ∀ i, 0 < w i) (v : Fin n → ℝ) (i : Fin m) :
    |(A *ᵥ v) i / s i| ≤ slackSensitivity A s w * matNorm (weightedGram A s w) v := by
  have hwn : ∀ i, 0 ≤ w i := fun i => (hw i).le
  obtain ⟨q, hq⟩ : ∃ q : Fin n → ℝ, q = Aᵀ *ᵥ Pi.single i (s i)⁻¹ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = (weightedGram A s w)⁻¹ *ᵥ q := ⟨_, rfl⟩
  have hHz : weightedGram A s w *ᵥ z = q := by rw [hz]; exact pf_inv A hA s w hs hw q
  have h1 : (A *ᵥ v) i / s i = v ⬝ᵥ (weightedGram A s w *ᵥ z) := by
    rw [hHz, hq, dotProduct_mulVec, vecMul_transpose, dotProduct_single, div_eq_mul_inv]
  have h2 : |(A *ᵥ v) i / s i| ≤
      matNorm (weightedGram A s w) v * matNorm (weightedGram A s w) z := by
    rw [h1, pf_quad, pf_mn, pf_mn]; exact pf_cs_abs w _ _ hwn
  have h3 : matNorm (weightedGram A s w) z ≤ slackSensitivity A s w := by
    have hle := le_ciSup (f := fun j : Fin m => matNorm (projectionMatrix A s w)
      (diagonal (fun k => (Real.sqrt (w k))⁻¹) *ᵥ Pi.single j (1 : ℝ)))
      (Set.finite_range _).bddAbove i
    refine le_of_eq_of_le ?_ hle
    simp only [matNorm]
    congr 1
    rw [hHz]
    have e1 : diagonal (fun i => (s i)⁻¹) *ᵥ (diagonal (fun i => Real.sqrt (w i)) *ᵥ
        (diagonal (fun k => (Real.sqrt (w k))⁻¹) *ᵥ Pi.single i (1:ℝ))) =
        Pi.single i (s i)⁻¹ := by
      ext j; simp only [mulVec_diagonal, Pi.single_apply]; split_ifs with h
      · subst h; field_simp [(Real.sqrt_pos.mpr (hw j)).ne']
      · simp
    unfold projectionMatrix
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
      ← mulVec_mulVec, e1, ← hq, ← hz]
    rw [hq, dotProduct_mulVec, vecMul_transpose, dotProduct_single]
    simp [dotProduct, mulVec_diagonal, Pi.single_apply]
    rw [← mulVec_mulVec, mulVec_diagonal]
    field_simp [(Real.sqrt_pos.mpr (hw i)).ne']
  have h4 : 0 ≤ matNorm (weightedGram A s w) v := Real.sqrt_nonneg _
  calc _ ≤ _ := h2
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right h3 h4

lemma alg1 (w s Y E a : ℝ) (hs : s ≠ 0) (hd : 1 - a * E ≠ 0) :
    w * (Y / s) * E + Y * (s⁻¹ * w - (s * (1 - a * E))⁻¹ * (w * (1 + (1 - a) * E))) =
      w * (Y / s) * (-(a * E ^ 2 / (1 - a * E))) := by
  have hd' : 1 - E * a ≠ 0 := by rwa [mul_comm] at hd
  field_simp
  ring

lemma alg_bd (E a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hE : |E| ≤ 1 / 8) :
    -(1/8) ≤ a * E ∧ a * E ≤ 1 / 8 ∧ -(1/8) ≤ E ∧ E ≤ 1/8 := by
  have := abs_le.mp hE
  refine ⟨by nlinarith, by nlinarith, by linarith, by linarith⟩

lemma alg2 (w u E a : ℝ) (hw : 0 ≤ w) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hE : |E| ≤ 1 / 8) :
    56 / 81 * (w * u * u) ≤ (w * (1 + (1 - a) * E)) * (u / (1 - a * E)) * (u / (1 - a * E)) := by
  obtain ⟨h1, h2, h3, h4⟩ := alg_bd E a ha0 ha1 hE
  have hd : 0 < 1 - a * E := by linarith
  have e : (w * (1 + (1 - a) * E)) * (u / (1 - a * E)) * (u / (1 - a * E)) =
      (w * u * u) * ((1 + (1 - a) * E) / (1 - a * E) ^ 2) := by
    field_simp
  rw [e]
  have hq : 56 / 81 ≤ (1 + (1 - a) * E) / (1 - a * E) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have : 0 ≤ w * u * u := by have := mul_self_nonneg u; nlinarith
  have := mul_le_mul_of_nonneg_left hq this
  linarith

lemma alg3 (w E a K : ℝ) (hw : 0 ≤ w) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hE : |E| ≤ K)
    (hK : K ≤ 1 / 8) :
    w * (-(a * E ^ 2 / (1 - a * E))) * (-(a * E ^ 2 / (1 - a * E))) ≤
      a ^ 2 * (64 / 49) * K ^ 2 * (w * E * E) := by
  obtain ⟨h1, h2, h3, h4⟩ := alg_bd E a ha0 ha1 (le_trans hE hK)
  have hd : 0 < 1 - a * E := by linarith
  have e : w * (-(a * E ^ 2 / (1 - a * E))) * (-(a * E ^ 2 / (1 - a * E))) =
      (w * E * E * a ^ 2) * (E ^ 2 / (1 - a * E) ^ 2) := by
    field_simp
  rw [e]
  have hE2 : E ^ 2 ≤ K ^ 2 := by
    have := abs_nonneg E
    rw [← sq_abs E]; exact pow_le_pow_left₀ this hE 2
  have hq : E ^ 2 / (1 - a * E) ^ 2 ≤ 64 / 49 * K ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : 49 / 64 ≤ (1 - a * E) ^ 2 := by nlinarith
    have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
    nlinarith
  have : 0 ≤ w * E * E * a ^ 2 :=
    mul_nonneg (by rw [mul_assoc]; exact mul_nonneg hw (mul_self_nonneg E)) (sq_nonneg a)
  calc (w * E * E * a ^ 2) * (E ^ 2 / (1 - a * E) ^ 2)
      ≤ (w * E * E * a ^ 2) * (64 / 49 * K ^ 2) := mul_le_mul_of_nonneg_left hq this
    _ = _ := by ring


theorem sns_main {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hA : A.rank = n) (t r : ℝ) (hr : 0 ≤ r)
    (xOld : Fin n → ℝ) (wOld : Fin m → ℝ) (hfeas : IsFeasible A b xOld wOld)
    (hδ : centrality A b c t xOld wOld ≤
      1 / (8 * slackSensitivity A (slack A b xOld) wOld))
    (h : Fin n → ℝ) (hh : h = newtonStep A b c t xOld wOld)
    (xNew : Fin n → ℝ) (hxN : xNew = xOld - (1 / (1 + r)) • h)
    (wNew : Fin m → ℝ) (hwN : wNew = wOld + (r / (1 + r)) •
      ((diagonal wOld * diagonal (fun i => (slack A b xOld i)⁻¹) * A) *ᵥ h)) :
    IsFeasible A b xNew wNew ∧
      centrality A b c t xNew wNew ≤
        2 / (1 + r) * slackSensitivity A (slack A b xOld) wOld *
          centrality A b c t xOld wOld ^ 2 := by
  obtain ⟨hx, hw⟩ := hfeas
  have hs0 : ∀ i, 0 < slack A b xOld i := hx
  have hwn : ∀ i, 0 ≤ wOld i := fun i => (hw i).le
  obtain ⟨s, hsd⟩ : ∃ s, slack A b xOld = s := ⟨_, rfl⟩
  have hs : ∀ i, 0 < s i := by rw [← hsd]; exact hs0
  obtain ⟨a, had⟩ : ∃ a : ℝ, 1 / (1 + r) = a := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [← had]; positivity
  have ha1 : a ≤ 1 := by rw [← had, div_le_one (by linarith)]; linarith
  have hra : r / (1 + r) = 1 - a := by rw [← had]; field_simp; ring
  rw [had] at hxN
  rw [show 2 / (1 + r) = 2 * a by rw [← had]; ring]
  rw [hra, hsd] at hwN
  rw [hsd] at hδ ⊢
  obtain ⟨γ, hγd⟩ : ∃ γ, slackSensitivity A s wOld = γ := ⟨_, rfl⟩
  rw [hγd] at hδ ⊢
  have hγ0 : 0 ≤ γ := by
    rw [← hγd]; exact Real.iSup_nonneg fun i => Real.sqrt_nonneg _
  have hδd : centrality A b c t xOld wOld = matNorm (weightedGram A s wOld) h := by
    rw [centrality, hh, hsd]
  rw [hδd] at hδ ⊢
  obtain ⟨δ, hδδ⟩ : ∃ δ, matNorm (weightedGram A s wOld) h = δ := ⟨_, rfl⟩
  rw [hδδ] at hδ ⊢
  have hδ0 : 0 ≤ δ := by rw [← hδδ]; exact Real.sqrt_nonneg _
  have hK : γ * δ ≤ 1 / 8 := by
    rcases hγ0.lt_or_eq with hg | hg
    · rw [le_div_iff₀ (by positivity)] at hδ; nlinarith
    · rw [← hg]; norm_num
  -- η
  have hη : ∀ i, |(A *ᵥ h) i / s i| ≤ γ * δ := by
    intro i; rw [← hγd, ← hδδ]; exact pf_gamma A hA s wOld hs hw h i
  have hη8 : ∀ i, |(A *ᵥ h) i / s i| ≤ 1 / 8 := fun i => le_trans (hη i) hK
  -- new slack and weights
  have hsN : ∀ i, slack A b xNew i = s i * (1 - a * ((A *ᵥ h) i / s i)) := by
    intro i
    have := congrFun hsd i
    simp only [slack, Pi.sub_apply] at this ⊢
    rw [hxN, mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [(hs i).ne']
    linarith
  have hwN' : ∀ i, wNew i = wOld i * (1 + (1 - a) * ((A *ᵥ h) i / s i)) := by
    intro i
    rw [hwN, ← mulVec_mulVec, ← mulVec_mulVec, Pi.add_apply, Pi.smul_apply, mulVec_diagonal,
      mulVec_diagonal, smul_eq_mul]
    field_simp [(hs i).ne']
  have hd : ∀ i, 0 < 1 - a * ((A *ᵥ h) i / s i) := fun i => by
    obtain ⟨h1, h2, h3, h4⟩ := alg_bd _ a ha0 ha1 (hη8 i); linarith
  have hp : ∀ i, 0 < 1 + (1 - a) * ((A *ᵥ h) i / s i) := fun i => by
    obtain ⟨h1, h2, h3, h4⟩ := alg_bd _ a ha0 ha1 (hη8 i); nlinarith
  have hsNp : ∀ i, 0 < slack A b xNew i := fun i => by rw [hsN]; exact mul_pos (hs i) (hd i)
  have hwNp : ∀ i, 0 < wNew i := fun i => by rw [hwN']; exact mul_pos (hw i) (hp i)
  refine ⟨⟨hsNp, hwNp⟩, ?_⟩
  -- new centrality
  obtain ⟨y, hy⟩ : ∃ y, newtonStep A b c t xNew wNew = y := ⟨_, rfl⟩
  have hHy : weightedGram A (slack A b xNew) wNew *ᵥ y = weightedGradient A b c t xNew wNew := by
    rw [← hy]; exact pf_inv A hA _ _ hsNp hwNp _
  have hHh : weightedGram A s wOld *ᵥ h = weightedGradient A b c t xOld wOld := by
    rw [hh, newtonStep, hsd]; exact pf_inv A hA _ _ hs hw _
  have hG' : weightedGradient A b c t xNew wNew = weightedGram A s wOld *ᵥ h +
      Aᵀ *ᵥ (fun i => (s i)⁻¹ * wOld i - (slack A b xNew i)⁻¹ * wNew i) := by
    rw [hHh]
    unfold weightedGradient
    rw [hsd, show (fun i => (s i)⁻¹ * wOld i - (slack A b xNew i)⁻¹ * wNew i) =
      (diagonal fun i => (s i)⁻¹) *ᵥ wOld - (diagonal fun i => (slack A b xNew i)⁻¹) *ᵥ wNew
      from by ext i; simp [mulVec_diagonal], mulVec_sub]
    abel
  -- quadratic identities
  have hQ : y ⬝ᵥ (weightedGram A (slack A b xNew) wNew *ᵥ y) =
      ∑ i, wOld i * ((A *ᵥ y) i / s i) * (-(a * ((A *ᵥ h) i / s i) ^ 2 /
        (1 - a * ((A *ᵥ h) i / s i)))) := by
    rw [hHy, hG', dotProduct_add, pf_quad, dotProduct_mulVec, vecMul_transpose]
    simp only [dotProduct]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsN, hwN']
    exact alg1 _ _ _ _ _ (hs i).ne' (hd i).ne'
  have hQ2 : y ⬝ᵥ (weightedGram A (slack A b xNew) wNew *ᵥ y) =
      ∑ i, wNew i * ((A *ᵥ y) i / slack A b xNew i) * ((A *ᵥ y) i / slack A b xNew i) :=
    pf_quad _ _ _ _ _
  have hY : 56 / 81 * ∑ i, wOld i * ((A *ᵥ y) i / s i) * ((A *ᵥ y) i / s i) ≤
      y ⬝ᵥ (weightedGram A (slack A b xNew) wNew *ᵥ y) := by
    rw [hQ2, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hsN, hwN', ← div_div]
    exact alg2 _ _ _ _ (hwn i) ha0 ha1 (hη8 i)
  have hV : ∑ i, wOld i * (-(a * ((A *ᵥ h) i / s i) ^ 2 / (1 - a * ((A *ᵥ h) i / s i)))) *
      (-(a * ((A *ᵥ h) i / s i) ^ 2 / (1 - a * ((A *ᵥ h) i / s i)))) ≤
      a ^ 2 * (64 / 49) * (γ * δ) ^ 2 * δ ^ 2 := by
    have hδ2 : δ ^ 2 = ∑ i, wOld i * ((A *ᵥ h) i / s i) * ((A *ᵥ h) i / s i) := by
      rw [← hδδ, pf_mn, Real.sq_sqrt (pf_nonneg _ _ hwn)]
    rw [hδ2, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => alg3 _ _ _ _ (hwn i) ha0 ha1 (hη i) hK
  have hcs := pf_cs wOld (fun i => (A *ᵥ y) i / s i)
    (fun i => -(a * ((A *ᵥ h) i / s i) ^ 2 / (1 - a * ((A *ᵥ h) i / s i)))) hwn
  rw [← hQ] at hcs
  obtain ⟨T, hT⟩ : ∃ T, y ⬝ᵥ (weightedGram A (slack A b xNew) wNew *ᵥ y) = T := ⟨_, rfl⟩
  rw [hT] at hcs hY
  have hT0 : 0 ≤ T := by
    rw [← hT, hQ2]; exact pf_nonneg _ _ fun i => (hwNp i).le
  have hY0 := pf_nonneg wOld (fun i => (A *ᵥ y) i / s i) hwn
  have hV0 := pf_nonneg wOld (fun i => -(a * ((A *ᵥ h) i / s i) ^ 2 /
    (1 - a * ((A *ᵥ h) i / s i)))) hwn
  have hcen : centrality A b c t xNew wNew = Real.sqrt T := by
    rw [centrality, hy, matNorm, hT]
  rw [hcen]
  -- T^2 ≤ Y V ≤ (81/56) T * a^2 (64/49) K^2 δ^2
  have hTb : T ≤ (81 / 56) * (a ^ 2 * (64 / 49) * (γ * δ) ^ 2 * δ ^ 2) := by
    rcases hT0.lt_or_eq with hTp | hTz
    · have h1 : T ^ 2 ≤ (81 / 56 * T) * (a ^ 2 * (64 / 49) * (γ * δ) ^ 2 * δ ^ 2) := by
        calc T ^ 2 ≤ _ := hcs
          _ ≤ _ := mul_le_mul (by linarith) hV hV0 (by linarith)
      nlinarith
    · rw [← hTz]; positivity
  have hR : 0 ≤ 2 * a * γ * δ ^ 2 := by positivity
  refine Real.sqrt_le_iff.mpr ⟨hR, ?_⟩
  have e : (2 * a * γ * δ ^ 2) ^ 2 = 4 * (a ^ 2 * (γ * δ) ^ 2 * δ ^ 2) := by ring
  have : 0 ≤ a ^ 2 * (γ * δ) ^ 2 * δ ^ 2 := by positivity
  rw [e]; nlinarith


theorem sns_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hA : A.rank = n) (t r : ℝ) (hr : 0 ≤ r)
    (xOld : Fin n → ℝ) (wOld : Fin m → ℝ) (hfeas : IsFeasible A b xOld wOld)
    (hδ : centrality A b c t xOld wOld ≤
      1 / (8 * slackSensitivity A (slack A b xOld) wOld)) :
    let h := newtonStep A b c t xOld wOld
    let xNew := xOld - (1 / (1 + r)) • h
    let wNew := wOld + (r / (1 + r)) •
      ((diagonal wOld * diagonal (fun i => (slack A b xOld i)⁻¹) * A) *ᵥ h)
    IsFeasible A b xNew wNew ∧
      centrality A b c t xNew wNew ≤
        2 / (1 + r) * slackSensitivity A (slack A b xOld) wOld *
          centrality A b c t xOld wOld ^ 2 := by
  intro h xNew wNew
  exact sns_main A b c hA t r hr xOld wOld hfeas hδ h rfl xNew rfl wNew rfl

end PathFindingLP.Centering

open PathFindingLP.Centering


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hA : A.rank = n) (t r : ℝ) (hr : 0 ≤ r)
    (xOld : Fin n → ℝ) (wOld : Fin m → ℝ) (hfeas : IsFeasible A b xOld wOld)
    (hδ : centrality A b c t xOld wOld ≤
      1 / (8 * slackSensitivity A (slack A b xOld) wOld)) :
    let h := newtonStep A b c t xOld wOld
    let xNew := xOld - (1 / (1 + r)) • h
    let wNew := wOld + (r / (1 + r)) •
      ((diagonal wOld * diagonal (fun i => (slack A b xOld i)⁻¹) * A) *ᵥ h)
    IsFeasible A b xNew wNew ∧
      centrality A b c t xNew wNew ≤
        2 / (1 + r) * slackSensitivity A (slack A b xOld) wOld *
          centrality A b c t xOld wOld ^ 2 := by
  exact sns_core A b c hA t r hr xOld wOld hfeas hδ
