-- Prove2me | solution 1 for PathFindingLP.Centering.centering_with_weights
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T23:01:51.331545+00:00
-- url     : https://prove2.me/submissions/af7d3081-4bf0-454d-b307-8ef646649b4e

import Mathlib
import Definitions.Def_PathFindingLP_Centering_WeightFunction

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


lemma dn_nonneg {m : ℕ} (g y : Fin m → ℝ) : 0 ≤ diagNorm g y := Real.sqrt_nonneg _

lemma dn_sq {m : ℕ} (g y : Fin m → ℝ) (hg : ∀ i, 0 ≤ g i) :
    diagNorm g y ^ 2 = ∑ i, g i * y i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_nonneg (hg i) (sq_nonneg _))

lemma dn_le {m : ℕ} (g g' u v : Fin m → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ i, g i * u i ^ 2 ≤ K ^ 2 * (g' i * v i ^ 2)) : diagNorm g u ≤ K * diagNorm g' v := by
  unfold diagNorm
  rw [← Real.sqrt_sq hK, ← Real.sqrt_mul (sq_nonneg K), Finset.mul_sum]
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => h i)

lemma dn_add {m : ℕ} (g u v : Fin m → ℝ) (hg : ∀ i, 0 ≤ g i) :
    diagNorm g (u + v) ≤ diagNorm g u + diagNorm g v := by
  have hu := dn_sq g u hg
  have hv := dn_sq g v hg
  have huv := dn_sq g (u + v) hg
  have h0 := dn_nonneg g u
  have h1 := dn_nonneg g v
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (g i) * u i)
    (fun i => Real.sqrt (g i) * v i)
  have e : ∀ i, Real.sqrt (g i) ^ 2 = g i := fun i => Real.sq_sqrt (hg i)
  have e1 : ∑ i, Real.sqrt (g i) * u i * (Real.sqrt (g i) * v i) = ∑ i, g i * u i * v i :=
    Finset.sum_congr rfl fun i _ => by linear_combination (u i * v i) * e i
  have e2 : ∑ i, (Real.sqrt (g i) * u i) ^ 2 = ∑ i, g i * u i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by linear_combination (u i ^ 2) * e i
  have e3 : ∑ i, (Real.sqrt (g i) * v i) ^ 2 = ∑ i, g i * v i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by linear_combination (v i ^ 2) * e i
  rw [e1, e2, e3, ← hu, ← hv] at hcs
  have e4 : ∑ i, g i * (u + v) i ^ 2 =
      ∑ i, g i * u i ^ 2 + 2 * ∑ i, g i * u i * v i + ∑ i, g i * v i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_; simp only [Pi.add_apply]; ring
  rw [e4, ← hu, ← hv] at huv
  have h2 := dn_nonneg g (u + v)
  have hX : ∑ i, g i * u i * v i ≤ diagNorm g u * diagNorm g v := by
    have hsq : (∑ i, g i * u i * v i) ^ 2 ≤ (diagNorm g u * diagNorm g v) ^ 2 := by
      rw [mul_pow]; exact hcs
    have := abs_le_of_sq_le_sq' hsq (mul_nonneg h0 h1)
    linarith [this.2]
  nlinarith

lemma dn_cs {m : ℕ} (g u v : Fin m → ℝ) (hg : ∀ i, 0 ≤ g i) :
    |∑ i, g i * u i * v i| ≤ diagNorm g u * diagNorm g v := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (g i) * u i)
    (fun i => Real.sqrt (g i) * v i)
  have e : ∀ i, Real.sqrt (g i) ^ 2 = g i := fun i => Real.sq_sqrt (hg i)
  have e1 : ∑ i, Real.sqrt (g i) * u i * (Real.sqrt (g i) * v i) = ∑ i, g i * u i * v i :=
    Finset.sum_congr rfl fun i _ => by linear_combination (u i * v i) * e i
  have e2 : ∑ i, (Real.sqrt (g i) * u i) ^ 2 = ∑ i, g i * u i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by linear_combination (u i ^ 2) * e i
  have e3 : ∑ i, (Real.sqrt (g i) * v i) ^ 2 = ∑ i, g i * v i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by linear_combination (v i ^ 2) * e i
  rw [e1, e2, e3, ← dn_sq g u hg, ← dn_sq g v hg] at hcs
  have hsq : (∑ i, g i * u i * v i) ^ 2 ≤ (diagNorm g u * diagNorm g v) ^ 2 := by
    rw [mul_pow]; exact hcs
  exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (mul_nonneg (dn_nonneg _ _) (dn_nonneg _ _)))

lemma exp_le_q (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  have := Real.exp_bound (x := x) (by rw [abs_of_nonneg h0]; exact h1) (n := 2) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at this
  have := (abs_le.mp this).2
  nlinarith

lemma one_sub_exp_neg_sq (z : ℝ) : (1 - Real.exp (-z)) ^ 2 ≤ z ^ 2 * Real.exp (2 * |z|) := by
  rcases le_or_gt 0 z with hz | hz
  · have h1 := Real.add_one_le_exp (-z)
    have h2 : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 : 1 ≤ Real.exp (2 * |z|) := Real.one_le_exp (by positivity)
    have : (1 - Real.exp (-z)) ^ 2 ≤ z ^ 2 := by
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    nlinarith [sq_nonneg z]
  · have h1 := Real.add_one_le_exp z
    have hp : 0 < Real.exp (-z) := Real.exp_pos _
    have hm : Real.exp z * Real.exp (-z) = 1 := by rw [← Real.exp_add]; simp
    have h2 : Real.exp (-z) - 1 ≤ -z * Real.exp (-z) := by nlinarith
    have h3 : 1 ≤ Real.exp (-z) := Real.one_le_exp (by linarith)
    have e : Real.exp (2 * |z|) = Real.exp (-z) ^ 2 := by
      rw [abs_of_neg hz, sq, ← Real.exp_add]; ring_nf
    rw [e]
    have : (Real.exp (-z) - 1) ^ 2 ≤ (-z * Real.exp (-z)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h2 2
    nlinarith

lemma log_bd (u : ℝ) (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u)| ≤ 2 * |u| ∧ |u - Real.log (1 + u)| ≤ 2 * u ^ 2 := by
  have hu' := abs_le.mp hu
  have hp : 0 < 1 + u := by linarith
  have h1 := Real.log_le_sub_one_of_pos hp
  have h2 := Real.one_sub_inv_le_log_of_pos hp
  have e : 1 - (1 + u)⁻¹ = u - u ^ 2 / (1 + u) := by field_simp; ring
  have h3 : u ^ 2 / (1 + u) ≤ 2 * u ^ 2 := by
    rw [div_le_iff₀ hp]; nlinarith [sq_nonneg u]
  have h4 : 0 ≤ u ^ 2 / (1 + u) := by positivity
  constructor
  · rw [abs_le]; constructor
    · rcases le_or_gt 0 u with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · rw [abs_of_neg h]; nlinarith
    · rcases le_or_gt 0 u with h | h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_neg h]; nlinarith
  · rw [abs_le]; constructor <;> nlinarith

lemma boot {m : ℕ} (f f' : Fin m → ℝ → ℝ) (c c' : ℝ) (hc : c' < c) (hc0 : 0 ≤ c')
    (hd : ∀ i, ∀ τ ∈ Set.Icc (0:ℝ) 1, HasDerivAt (f i) (f' i τ) τ)
    (hb : ∀ τ ∈ Set.Icc (0:ℝ) 1, (∀ i, |f i τ - f i 0| ≤ c) → ∀ i, |f' i τ| ≤ c') :
    ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ i, |f i τ - f i 0| ≤ c := by
  by_contra hne
  push_neg at hne
  have hcont : ∀ i, ContinuousOn (f i) (Set.Icc 0 1) := fun i τ hτ =>
    (hd i τ hτ).continuousAt.continuousWithinAt
  let S := ⋃ i, (Set.Icc (0:ℝ) 1 ∩ (fun τ => |f i τ - f i 0|) ⁻¹' Set.Ici c)
  have hSne : S.Nonempty := by
    obtain ⟨τ, hτ, i, hi⟩ := hne; exact ⟨τ, Set.mem_iUnion.mpr ⟨i, hτ, hi.le⟩⟩
  have hSc : IsClosed S := by
    refine isClosed_iUnion_of_finite fun i => ?_
    exact ContinuousOn.preimage_isClosed_of_isClosed
      (((hcont i).sub continuousOn_const).abs) isClosed_Icc isClosed_Ici
  have hbdd : BddBelow S := ⟨0, fun x hx => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx; exact hi.1.1⟩
  have hmem := hSc.csInf_mem hSne hbdd
  obtain ⟨i, ⟨h0, h1⟩, hi⟩ := Set.mem_iUnion.mp hmem
  simp only [Set.mem_preimage, Set.mem_Ici] at hi
  have hlt : ∀ σ ∈ Set.Icc (0:ℝ) 1, σ < sInf S → ∀ j, |f j σ - f j 0| ≤ c := by
    intro σ hσ hσl j
    by_contra h
    push_neg at h
    have : sInf S ≤ σ := csInf_le hbdd (Set.mem_iUnion.mpr ⟨j, hσ, h.le⟩)
    linarith
  have hpos : 0 < sInf S := by
    rcases h0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hi; simp at hi; linarith
  obtain ⟨ξ, hξ, heq⟩ := exists_hasDerivAt_eq_slope (f i) (f' i) hpos
    ((hcont i).mono (Set.Icc_subset_Icc le_rfl h1))
    (fun x hx => hd i x ⟨hx.1.le, hx.2.le.trans h1⟩)
  have hξI : ξ ∈ Set.Icc (0:ℝ) 1 := ⟨hξ.1.le, hξ.2.le.trans h1⟩
  have hbd := hb ξ hξI (hlt ξ hξI hξ.2) i
  rw [heq, sub_zero, abs_div, abs_of_pos hpos, div_le_iff₀ hpos] at hbd
  nlinarith

lemma mvt_dn {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) (F F' : Fin m → ℝ → ℝ)
    (hd : ∀ i, ∀ τ ∈ Set.Icc (0:ℝ) 1, HasDerivAt (F i) (F' i τ) τ) (B : ℝ)
    (hB : ∀ τ ∈ Set.Icc (0:ℝ) 1, diagNorm w (fun i => F' i τ) ≤ B) :
    diagNorm w (fun i => F i 1 - F i 0) ≤ B := by
  obtain ⟨v, hv⟩ : ∃ v : Fin m → ℝ, v = fun i => F i 1 - F i 0 := ⟨_, rfl⟩
  rw [← hv]
  have hψ : ∀ τ ∈ Set.Icc (0:ℝ) 1, HasDerivAt (fun τ => ∑ i, w i * v i * F i τ)
      (∑ i, w i * v i * F' i τ) τ := fun τ hτ =>
    HasDerivAt.fun_sum fun i _ => (hd i τ hτ).const_mul (w i * v i)
  obtain ⟨ξ, hξ, heq⟩ := exists_hasDerivAt_eq_slope (fun τ => ∑ i, w i * v i * F i τ) _
    zero_lt_one (fun τ hτ => (hψ τ hτ).continuousAt.continuousWithinAt)
    (fun x hx => hψ x ⟨hx.1.le, hx.2.le⟩)
  have e : (∑ i, w i * v i * F i 1) - (∑ i, w i * v i * F i 0) = diagNorm w v ^ 2 := by
    rw [dn_sq w v hw, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hv]; ring
  rw [e, sub_zero, div_one] at heq
  have hcs : |∑ i, w i * v i * F' i ξ| ≤ diagNorm w v * diagNorm w (fun i => F' i ξ) :=
    dn_cs w v (fun i => F' i ξ) hw
  rw [heq] at hcs
  have hB' := hB ξ ⟨hξ.1.le, hξ.2.le⟩
  have h0 := dn_nonneg w v
  have h1 := dn_nonneg w (fun i => F' i ξ)
  have h2 := le_abs_self (diagNorm w v ^ 2)
  nlinarith

lemma cen_dn {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (t : ℝ)
    (x : Fin n → ℝ) (w : Fin m → ℝ) :
    centrality A b c t x w = diagNorm w
      (fun i => (A *ᵥ newtonStep A b c t x w) i / slack A b x i) := by
  rw [centrality, pf_mn, diagNorm]
  congr 1; refine Finset.sum_congr rfl fun i _ => ?_; ring

lemma wc {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) (hs : ∀ i, 0 < slack A b x i)
    (w1 w2 : Fin m → ℝ) (hw1 : ∀ i, 0 < w1 i) (hw2 : ∀ i, 0 < w2 i) (K : ℝ) (hK : 0 ≤ K)
    (hK2 : ∀ i, w1 i ≤ K ^ 2 * w2 i) :
    centrality A b c t x w2 ≤
      K * centrality A b c t x w1 + diagNorm w2 (fun i => (w2 i - w1 i) / w2 i) := by
  rw [cen_dn, cen_dn]
  obtain ⟨s, hsd⟩ : ∃ s, slack A b x = s := ⟨_, rfl⟩
  have hs' : ∀ i, 0 < s i := by rw [← hsd]; exact hs
  obtain ⟨y1, hy1⟩ : ∃ y, newtonStep A b c t x w1 = y := ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y, newtonStep A b c t x w2 = y := ⟨_, rfl⟩
  rw [hy1, hy2, hsd]
  have hH1 : weightedGram A s w1 *ᵥ y1 = weightedGradient A b c t x w1 := by
    rw [← hy1, newtonStep, hsd]; exact pf_inv A hA _ _ hs' hw1 _
  have hH2 : weightedGram A s w2 *ᵥ y2 = weightedGradient A b c t x w2 := by
    rw [← hy2, newtonStep, hsd]; exact pf_inv A hA _ _ hs' hw2 _
  have hg : weightedGradient A b c t x w2 = weightedGradient A b c t x w1 -
      Aᵀ *ᵥ (fun i => (s i)⁻¹ * (w2 i - w1 i)) := by
    unfold weightedGradient
    rw [hsd, show (fun i => (s i)⁻¹ * (w2 i - w1 i)) =
      (diagonal fun i => (s i)⁻¹) *ᵥ w2 - (diagonal fun i => (s i)⁻¹) *ᵥ w1
      from by ext i; simp [mulVec_diagonal]; ring, mulVec_sub]
    abel
  obtain ⟨p, hp⟩ : ∃ p : Fin m → ℝ, p = fun i => (A *ᵥ y2) i / s i := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin m → ℝ, q = fun i => (A *ᵥ y1) i / s i := ⟨_, rfl⟩
  rw [← hp, ← hq]
  have hw1n : ∀ i, 0 ≤ w1 i := fun i => (hw1 i).le
  have hw2n : ∀ i, 0 ≤ w2 i := fun i => (hw2 i).le
  have e1 : y2 ⬝ᵥ (weightedGram A s w2 *ᵥ y2) = diagNorm w2 p ^ 2 := by
    rw [pf_quad, dn_sq _ _ hw2n, hp]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  have e2 : y2 ⬝ᵥ (weightedGram A s w2 *ᵥ y2) =
      ∑ i, w1 i * p i * q i - ∑ i, w2 i * p i * ((w2 i - w1 i) / w2 i) := by
    rw [hH2, hg, dotProduct_sub, ← hH1, pf_quad, dotProduct_mulVec, vecMul_transpose, hp, hq]
    congr 1
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp [(hw2 i).ne', (hs' i).ne']
  have h1 := le_abs_self (∑ i, w1 i * p i * q i)
  have h2 := neg_abs_le (∑ i, w2 i * p i * ((w2 i - w1 i) / w2 i))
  have c1 := dn_cs w1 p q hw1n
  have c2 := dn_cs w2 p (fun i => (w2 i - w1 i) / w2 i) hw2n
  have c3 : diagNorm w1 p ≤ K * diagNorm w2 p := dn_le _ _ _ _ K hK fun i => by
    have := hK2 i; have := sq_nonneg (p i); nlinarith
  have d0 := dn_nonneg w2 p
  have d1 := dn_nonneg w1 q
  have d2 := dn_nonneg w2 (fun i => (w2 i - w1 i) / w2 i)
  have d3 := dn_nonneg w1 p
  have key : diagNorm w2 p ^ 2 ≤ diagNorm w2 p *
      (K * diagNorm w1 q + diagNorm w2 (fun i => (w2 i - w1 i) / w2 i)) := by
    have : diagNorm w1 p * diagNorm w1 q ≤ K * diagNorm w2 p * diagNorm w1 q :=
      mul_le_mul_of_nonneg_right c3 d1
    nlinarith
  rcases d0.lt_or_eq with h | h
  · nlinarith
  · rw [← h]; positivity

lemma deriv_path {m : ℕ} (g : (Fin m → ℝ) → (Fin m → ℝ)) (s d : Fin m → ℝ) (τ : ℝ)
    (hdiff : DifferentiableAt ℝ g (s + τ • d)) (hpos : ∀ j, 0 < (s + τ • d) j)
    (hgp : ∀ j, 0 < g (s + τ • d) j) (i : Fin m) :
    HasDerivAt (fun τ => Real.log (g (s + τ • d) i))
      (jacobianTerm g (s + τ • d) (fun j => d j / (s + τ • d) j) i) τ := by
  have hγ : HasDerivAt (fun τ : ℝ => s + τ • d) d τ := by
    have := ((hasDerivAt_id τ).smul_const d).const_add s
    simpa using this
  have hc := hdiff.hasFDerivAt.comp_hasDerivAt τ hγ
  have hci := (hasDerivAt_pi.mp hc) i
  have hl := hci.log (hgp i).ne'
  refine HasDerivAt.congr_deriv hl ?_
  unfold jacobianTerm
  have e : (fun j => (s + τ • d) j * (d j / (s + τ • d) j)) = d := by
    ext j; rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ (hpos j).ne'
  rw [e, div_eq_inv_mul]
  rfl

lemma sc_inf {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (g : (Fin m → ℝ) → (Fin m → ℝ))
    (c₁ cγ cr : ℝ) (hg : IsWeightFunction A g c₁ cγ cr) (p : Fin m → ℝ) (hp : ∀ i, 0 < p i)
    (y : Fin m → ℝ) (i : Fin m) :
    |jacobianTerm g p y i| ≤ cr * (2 * ‖y‖ + cr * diagNorm (g p) y) := by
  have hr := hg.one_le_cr
  have h := hg.stepConsistency_inf p hp cr le_rfl y
  have h1 : |(y + cr⁻¹ • jacobianTerm g p y) i| ≤ ‖y + cr⁻¹ • jacobianTerm g p y‖ := by
    have := norm_le_pi_norm (y + cr⁻¹ • jacobianTerm g p y) i
    rwa [Real.norm_eq_abs] at this
  have h2 : |y i| ≤ ‖y‖ := by
    have := norm_le_pi_norm y i
    rwa [Real.norm_eq_abs] at this
  have e : jacobianTerm g p y i = cr * ((y + cr⁻¹ • jacobianTerm g p y) i - y i) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [e, abs_mul, abs_of_pos (by linarith)]
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  calc |(y + cr⁻¹ • jacobianTerm g p y) i - y i|
      ≤ |(y + cr⁻¹ • jacobianTerm g p y) i| + |y i| := abs_sub _ _
    _ ≤ _ := by linarith

lemma alg_y (u τ ρ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hu : |u| ≤ ρ / 200) :
    0 < 1 - τ * u ∧ |-u / (1 - τ * u)| ≤ (1 + ρ / 100) * |u| ∧
      |-u / (1 - τ * u) - -u| ≤ ρ / 100 * |u| := by
  have hu' := abs_le.mp hu
  have htu : |τ * u| ≤ ρ / 200 := by
    rw [abs_mul, abs_of_nonneg hτ0]; nlinarith [abs_nonneg u]
  have htu' := abs_le.mp htu
  have hd : 0 < 1 - τ * u := by linarith
  refine ⟨hd, ?_, ?_⟩
  · rw [abs_div, abs_neg, abs_of_pos hd, div_le_iff₀ hd]
    have : 0 ≤ |u| := abs_nonneg u
    have hk : 1 ≤ (1 + ρ / 100) * (1 - τ * u) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hk this]
  · have hd' : 1 - τ * u ≠ 0 := hd.ne'
    have e : -u / (1 - τ * u) - -u = -(τ * u) * u / (1 - τ * u) := by
      rw [eq_div_iff hd', sub_mul, div_mul_cancel₀ _ hd']; ring
    rw [e, abs_div, abs_of_pos hd, div_le_iff₀ hd, abs_mul, abs_neg]
    have : 0 ≤ |u| := abs_nonneg u
    have : |τ * u| ≤ ρ / 100 * (1 - τ * u) := by
      rcases abs_cases (τ * u) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> nlinarith
    nlinarith

lemma num_final (ρ a ε : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (ha : a * (1 + ρ) = ρ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ ρ ^ 2 / 100) :
    11 / 10 * (2 * a * ε) + (1 + 93 * ρ / 1000) *
      ((1 - a) * ((1 + 21 * ρ / 1000) ^ 2 * (1 + ρ / 100) + ρ / 100) + 2 * ε) ≤ 1 - ρ / 4 := by
  have hp : 0 < 1 + ρ := by linarith
  have ha' : a = ρ / (1 + ρ) := by field_simp; linarith
  have h1a : 1 - a = 1 / (1 + ρ) := by rw [ha']; field_simp; ring
  rw [h1a, ha']
  rw [← sub_nonneg]
  have key : 0 ≤ (1 - ρ / 4) * (1 + ρ) - (11 / 10 * (2 * ρ * ε) + (1 + 93 * ρ / 1000) *
      (((1 + 21 * ρ / 1000) ^ 2 * (1 + ρ / 100) + ρ / 100) + 2 * ε * (1 + ρ))) := by
    have hε' : ε * (1 + ρ) ≤ ρ ^ 2 / 100 * 2 := by nlinarith
    have hρ2 : ρ ^ 2 ≤ ρ := by nlinarith
    have hρ3 : ρ ^ 3 ≤ ρ ^ 2 := by nlinarith
    have hρ4 : ρ ^ 4 ≤ ρ ^ 3 := by nlinarith
    nlinarith [mul_nonneg hρ0.le hε0, mul_nonneg (mul_nonneg hρ0.le hρ0.le) hε0]
  have e : (1 - ρ / 4) - (11 / 10 * (2 * (ρ / (1 + ρ)) * ε) + (1 + 93 * ρ / 1000) *
      (1 / (1 + ρ) * ((1 + 21 * ρ / 1000) ^ 2 * (1 + ρ / 100) + ρ / 100) + 2 * ε)) =
      ((1 - ρ / 4) * (1 + ρ) - (11 / 10 * (2 * ρ * ε) + (1 + 93 * ρ / 1000) *
      (((1 + 21 * ρ / 1000) ^ 2 * (1 + ρ / 100) + ρ / 100) + 2 * ε * (1 + ρ)))) / (1 + ρ) := by
    field_simp
  rw [e]; positivity

lemma num_boot (ρ a ε δ cr : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hcr : cr * ρ = 1)
    (_ha0 : 0 ≤ cr * a) (ha1 : cr * a ≤ 1) (hε0 : 0 ≤ ε) (hε : ε ≤ ρ ^ 2 / 100)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ ρ ^ 2 / 100) :
    cr * (2 * ((1 + ρ / 100) * (a * ε)) + cr * ((1 + 21 * ρ / 1000) * ((1 + ρ / 100) * a) * δ))
      < 4 * ρ / 100 := by
  have hcr0 : 0 < cr := by nlinarith
  have h1 : cr * δ ≤ ρ / 100 := by
    have : cr * δ ≤ cr * (ρ ^ 2 / 100) := mul_le_mul_of_nonneg_left hδ hcr0.le
    nlinarith
  have h2 : ε ≤ ρ / 100 := by nlinarith
  have e : cr * (2 * ((1 + ρ / 100) * (a * ε)) + cr * ((1 + 21 * ρ / 1000) * ((1 + ρ / 100) * a) * δ))
      = (1 + ρ / 100) * (cr * a) * (2 * ε + (1 + 21 * ρ / 1000) * (cr * δ)) := by ring
  rw [e]
  have h3 : 2 * ε + (1 + 21 * ρ / 1000) * (cr * δ) ≤ 2 * (ρ / 100) + (1 + 21 * ρ / 1000) * (ρ / 100) := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 1 + 21 * ρ / 1000)
    linarith
  have h4 : 0 ≤ 2 * ε + (1 + 21 * ρ / 1000) * (cr * δ) := by
    have : 0 ≤ cr * δ := mul_nonneg hcr0.le hδ0
    positivity
  calc (1 + ρ / 100) * (cr * a) * (2 * ε + (1 + 21 * ρ / 1000) * (cr * δ))
      ≤ (1 + ρ / 100) * 1 * (2 * (ρ / 100) + (1 + 21 * ρ / 1000) * (ρ / 100)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left ha1 (by positivity)) h3 h4 (by positivity)
    _ < 4 * ρ / 100 := by nlinarith

set_option maxHeartbeats 1000000 in
theorem cw_main {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hA : A.rank = n)
    (g : (Fin m → ℝ) → (Fin m → ℝ)) (c₁ cγ cr : ℝ) (hg : IsWeightFunction A g c₁ cγ cr)
    (t : ℝ) (xOld : Fin n → ℝ) (hx : xOld ∈ interiorS0 A b)
    (hδ : centrality A b c t xOld (g (slack A b xOld)) ≤ 1 / (100 * cγ * cr ^ 2))
    (xNew : Fin n → ℝ)
    (hxN : xNew = xOld - (1 / (1 + cr)) • newtonStep A b c t xOld (g (slack A b xOld))) :
    xNew ∈ interiorS0 A b ∧
      centrality A b c t xNew (g (slack A b xNew)) ≤
        (1 - 1 / (4 * cr)) * centrality A b c t xOld (g (slack A b xOld)) := by
  have hr := hg.one_le_cr
  have hcγ := hg.one_le_cγ
  have hr0 : 0 < cr := by linarith
  have hs0 : ∀ i, 0 < slack A b xOld i := hx
  obtain ⟨s, hsd⟩ : ∃ s, slack A b xOld = s := ⟨_, rfl⟩
  have hs : ∀ i, 0 < s i := by rw [← hsd]; exact hs0
  obtain ⟨w, hwd⟩ : ∃ w, g s = w := ⟨_, rfl⟩
  have hw : ∀ i, 0 < w i := by rw [← hwd]; exact hg.pos s hs
  have hwn : ∀ i, 0 ≤ w i := fun i => (hw i).le
  obtain ⟨h, hhd⟩ : ∃ h, newtonStep A b c t xOld w = h := ⟨_, rfl⟩
  obtain ⟨δ, hδd⟩ : ∃ δ, centrality A b c t xOld w = δ := ⟨_, rfl⟩
  rw [hsd, hwd] at hδ hxN
  rw [hsd, hwd, hδd]
  rw [hδd] at hδ
  rw [hhd] at hxN
  obtain ⟨η, hηd⟩ : ∃ η : Fin m → ℝ, η = fun i => (A *ᵥ h) i / s i := ⟨_, rfl⟩
  have hηi : ∀ i, η i * s i = (A *ᵥ h) i := by
    intro i; rw [hηd]; field_simp [(hs i).ne']
  have hδη : δ = diagNorm w η := by rw [← hδd, cen_dn, hhd, hsd, hηd]
  have hδ0 : 0 ≤ δ := by rw [hδη]; exact dn_nonneg _ _
  have hδsq : δ ^ 2 = ∑ i, w i * η i ^ 2 := by rw [hδη]; exact dn_sq _ _ hwn
  obtain ⟨γ, hγd⟩ : ∃ γ, slackSensitivity A s w = γ := ⟨_, rfl⟩
  have hγ0 : 0 ≤ γ := by rw [← hγd]; exact Real.iSup_nonneg fun i => Real.sqrt_nonneg _
  have hγc : γ ≤ cγ := by rw [← hγd, ← hwd]; exact hg.slackSensitivity_le s hs
  have hmat : matNorm (weightedGram A s w) h = δ := by
    rw [← hδd, centrality, hhd, hsd]
  have hηb : ∀ i, |η i| ≤ γ * δ := by
    intro i; rw [hηd, ← hγd, ← hmat]; exact pf_gamma A hA s w hs hw h i
  obtain ⟨ρ, hρd⟩ : ∃ ρ, 1 / cr = ρ := ⟨_, rfl⟩
  have hcrρ : cr * ρ = 1 := by rw [← hρd]; field_simp
  have hρ0 : 0 < ρ := by rw [← hρd]; positivity
  have hρ1 : ρ ≤ 1 := by rw [← hρd, div_le_one hr0]; exact hr
  have hρ2 : ρ ^ 2 ≤ ρ := by nlinarith only [hρ0, hρ1]
  have hbound : 1 / (100 * cγ * cr ^ 2) ≤ ρ ^ 2 / 100 := by
    have e : ρ ^ 2 / 100 = 1 / (100 * cr ^ 2) := by rw [← hρd]; field_simp
    rw [e]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith only [hcγ, sq_nonneg cr]
  have hδ1 : δ ≤ ρ ^ 2 / 100 := hδ.trans hbound
  have hε : γ * δ ≤ ρ ^ 2 / 100 := by
    have h1 : γ * δ ≤ cγ * δ := mul_le_mul_of_nonneg_right hγc hδ0
    have h2 : cγ * δ ≤ cγ * (1 / (100 * cγ * cr ^ 2)) :=
      mul_le_mul_of_nonneg_left hδ (by linarith)
    have h3 : cγ * (1 / (100 * cγ * cr ^ 2)) = ρ ^ 2 / 100 := by
      rw [← hρd]; field_simp
    linarith
  obtain ⟨ε, hεd⟩ : ∃ ε, γ * δ = ε := ⟨_, rfl⟩
  rw [hεd] at hε hηb
  have hε0 : 0 ≤ ε := by rw [← hεd]; positivity
  have hερ : ε ≤ ρ / 100 := by linarith
  obtain ⟨a, had⟩ : ∃ a : ℝ, 1 / (1 + cr) = a := ⟨_, rfl⟩
  rw [had] at hxN
  have ha0 : 0 < a := by rw [← had]; positivity
  have hacr : a * (1 + cr) = 1 := by rw [← had]; field_simp
  have haρ : a * (1 + ρ) = ρ := by
    have : a * (1 + ρ) * cr = ρ * cr := by linear_combination hacr + (a - 1) * hcrρ
    exact mul_right_cancel₀ hr0.ne' this
  have hcra : cr * a = 1 - a := by linarith
  have ha1 : a ≤ 1 / 2 := by nlinarith only [hacr, hr, ha0]
  have hua : ∀ i, |a * η i| ≤ ρ / 200 := by
    intro i
    rw [abs_mul, abs_of_pos ha0]
    have := mul_le_mul ha1 ((hηb i).trans hε) (abs_nonneg _) (by norm_num)
    linarith only [this, hρ2]
  -- new slack
  have hsN : ∀ i, slack A b xNew i = s i * (1 - a * η i) := by
    intro i
    have h1 : slack A b xNew i = slack A b xOld i - a * (A *ᵥ h) i := by
      simp only [slack, Pi.sub_apply]
      rw [hxN, mulVec_sub, mulVec_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [h1, hsd, ← hηi i]; ring
  have hIcc0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hIcc1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hsNpos : ∀ i, 0 < slack A b xNew i := by
    intro i; rw [hsN]
    exact mul_pos (hs i) (by simpa using (alg_y (a * η i) 1 ρ zero_le_one le_rfl hρ0 hρ1 (hua i)).1)
  refine ⟨hsNpos, ?_⟩
  -- path
  obtain ⟨d, hdd⟩ : ∃ d : Fin m → ℝ, d = fun j => -(a * (s j * η j)) := ⟨_, rfl⟩
  have hpt : ∀ (τ : ℝ) j, (s + τ • d) j = s j * (1 - τ * (a * η j)) := by
    intro τ j; rw [hdd]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hp1 : s + (1:ℝ) • d = slack A b xNew := by
    ext j; rw [hpt, hsN]; ring
  have hp0 : s + (0:ℝ) • d = s := by simp
  have hppos : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ j, 0 < (s + τ • d) j := by
    intro τ hτ j; rw [hpt]
    exact mul_pos (hs j) (alg_y (a * η j) τ ρ hτ.1 hτ.2 hρ0 hρ1 (hua j)).1
  have hgpos : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ j, 0 < g (s + τ • d) j := fun τ hτ =>
    hg.pos _ (hppos τ hτ)
  have hyf : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ j,
      d j / (s + τ • d) j = -(a * η j) / (1 - τ * (a * η j)) := by
    intro τ hτ j
    have h1 := (alg_y (a * η j) τ ρ hτ.1 hτ.2 hρ0 hρ1 (hua j)).1
    rw [hpt, hdd, div_eq_div_iff (mul_pos (hs j) h1).ne' h1.ne']; ring
  have hy0 : ∀ j, d j / (s + (0:ℝ) • d) j = -(a * η j) := by
    intro j; rw [hyf 0 hIcc0]; simp
  have hyb : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ j,
      |d j / (s + τ • d) j| ≤ (1 + ρ / 100) * (a * |η j|) := by
    intro τ hτ j
    rw [hyf τ hτ]
    have := (alg_y (a * η j) τ ρ hτ.1 hτ.2 hρ0 hρ1 (hua j)).2.1
    rwa [abs_mul, abs_of_pos ha0] at this
  have hyb2 : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ j,
      |-(a * η j) - d j / (s + τ • d) j| ≤ ρ / 100 * (a * |η j|) := by
    intro τ hτ j
    rw [hyf τ hτ, abs_sub_comm]
    have := (alg_y (a * η j) τ ρ hτ.1 hτ.2 hρ0 hρ1 (hua j)).2.2
    rwa [abs_mul, abs_of_pos ha0] at this
  -- ratio bounds from log bounds
  obtain ⟨L, hLd⟩ : ∃ L : ℝ, 1 + 21 * ρ / 1000 = L := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [← hLd]; positivity
  have hL : Real.exp (ρ / 25) ≤ L ^ 2 := by
    have := exp_le_q (ρ / 25) (by positivity) (by linarith); rw [← hLd]; nlinarith only [this, hρ0, hρ1]
  have hlog0 : ∀ j, Real.log (g (s + (0:ℝ) • d) j) = Real.log (w j) := by
    intro j; rw [hp0, hwd]
  have hrat : ∀ τ ∈ Set.Icc (0:ℝ) 1,
      (∀ j, |Real.log (g (s + τ • d) j) - Real.log (g (s + (0:ℝ) • d) j)| ≤ ρ / 25) →
      ∀ j, g (s + τ • d) j ≤ L ^ 2 * w j ∧ w j ≤ L ^ 2 * g (s + τ • d) j := by
    intro τ hτ hb j
    simp only [hlog0] at hb
    have hb' := abs_le.mp (hb j)
    have e1 : g (s + τ • d) j = w j * Real.exp (Real.log (g (s + τ • d) j) - Real.log (w j)) := by
      rw [Real.exp_sub, Real.exp_log (hgpos τ hτ j), Real.exp_log (hw j)]
      field_simp [(hw j).ne']
    have e2 : w j = g (s + τ • d) j * Real.exp (-(Real.log (g (s + τ • d) j) - Real.log (w j))) := by
      rw [Real.exp_neg, Real.exp_sub, Real.exp_log (hgpos τ hτ j), Real.exp_log (hw j)]
      field_simp [(hgpos τ hτ j).ne']
    have x1 : Real.exp (Real.log (g (s + τ • d) j) - Real.log (w j)) ≤ L ^ 2 :=
      (Real.exp_le_exp.mpr hb'.2).trans hL
    have x2 : Real.exp (-(Real.log (g (s + τ • d) j) - Real.log (w j))) ≤ L ^ 2 :=
      (Real.exp_le_exp.mpr (by linarith)).trans hL
    constructor
    · rw [e1]; have := mul_le_mul_of_nonneg_left x1 (hwn j); nlinarith only [this]
    · have := hgpos τ hτ j
      calc w j = _ := e2
        _ ≤ g (s + τ • d) j * L ^ 2 := mul_le_mul_of_nonneg_left x2 this.le
        _ = _ := by ring
  have hydn : ∀ τ ∈ Set.Icc (0:ℝ) 1, (∀ j, g (s + τ • d) j ≤ L ^ 2 * w j) →
      diagNorm (g (s + τ • d)) (fun j => d j / (s + τ • d) j) ≤ L * ((1 + ρ / 100) * a) * δ := by
    intro τ hτ hr1
    rw [hδη]
    apply dn_le _ _ _ _ _ (by positivity)
    intro j
    have h1 := hr1 j
    have h2 : (d j / (s + τ • d) j) ^ 2 ≤ ((1 + ρ / 100) * (a * |η j|)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hyb τ hτ j) 2
    have h3 : ((1 + ρ / 100) * (a * |η j|)) ^ 2 = ((1 + ρ / 100) * a) ^ 2 * η j ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]; ring
    have h4 := hgpos τ hτ j
    calc g (s + τ • d) j * (d j / (s + τ • d) j) ^ 2
        ≤ (L ^ 2 * w j) * (((1 + ρ / 100) * a) ^ 2 * η j ^ 2) := by
          rw [← h3]; exact mul_le_mul h1 h2 (sq_nonneg _) (mul_nonneg (sq_nonneg _) (hwn j))
      _ = _ := by ring
  -- bootstrap
  have hE0 := num_boot ρ a ε δ cr hρ0 hρ1 hcrρ (by rw [hcra]; linarith) (by rw [hcra]; linarith)
    hε0 hε hδ0 hδ1
  have hboot := boot (fun i τ => Real.log (g (s + τ • d) i))
    (fun i τ => jacobianTerm g (s + τ • d) (fun j => d j / (s + τ • d) j) i) (ρ / 25)
    (cr * (2 * ((1 + ρ / 100) * (a * ε)) + cr * (L * ((1 + ρ / 100) * a) * δ)))
    (by rw [← hLd]; linarith only [hE0]) (by positivity)
    (fun i τ hτ => deriv_path g s d τ (hg.differentiableAt _ (hppos τ hτ)) (hppos τ hτ)
      (hgpos τ hτ) i)
    (by
      intro τ hτ hb i
      have hr1 := fun j => (hrat τ hτ hb j).1
      have hsc := sc_inf A g c₁ cγ cr hg (s + τ • d) (hppos τ hτ) (fun j => d j / (s + τ • d) j) i
      have hyn : ‖(fun j => d j / (s + τ • d) j)‖ ≤ (1 + ρ / 100) * (a * ε) := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
        rw [Real.norm_eq_abs]
        refine (hyb τ hτ j).trans ?_
        gcongr
        exact hηb j
      have hyd := hydn τ hτ hr1
      calc _ ≤ _ := hsc
        _ ≤ _ := by gcongr)
  have hrat' : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ j,
      g (s + τ • d) j ≤ L ^ 2 * w j ∧ w j ≤ L ^ 2 * g (s + τ • d) j :=
    fun τ hτ => hrat τ hτ (hboot τ hτ)
  obtain ⟨B, hBd⟩ : ∃ B : ℝ,
      cr * (L * (L * ((1 + ρ / 100) * a) * δ)) + cr * (ρ / 100 * a * δ) = B := ⟨_, rfl⟩
  have hD := mvt_dn w hwn (fun i τ => Real.log (g (s + τ • d) i) + τ * (cr * -(a * η i)))
    (fun i τ => jacobianTerm g (s + τ • d) (fun j => d j / (s + τ • d) j) i + cr * -(a * η i))
    (fun i τ hτ => by
      have h1 := deriv_path g s d τ (hg.differentiableAt _ (hppos τ hτ)) (hppos τ hτ)
        (hgpos τ hτ) i
      have h2 := (hasDerivAt_id τ).mul_const (cr * -(a * η i))
      exact (h1.add h2).congr_deriv (by simp))
    B
    (by
      intro τ hτ
      have hr1 := fun j => (hrat' τ hτ j).1
      have hr2 := fun j => (hrat' τ hτ j).2
      have hyd := hydn τ hτ hr1
      have hyb2' : ∀ j, |-(a * η j) - (fun j => d j / (s + τ • d) j) j| ≤
          ρ / 100 * (a * |η j|) := hyb2 τ hτ
      have hop := hg.stepConsistency_op _ (hppos τ hτ) cr le_rfl (fun j => d j / (s + τ • d) j)
      have hgp := hgpos τ hτ
      generalize (fun j => d j / (s + τ • d) j) = y at hyd hop hyb2' ⊢
      generalize jacobianTerm g (s + τ • d) y = J at hop ⊢
      generalize g (s + τ • d) = G at hyd hop hr1 hr2 hgp ⊢
      have hvec : (fun i => J i + cr * -(a * η i)) =
          cr • (y + cr⁻¹ • J) + cr • (fun j => -(a * η j) - y j) := by
        ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; field_simp; ring
      rw [hvec]
      refine (dn_add w _ _ hwn).trans ?_
      rw [← hBd]
      apply add_le_add
      · have h1 : diagNorm w (cr • (y + cr⁻¹ • J)) ≤ (cr * L) * diagNorm G (y + cr⁻¹ • J) := by
          apply dn_le _ _ _ _ _ (by positivity)
          intro j
          have := hr2 j
          have h3 : 0 ≤ (y + cr⁻¹ • J) j ^ 2 := sq_nonneg _
          simp only [Pi.smul_apply, smul_eq_mul]
          have := mul_le_mul_of_nonneg_right this h3
          have := mul_le_mul_of_nonneg_left this (sq_nonneg cr); nlinarith only [this]
        calc diagNorm w (cr • (y + cr⁻¹ • J)) ≤ (cr * L) * diagNorm G (y + cr⁻¹ • J) := h1
          _ ≤ (cr * L) * diagNorm G y := mul_le_mul_of_nonneg_left hop (by positivity)
          _ ≤ (cr * L) * (L * ((1 + ρ / 100) * a) * δ) :=
              mul_le_mul_of_nonneg_left hyd (by positivity)
          _ = cr * (L * (L * ((1 + ρ / 100) * a) * δ)) := by ring
      · rw [hδη]
        calc diagNorm w (cr • (fun j => -(a * η j) - y j))
            ≤ (cr * (ρ / 100 * a)) * diagNorm w η := by
              apply dn_le _ _ _ _ _ (by positivity)
              intro j
              simp only [Pi.smul_apply, smul_eq_mul]
              have h4 : (-(a * η j) - y j) ^ 2 ≤ (ρ / 100 * (a * |η j|)) ^ 2 := by
                rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hyb2' j) 2
              have h5 : (ρ / 100 * (a * |η j|)) ^ 2 = (ρ / 100 * a) ^ 2 * η j ^ 2 := by
                rw [mul_pow, mul_pow, sq_abs]; ring
              rw [h5] at h4
              have := mul_le_mul_of_nonneg_left h4 (mul_nonneg (hwn j) (sq_nonneg cr))
              nlinarith only [this]
          _ = cr * (ρ / 100 * a * diagNorm w η) := by ring)
  -- new weights
  obtain ⟨W2, hW2⟩ : ∃ W2, g (slack A b xNew) = W2 := ⟨_, rfl⟩
  rw [hW2]
  have hW2pos : ∀ j, 0 < W2 j := by rw [← hW2]; exact hg.pos _ hsNpos
  have hb1 : ∀ j, |Real.log (W2 j) - Real.log (w j)| ≤ ρ / 25 := by
    intro j; have := hboot 1 hIcc1 j; rwa [hp1, hW2, hlog0] at this
  have hD' : diagNorm w (fun i => Real.log (W2 i) - Real.log (w i) - (1 - a) * η i) ≤ B := by
    have e : (fun i => Real.log (W2 i) - Real.log (w i) - (1 - a) * η i) =
        (fun i => (Real.log (g (s + (1:ℝ) • d) i) + 1 * (cr * -(a * η i))) -
          (Real.log (g (s + (0:ℝ) • d) i) + 0 * (cr * -(a * η i)))) := by
      ext i; rw [hp1, hW2, hlog0, ← hcra]; ring
    rw [e]; exact hD
  have hua2 : ∀ i, |(1 - a) * η i| ≤ ε := by
    intro i; rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 1 - a)]
    calc (1 - a) * |η i| ≤ 1 * |η i| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ ε := by rw [one_mul]; exact hηb i
  have hW1pos : ∀ i, 0 < 1 + (1 - a) * η i := by
    intro i; have := abs_le.mp (hua2 i); linarith
  obtain ⟨W1, hW1⟩ : ∃ W1 : Fin m → ℝ, W1 = fun i => w i * (1 + (1 - a) * η i) := ⟨_, rfl⟩
  have hW1p : ∀ i, 0 < W1 i := by intro i; rw [hW1]; exact mul_pos (hw i) (hW1pos i)
  obtain ⟨z, hz⟩ : ∃ z : Fin m → ℝ, z = fun i => Real.log (W2 i) - Real.log (W1 i) := ⟨_, rfl⟩
  have hlb := fun i => log_bd ((1 - a) * η i) (by have := hua2 i; linarith)
  have hzdec : z = (fun i => Real.log (W2 i) - Real.log (w i) - (1 - a) * η i) +
      (fun i => (1 - a) * η i - Real.log (1 + (1 - a) * η i)) := by
    ext i; rw [hz, hW1]; simp only [Pi.add_apply]
    rw [Real.log_mul (hw i).ne' (hW1pos i).ne']; ring
  have hEdn : diagNorm w (fun i => (1 - a) * η i - Real.log (1 + (1 - a) * η i)) ≤ 2 * ε * δ := by
    rw [hδη]
    apply dn_le _ _ _ _ _ (by positivity)
    intro i
    have h1 := (hlb i).2
    have h2 : ((1 - a) * η i) ^ 2 ≤ ε * |η i| := by
      rw [← sq_abs, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 1 - a)]
      have k1 : (1 - a) * |η i| ≤ |η i| := by
        have := mul_le_mul_of_nonneg_right (by linarith : 1 - a ≤ 1) (abs_nonneg (η i))
        linarith
      have k0 : 0 ≤ (1 - a) * |η i| := mul_nonneg (by linarith) (abs_nonneg _)
      calc ((1 - a) * |η i|) ^ 2 ≤ |η i| ^ 2 := pow_le_pow_left₀ k0 k1 2
        _ = |η i| * |η i| := sq _
        _ ≤ ε * |η i| := mul_le_mul_of_nonneg_right (hηb i) (abs_nonneg _)
    have h3 : ((1 - a) * η i - Real.log (1 + (1 - a) * η i)) ^ 2 ≤ (2 * ε) ^ 2 * η i ^ 2 := by
      rw [← sq_abs, ← sq_abs (η i)]
      have := abs_nonneg ((1 - a) * η i - Real.log (1 + (1 - a) * η i))
      have h4 : |(1 - a) * η i - Real.log (1 + (1 - a) * η i)| ≤ 2 * ε * |η i| := by linarith
      calc _ ≤ (2 * ε * |η i|) ^ 2 := pow_le_pow_left₀ this h4 2
        _ = _ := by ring
    have := mul_le_mul_of_nonneg_left h3 (hwn i)
    linarith
  have hzdn : diagNorm w z ≤ B + 2 * ε * δ := by
    rw [hzdec]; exact (dn_add w _ _ hwn).trans (add_le_add hD' hEdn)
  have hzabs : ∀ i, |z i| ≤ 3 * ρ / 50 := by
    intro i
    have e : z i = (Real.log (W2 i) - Real.log (w i)) - Real.log (1 + (1 - a) * η i) := by
      rw [hz, hW1]; simp only
      rw [Real.log_mul (hw i).ne' (hW1pos i).ne']; ring
    rw [e]
    have h1 := abs_le.mp (hb1 i)
    have h2 := abs_le.mp ((hlb i).1)
    have h3 := hua2 i
    rw [abs_le]; constructor <;> linarith
  have hW1e : ∀ i, W1 i = W2 i * Real.exp (-z i) := by
    intro i
    rw [hz]; simp only
    rw [neg_sub, Real.exp_sub, Real.exp_log (hW1p i), Real.exp_log (hW2pos i)]
    field_simp [(hW2pos i).ne']
  have hW2e : ∀ i, W2 i = w i * Real.exp (Real.log (W2 i) - Real.log (w i)) := by
    intro i
    rw [Real.exp_sub, Real.exp_log (hW2pos i), Real.exp_log (hw i)]
    field_simp [(hw i).ne']
  have hK : ∀ i, W1 i ≤ (11 / 10) ^ 2 * W2 i := by
    intro i
    rw [hW1e]
    have h1 : Real.exp (-z i) ≤ Real.exp (3 * ρ / 50) :=
      Real.exp_le_exp.mpr (by have := abs_le.mp (hzabs i); linarith)
    have h2 := exp_le_q (3 * ρ / 50) (by positivity) (by linarith)
    have h4 : (3 * ρ / 50) ^ 2 ≤ 9 / 2500 := by nlinarith only [hρ0, hρ1]
    have h3 : Real.exp (-z i) ≤ (11 / 10) ^ 2 := by linarith
    have := mul_le_mul_of_nonneg_left h3 (hW2pos i).le
    linarith
  have hQ : diagNorm W2 (fun i => (W2 i - W1 i) / W2 i) ≤ (1 + 93 * ρ / 1000) * diagNorm w z := by
    apply dn_le _ _ _ _ _ (by positivity)
    intro i
    have e : (W2 i - W1 i) / W2 i = 1 - Real.exp (-z i) := by
      rw [hW1e]; field_simp [(hW2pos i).ne']
    rw [e]
    have h1 := one_sub_exp_neg_sq (z i)
    have h2 : W2 i ≤ w i * Real.exp (ρ / 25) := by
      rw [hW2e i]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (abs_le.mp (hb1 i)).2) (hwn i)
    have h3 : Real.exp (ρ / 25) * Real.exp (2 * |z i|) ≤ (1 + 93 * ρ / 1000) ^ 2 := by
      rw [← Real.exp_add]
      have h4 : Real.exp (ρ / 25 + 2 * |z i|) ≤ Real.exp (4 * ρ / 25) :=
        Real.exp_le_exp.mpr (by have := hzabs i; linarith)
      have h5 := exp_le_q (4 * ρ / 25) (by positivity) (by linarith)
      nlinarith only [h4, h5, hρ0, hρ1]
    have h6 : 0 ≤ (1 - Real.exp (-z i)) ^ 2 := sq_nonneg _
    have h7 := hW2pos i
    calc W2 i * (1 - Real.exp (-z i)) ^ 2 ≤ W2 i * (z i ^ 2 * Real.exp (2 * |z i|)) :=
          mul_le_mul_of_nonneg_left h1 h7.le
      _ ≤ (w i * Real.exp (ρ / 25)) * (z i ^ 2 * Real.exp (2 * |z i|)) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (w i * z i ^ 2) * (Real.exp (ρ / 25) * Real.exp (2 * |z i|)) := by ring
      _ ≤ (w i * z i ^ 2) * (1 + 93 * ρ / 1000) ^ 2 :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg (hwn i) (sq_nonneg _))
      _ = _ := by ring
  have hwc := wc A hA b c t xNew hsNpos W1 W2 hW1p hW2pos (11 / 10) (by norm_num) hK
  -- split step
  have hδs : centrality A b c t xOld w ≤ 1 / (8 * slackSensitivity A (slack A b xOld) w) := by
    rw [hδd, hsd, hγd]
    rcases hγ0.lt_or_eq with hγp | hγz
    · rw [le_div_iff₀ (by positivity)]
      have : γ * δ ≤ 1 / 100 := by rw [hεd]; linarith
      nlinarith only [this]
    · have hη0 : ∀ i, η i = 0 := by
        intro i; have := hηb i; rw [← hεd, ← hγz, zero_mul] at this
        exact abs_nonpos_iff.mp this
      have : δ = 0 := by
        rw [hδη]; unfold diagNorm; simp [hη0]
      rw [this]; rw [← hγz]; simp
  have hsns := (sns_main A b c hA t cr hr0.le xOld w ⟨hx, hw⟩ hδs h hhd.symm xNew
    (by rw [had]; exact hxN) W1 (by
      ext i
      rw [hW1, ← mulVec_mulVec, ← mulVec_mulVec, Pi.add_apply, Pi.smul_apply, mulVec_diagonal,
        mulVec_diagonal, smul_eq_mul, hsd, ← hηi i]
      have : cr / (1 + cr) = 1 - a := by rw [← had]; field_simp; ring
      rw [this]; field_simp [(hs i).ne'])).2
  rw [hsd, hγd, hδd] at hsns
  have hfin := num_final ρ a ε hρ0 hρ1 haρ hε0 hε
  rw [hLd] at hfin
  have eB : B = (1 - a) * δ * (L ^ 2 * (1 + ρ / 100) + ρ / 100) := by
    rw [← hBd, ← hcra]; ring
  have e2 : 2 / (1 + cr) * γ * δ ^ 2 = 2 * a * ε * δ := by
    rw [← hεd, ← had]; ring
  calc centrality A b c t xNew W2
      ≤ 11 / 10 * centrality A b c t xNew W1 + diagNorm W2 (fun i => (W2 i - W1 i) / W2 i) := hwc
    _ ≤ 11 / 10 * (2 / (1 + cr) * γ * δ ^ 2) + (1 + 93 * ρ / 1000) * (B + 2 * ε * δ) := by
        gcongr
        exact hQ.trans (mul_le_mul_of_nonneg_left hzdn (by positivity))
    _ = (11 / 10 * (2 * a * ε) + (1 + 93 * ρ / 1000) *
          ((1 - a) * (L ^ 2 * (1 + ρ / 100) + ρ / 100) + 2 * ε)) * δ := by
        rw [e2, eB]; ring
    _ ≤ (1 - ρ / 4) * δ := mul_le_mul_of_nonneg_right hfin hδ0
    _ = (1 - 1 / (4 * cr)) * δ := by rw [← hρd]; ring

theorem centering_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hA : A.rank = n)
    (g : (Fin m → ℝ) → (Fin m → ℝ)) (c₁ cγ cr : ℝ) (hg : IsWeightFunction A g c₁ cγ cr)
    (t : ℝ) (xOld : Fin n → ℝ) (hx : xOld ∈ interiorS0 A b)
    (hδ : centrality A b c t xOld (g (slack A b xOld)) ≤ 1 / (100 * cγ * cr ^ 2)) :
    let xNew := xOld - (1 / (1 + cr)) • newtonStep A b c t xOld (g (slack A b xOld))
    xNew ∈ interiorS0 A b ∧
      centrality A b c t xNew (g (slack A b xNew)) ≤
        (1 - 1 / (4 * cr)) * centrality A b c t xOld (g (slack A b xOld)) := by
  intro xNew
  exact cw_main A b c hA g c₁ cγ cr hg t xOld hx hδ xNew rfl

end PathFindingLP.Centering

open PathFindingLP.Centering


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hA : A.rank = n)
    (g : (Fin m → ℝ) → (Fin m → ℝ)) (c₁ cγ cr : ℝ) (hg : IsWeightFunction A g c₁ cγ cr)
    (t : ℝ) (xOld : Fin n → ℝ) (hx : xOld ∈ interiorS0 A b)
    (hδ : centrality A b c t xOld (g (slack A b xOld)) ≤ 1 / (100 * cγ * cr ^ 2)) :
    let xNew := xOld - (1 / (1 + cr)) • newtonStep A b c t xOld (g (slack A b xOld))
    xNew ∈ interiorS0 A b ∧
      centrality A b c t xNew (g (slack A b xNew)) ≤
        (1 - 1 / (4 * cr)) * centrality A b c t xOld (g (slack A b xOld)) := by
  exact centering_core A b c hA g c₁ cγ cr hg t xOld hx hδ
