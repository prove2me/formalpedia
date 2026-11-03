-- Prove2me | solution 1 for OptInapprox.MaxCut.proposition_7_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:25:51.490201+00:00
-- url     : https://prove2.me/submissions/444cc082-83ae-4cd2-91a9-69275a232992

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_MIS
import Theorems.Thm_OptInapprox_MaxCut_proposition_7_1
import Theorems.Thm_OptInapprox_MaxCut_proposition_7_2

open OptInapprox.MaxCut

noncomputable section

private lemma chi_eq_prod_ite {n : ℕ} (S : Finset (Fin n)) (y : Fin n → Bool) :
    chi S y = ∏ i : Fin n, (if i ∈ S then pm (y i) else 1) := by
  unfold chi
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp

private lemma sum_corrKernel_chi {n : ℕ} (η : ℝ) (x : Fin n → Bool) (S : Finset (Fin n)) :
    ∑ y : Fin n → Bool, corrKernel η x y * chi S y = η ^ S.card * chi S x := by
  have hterm : ∀ y : Fin n → Bool,
      corrKernel η x y * chi S y =
      ∏ i : Fin n, ((1 + η * pm (x i) * pm (y i)) / 2 * (if i ∈ S then pm (y i) else 1)) := by
    intro y
    unfold corrKernel
    rw [chi_eq_prod_ite S y, ← Finset.prod_mul_distrib]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    (1 + η * pm (x i) * pm b) / 2 * (if i ∈ S then pm b else 1))]
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (∑ b : Bool, (1 + η * pm (x i) * pm b) / 2 * (if i ∈ S then pm b else 1)) =
      if i ∈ S then η * pm (x i) else 1 := by
    intro i _
    rw [Fintype.sum_bool]
    have ht : pm true = -1 := rfl
    have hf : pm false = 1 := rfl
    by_cases hi : i ∈ S
    · simp only [hi, ite_true, ht, hf]
      cases x i <;> { simp [pm]; ring }
    · simp only [hi, ite_false, ht, hf]
      ring
  rw [Finset.prod_congr rfl h1, ← Finset.prod_filter]
  have hfilter : Finset.univ.filter (fun i : Fin n => i ∈ S) = S := by
    ext i; simp
  rw [hfilter, Finset.prod_mul_distrib, Finset.prod_const]
  rfl

private lemma sum_corrKernel {n : ℕ} (η : ℝ) (x : Fin n → Bool) :
    ∑ y : Fin n → Bool, corrKernel η x y = 1 := by
  have h := sum_corrKernel_chi η x ∅
  have hchi : ∀ y : Fin n → Bool, chi ∅ y = 1 := fun _ => rfl
  simp_rw [hchi, mul_one, Finset.card_empty, pow_zero] at h
  exact h

private lemma corrKernel_nonneg {n : ℕ} {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (x y : Fin n → Bool) : 0 ≤ corrKernel η x y := by
  unfold corrKernel
  refine Finset.prod_nonneg (fun i _ => ?_)
  cases x i <;> cases y i <;> { simp [pm]; linarith }

private lemma abs_bonamiBeckner_le_one {n : ℕ} {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (f : (Fin n → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1) (x : Fin n → Bool) :
    |bonamiBeckner η f x| ≤ 1 := by
  calc |bonamiBeckner η f x|
      = |∑ y, corrKernel η x y * f y| := rfl
    _ ≤ ∑ y, |corrKernel η x y * f y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, corrKernel η x y * |f y| := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [abs_mul, abs_of_nonneg (corrKernel_nonneg hη0 hη1 x y)]
    _ ≤ ∑ y, corrKernel η x y * 1 := by
        refine Finset.sum_le_sum (fun y _ =>
          mul_le_mul_of_nonneg_left (hf y) (corrKernel_nonneg hη0 hη1 x y))
    _ = 1 := by simp [sum_corrKernel]

private lemma corrKernel_symm {n : ℕ} (η : ℝ) (x y : Fin n → Bool) :
    corrKernel η x y = corrKernel η y x := by
  unfold corrKernel
  refine Finset.prod_congr rfl (fun i _ => by ring)

private lemma fourier_bonamiBeckner {n : ℕ} (η : ℝ) (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) :
    OptInapprox.MaxCut.fourier (bonamiBeckner η f) S =
      η ^ S.card * OptInapprox.MaxCut.fourier f S := by
  unfold OptInapprox.MaxCut.fourier cubeE bonamiBeckner
  have hswap : ∑ x : Fin n → Bool, (∑ y : Fin n → Bool, corrKernel η x y * f y) * chi S x =
      ∑ y : Fin n → Bool, f y * (∑ x : Fin n → Bool, corrKernel η y x * chi S x) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [corrKernel_symm η x y]
    ring
  rw [hswap]
  simp_rw [sum_corrKernel_chi]
  have hpull : ∑ y : Fin n → Bool, f y * (η ^ S.card * chi S y) =
      η ^ S.card * ∑ y : Fin n → Bool, f y * chi S y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => by ring)
  rw [hpull]
  ring

private lemma cubeE_bonamiBeckner {n : ℕ} (η : ℝ) (f : (Fin n → Bool) → ℝ) :
    cubeE (bonamiBeckner η f) = cubeE f := by
  have h1 : OptInapprox.MaxCut.fourier (bonamiBeckner η f) ∅ = cubeE (bonamiBeckner η f) := by
    unfold OptInapprox.MaxCut.fourier chi; simp
  have h2 : OptInapprox.MaxCut.fourier f ∅ = cubeE f := by
    unfold OptInapprox.MaxCut.fourier chi; simp
  have h3 := fourier_bonamiBeckner η f ∅
  simp only [Finset.card_empty, pow_zero, one_mul] at h3
  linarith

private lemma sum_fourier_sq_le_one {n : ℕ} (f : (Fin n → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    ∑ S : Finset (Fin n), OptInapprox.MaxCut.fourier f S ^ 2 ≤ 1 := by
  have h71 := proposition_7_1 f 1 (by norm_num) (by norm_num)
  have hsum : ∑ S : Finset (Fin n), OptInapprox.MaxCut.fourier f S ^ 2 =
      cubeE (fun x => f x * bonamiBeckner 1 f x) := by
    calc ∑ S : Finset (Fin n), OptInapprox.MaxCut.fourier f S ^ 2
        = ∑ S : Finset (Fin n), (1 : ℝ) ^ S.card * OptInapprox.MaxCut.fourier f S ^ 2 := by simp
      _ = noiseStab 1 f := h71.2.symm
      _ = cubeE (fun x => f x * bonamiBeckner 1 f x) := h71.1
  rw [hsum]
  unfold cubeE
  have hle : ∑ x : Fin n → Bool, f x * bonamiBeckner 1 f x ≤ ∑ _x : Fin n → Bool, (1 : ℝ) := by
    refine Finset.sum_le_sum (fun x _ => ?_)
    have hb := abs_bonamiBeckner_le_one (η := 1) zero_le_one (le_refl 1) f hf x
    calc f x * bonamiBeckner 1 f x
        ≤ |f x * bonamiBeckner 1 f x| := le_abs_self _
      _ = |f x| * |bonamiBeckner 1 f x| := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (hf x) hb (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hsum1 : ∑ _x : Fin n → Bool, (1 : ℝ) = (2 : ℝ) ^ n := by
    simp [Finset.card_univ, Fintype.card_fin]
  have hmul := mul_le_mul_of_nonneg_left (hle.trans_eq hsum1) (by positivity : (0 : ℝ) ≤ (2 ^ n : ℝ)⁻¹)
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  rwa [inv_mul_cancel₀ h2n] at hmul

private lemma lowDegInf_eq_sum_filter {n : ℕ} (k' : ℕ) (i : Fin n) (f : (Fin n → Bool) → ℝ) :
    lowDegInf k' i f =
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S),
        if S.card ≤ k' then OptInapprox.MaxCut.fourier f S ^ 2 else 0 := by
  unfold lowDegInf
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  by_cases hi : i ∈ S <;> by_cases hk : S.card ≤ k' <;> simp [hi, hk]

private lemma influence_bonamiBeckner_le {n : ℕ} {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (f : (Fin n → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1) (k' : ℕ) (i : Fin n) :
    influence i (bonamiBeckner η f) ≤ lowDegInf k' i f + (η ^ 2) ^ k' := by
  rw [proposition_7_2 (bonamiBeckner η f) i, lowDegInf_eq_sum_filter k' i f]
  have hη2_0 : 0 ≤ η ^ 2 := sq_nonneg η
  have hη2_1 : η ^ 2 ≤ 1 := by nlinarith
  have hterm : ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S),
      OptInapprox.MaxCut.fourier (bonamiBeckner η f) S ^ 2 ≤
      (if S.card ≤ k' then OptInapprox.MaxCut.fourier f S ^ 2 else 0) +
        (η ^ 2) ^ k' * OptInapprox.MaxCut.fourier f S ^ 2 := by
    intro S _
    rw [fourier_bonamiBeckner, mul_pow, ← pow_mul, mul_comm S.card 2, pow_mul]
    have hcoeff : (η ^ 2) ^ S.card ≤ (if S.card ≤ k' then (1 : ℝ) else 0) + (η ^ 2) ^ k' := by
      by_cases hk : S.card ≤ k'
      · rw [if_pos hk]
        have hle1 : (η ^ 2) ^ S.card ≤ 1 := pow_le_one₀ hη2_0 hη2_1
        have hpos : 0 ≤ (η ^ 2) ^ k' := pow_nonneg hη2_0 k'
        linarith
      · rw [if_neg hk]
        have hle : (η ^ 2) ^ S.card ≤ (η ^ 2) ^ k' :=
          pow_le_pow_of_le_one hη2_0 hη2_1 (by omega)
        linarith
    calc (η ^ 2) ^ S.card * OptInapprox.MaxCut.fourier f S ^ 2
        ≤ ((if S.card ≤ k' then (1 : ℝ) else 0) + (η ^ 2) ^ k') *
            OptInapprox.MaxCut.fourier f S ^ 2 :=
          mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
      _ = (if S.card ≤ k' then OptInapprox.MaxCut.fourier f S ^ 2 else 0) +
            (η ^ 2) ^ k' * OptInapprox.MaxCut.fourier f S ^ 2 := by
          split_ifs <;> ring
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hsub : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S),
        OptInapprox.MaxCut.fourier f S ^ 2 ≤
      ∑ S : Finset (Fin n), OptInapprox.MaxCut.fourier f S ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
  have htot : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S),
      OptInapprox.MaxCut.fourier f S ^ 2 ≤ 1 := hsub.trans (sum_fourier_sq_le_one f hf)
  have hmul : (η ^ 2) ^ k' * ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S),
      OptInapprox.MaxCut.fourier f S ^ 2 ≤ (η ^ 2) ^ k' * 1 :=
    mul_le_mul_of_nonneg_left htot (pow_nonneg hη2_0 k')
  linarith

private lemma noiseStab_le_bonamiBeckner_add {n : ℕ} {ρ η : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (f : (Fin n → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1) (M : ℕ) :
    noiseStab ρ f ≤ noiseStab ρ (bonamiBeckner η f) + (1 - (η ^ 2) ^ M) + ρ ^ M := by
  rw [(proposition_7_1 f ρ (by linarith) hρ1).2,
      (proposition_7_1 (bonamiBeckner η f) ρ (by linarith) hρ1).2]
  have hη2_0 : 0 ≤ η ^ 2 := sq_nonneg η
  have hη2_1 : η ^ 2 ≤ 1 := by nlinarith
  have hterm : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
      ρ ^ S.card * OptInapprox.MaxCut.fourier f S ^ 2 ≤
      ρ ^ S.card * OptInapprox.MaxCut.fourier (bonamiBeckner η f) S ^ 2 +
        ((1 - (η ^ 2) ^ M) + ρ ^ M) * OptInapprox.MaxCut.fourier f S ^ 2 := by
    intro S _
    rw [fourier_bonamiBeckner, mul_pow, ← pow_mul, mul_comm S.card 2, pow_mul]
    have hcoeff : ρ ^ S.card ≤ ρ ^ S.card * (η ^ 2) ^ S.card + ((1 - (η ^ 2) ^ M) + ρ ^ M) := by
      by_cases hM : S.card ≤ M
      · have h1 : (η ^ 2) ^ M ≤ (η ^ 2) ^ S.card := pow_le_pow_of_le_one hη2_0 hη2_1 hM
        have h2 : ρ ^ S.card ≤ 1 := pow_le_one₀ hρ0 hρ1
        have h3 : 0 ≤ 1 - (η ^ 2) ^ S.card := sub_nonneg.mpr (pow_le_one₀ hη2_0 hη2_1)
        have h4 : ρ ^ S.card * (1 - (η ^ 2) ^ S.card) ≤ 1 * (1 - (η ^ 2) ^ M) := by
          calc ρ ^ S.card * (1 - (η ^ 2) ^ S.card)
              ≤ 1 * (1 - (η ^ 2) ^ S.card) := mul_le_mul_of_nonneg_right h2 h3
            _ ≤ 1 * (1 - (η ^ 2) ^ M) := by linarith
        have h5 : 0 ≤ ρ ^ M := pow_nonneg hρ0 M
        linarith
      · have h1 : ρ ^ S.card ≤ ρ ^ M := pow_le_pow_of_le_one hρ0 hρ1 (by omega)
        have h2 : 0 ≤ ρ ^ S.card * (η ^ 2) ^ S.card := mul_nonneg (pow_nonneg hρ0 _) (pow_nonneg hη2_0 _)
        have h3 : 0 ≤ 1 - (η ^ 2) ^ M := sub_nonneg.mpr (pow_le_one₀ hη2_0 hη2_1)
        linarith
    calc ρ ^ S.card * OptInapprox.MaxCut.fourier f S ^ 2
        ≤ (ρ ^ S.card * (η ^ 2) ^ S.card + ((1 - (η ^ 2) ^ M) + ρ ^ M)) *
            OptInapprox.MaxCut.fourier f S ^ 2 :=
          mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
      _ = ρ ^ S.card * ((η ^ 2) ^ S.card * OptInapprox.MaxCut.fourier f S ^ 2) +
            ((1 - (η ^ 2) ^ M) + ρ ^ M) * OptInapprox.MaxCut.fourier f S ^ 2 := by ring
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hnonneg : 0 ≤ (1 - (η ^ 2) ^ M) + ρ ^ M := by
    have h1 : 0 ≤ 1 - (η ^ 2) ^ M := sub_nonneg.mpr (pow_le_one₀ hη2_0 hη2_1)
    have h2 : 0 ≤ ρ ^ M := pow_nonneg hρ0 M
    linarith
  have hmul := mul_le_mul_of_nonneg_left (sum_fourier_sq_le_one f hf) hnonneg
  linarith

private lemma one_add_mul_pow_le_one {r : ℝ} (hr0 : 0 ≤ r) (_hr1 : r ≤ 1) (k : ℕ) :
    (1 + (k : ℝ) * (1 - r)) * r ^ k ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    push_cast
    have hstep : (1 + ((k : ℝ) + 1) * (1 - r)) * r ≤ 1 + (k : ℝ) * (1 - r) := by
      have hdiff : (1 + (k : ℝ) * (1 - r)) - (1 + ((k : ℝ) + 1) * (1 - r)) * r =
          ((k : ℝ) + 1) * (1 - r) ^ 2 := by ring
      have hpos : 0 ≤ ((k : ℝ) + 1) * (1 - r) ^ 2 := by positivity
      linarith
    calc (1 + ((k : ℝ) + 1) * (1 - r)) * r ^ (k + 1)
        = ((1 + ((k : ℝ) + 1) * (1 - r)) * r) * r ^ k := by rw [pow_succ]; ring
      _ ≤ (1 + (k : ℝ) * (1 - r)) * r ^ k :=
          mul_le_mul_of_nonneg_right hstep (pow_nonneg hr0 k)
      _ ≤ 1 := ih

private lemma exists_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {c : ℝ} (hc : 0 < c) :
    ∃ k : ℕ, r ^ k ≤ c := by
  let k := ⌈1 / (c * (1 - r))⌉₊
  refine ⟨k, ?_⟩
  have h1 := one_add_mul_pow_le_one hr0 (le_of_lt hr1) k
  have hsub : 0 < 1 - r := by linarith
  have hceil : 1 / (c * (1 - r)) ≤ (k : ℝ) := Nat.le_ceil _
  have hmul : 1 / c ≤ (k : ℝ) * (1 - r) := by
    have h2 := mul_le_mul_of_nonneg_right hceil (le_of_lt hsub)
    have h3 : 1 / (c * (1 - r)) * (1 - r) = 1 / c := by
      have : 1 - r ≠ 0 := ne_of_gt hsub
      field_simp [this, ne_of_gt hc]
    linarith
  have h4 : (1 / c) * r ^ k ≤ 1 := by
    calc (1 / c) * r ^ k
        ≤ (1 + (k : ℝ) * (1 - r)) * r ^ k :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hr0 k)
      _ ≤ 1 := h1
  have h5 := mul_le_mul_of_nonneg_left h4 (le_of_lt hc)
  have h6 : c * (1 / c * r ^ k) = r ^ k := by
    field_simp [ne_of_gt hc]
  linarith

private lemma one_sub_pow_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (m : ℕ) :
    1 - a ^ m ≤ (m : ℝ) * (1 - a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast
    have h1 : 1 - a ^ (m + 1) = (1 - a ^ m) * a + (1 - a) := by rw [pow_succ]; ring
    have hsub : 0 ≤ 1 - a := by linarith
    have h2 : (1 - a ^ m) * a ≤ ((m : ℝ) * (1 - a)) * 1 :=
      mul_le_mul ih ha1 ha0 (by positivity)
    linarith

private lemma prop_7_3_aux (hMIS : MajorityIsStablest) (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∃ k' : ℕ,
      ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ), (∀ x, |f x| ≤ 1) → cubeE f = 0 →
        (∀ i, lowDegInf k' i f ≤ δ') → noiseStab ρ f ≤ 1 - 2 / Real.pi * Real.arccos ρ + ε := by
  obtain ⟨M, hM⟩ := exists_pow_le hρ₀ hρ₁ (by linarith : 0 < ε / 4)
  let γ : ℝ := min (1 / 2) (ε / (8 * ((M : ℝ) + 1)))
  have hM1_pos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hγ_pos : 0 < γ := lt_min (by norm_num) (by positivity)
  have hγ_half : γ ≤ 1 / 2 := min_le_left _ _
  have hγ_eps : γ ≤ ε / (8 * ((M : ℝ) + 1)) := min_le_right _ _
  let η : ℝ := 1 - γ
  have hη0 : 0 ≤ η := by linarith
  have hη1 : η < 1 := by linarith
  have hη2_0 : 0 ≤ η ^ 2 := sq_nonneg η
  have hη2_1 : η ^ 2 < 1 := by nlinarith
  have h1_sub_η2M : 1 - (η ^ 2) ^ M ≤ ε / 4 := by
    have hstep1 : 1 - (η ^ 2) ^ M ≤ (M : ℝ) * (1 - η ^ 2) :=
      one_sub_pow_le hη2_0 (le_of_lt hη2_1) M
    have hstep2 : 1 - η ^ 2 ≤ 2 * γ := by
      have : 1 - η ^ 2 = (2 - γ) * γ := by ring
      nlinarith
    have hstep3 : (M : ℝ) * (1 - η ^ 2) ≤ ((M : ℝ) + 1) * (2 * γ) := by
      have hM_le : (M : ℝ) ≤ (M : ℝ) + 1 := by linarith
      calc (M : ℝ) * (1 - η ^ 2)
          ≤ (M : ℝ) * (2 * γ) := mul_le_mul_of_nonneg_left hstep2 (Nat.cast_nonneg M)
        _ ≤ ((M : ℝ) + 1) * (2 * γ) := mul_le_mul_of_nonneg_right hM_le (by linarith)
    have hstep4 : ((M : ℝ) + 1) * (2 * γ) ≤ ε / 4 := by
      have hmul := mul_le_mul_of_nonneg_left hγ_eps (by positivity : (0 : ℝ) ≤ 2 * ((M : ℝ) + 1))
      have heq : 2 * ((M : ℝ) + 1) * (ε / (8 * ((M : ℝ) + 1))) = ε / 4 := by
        field_simp [ne_of_gt hM1_pos]
        ring
      linarith
    linarith
  obtain ⟨δ, hδ_pos, hδ⟩ := hMIS ρ hρ₀ hρ₁ (ε / 2) (by linarith)
  obtain ⟨k', hk'⟩ := exists_pow_le hη2_0 hη2_1 (by linarith : 0 < δ / 2)
  refine ⟨δ / 2, by linarith, k', fun n f hf hEf hlow => ?_⟩
  have hmis_g := hδ n (bonamiBeckner η f)
    (abs_bonamiBeckner_le_one hη0 (le_of_lt hη1) f hf)
    (by rw [cubeE_bonamiBeckner, hEf])
    (fun i => by
      have hinf := influence_bonamiBeckner_le hη0 (le_of_lt hη1) f hf k' i
      have hli := hlow i
      linarith)
  have hns := noiseStab_le_bonamiBeckner_add hρ₀ (le_of_lt hρ₁) hη0 (le_of_lt hη1) f hf M
  linarith

private def negCube {n : ℕ} (x : Fin n → Bool) : Fin n → Bool := fun i => !x i

@[simp]
private lemma negCube_involutive {n : ℕ} (x : Fin n → Bool) : negCube (negCube x) = x := by
  ext i
  simp [negCube]

private def negCubeEquiv {n : ℕ} : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := negCube
  invFun := negCube
  left_inv := negCube_involutive
  right_inv := negCube_involutive

private lemma pm_not (b : Bool) : pm (!b) = -pm b := by
  cases b <;> norm_num [pm]

private lemma chi_negCube {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    chi S (negCube x) = (-1 : ℝ) ^ S.card * chi S x := by
  unfold chi negCube
  have h : ∀ i ∈ S, pm (!x i) = (-1 : ℝ) * pm (x i) := by
    intro i _
    rw [pm_not]
    ring
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_const]

private def oddPart {n : ℕ} (f : (Fin n → Bool) → ℝ) (x : Fin n → Bool) : ℝ :=
  (f x - f (negCube x)) / 2

private lemma abs_oddPart_le_one {n : ℕ} (f : (Fin n → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (x : Fin n → Bool) : |oddPart f x| ≤ 1 := by
  unfold oddPart
  rw [abs_div, Nat.abs_ofNat]
  have h1 := hf x
  have h2 := hf (negCube x)
  have h3 := abs_sub (f x) (f (negCube x))
  linarith

private lemma cubeE_oddPart {n : ℕ} (f : (Fin n → Bool) → ℝ) : cubeE (oddPart f) = 0 := by
  unfold cubeE oddPart
  have hbij : ∑ x : Fin n → Bool, f (negCube x) = ∑ x : Fin n → Bool, f x :=
    Equiv.sum_comp negCubeEquiv f
  have hsum : ∑ x : Fin n → Bool, (f x - f (negCube x)) / 2 =
      ((∑ x, f x) - (∑ x, f (negCube x))) / 2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [hsum, hbij]
  ring

private lemma fourier_negCube {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) :
    OptInapprox.MaxCut.fourier (fun x => f (negCube x)) S =
      (-1 : ℝ) ^ S.card * OptInapprox.MaxCut.fourier f S := by
  unfold OptInapprox.MaxCut.fourier cubeE
  have hbij : ∑ x : Fin n → Bool, f (negCube x) * chi S x =
      ∑ y : Fin n → Bool, f y * chi S (negCube y) := by
    have h := Equiv.sum_comp negCubeEquiv (fun x => f (negCube x) * chi S x)
    rw [← h]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    change f (negCube (negCube y)) * chi S (negCube y) = f y * chi S (negCube y)
    rw [negCube_involutive]
  rw [hbij]
  simp_rw [chi_negCube]
  have h2 : ∑ y : Fin n → Bool, f y * ((-1 : ℝ) ^ S.card * chi S y) =
      (-1 : ℝ) ^ S.card * ∑ y : Fin n → Bool, f y * chi S y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => by ring)
  rw [h2]
  ring

private lemma fourier_oddPart {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) :
    OptInapprox.MaxCut.fourier (oddPart f) S =
      ((1 - (-1 : ℝ) ^ S.card) / 2) * OptInapprox.MaxCut.fourier f S := by
  have hlin : OptInapprox.MaxCut.fourier (oddPart f) S =
      (OptInapprox.MaxCut.fourier f S -
        OptInapprox.MaxCut.fourier (fun x => f (negCube x)) S) / 2 := by
    unfold OptInapprox.MaxCut.fourier cubeE oddPart
    have hsum : ∑ x : Fin n → Bool, (f x - f (negCube x)) / 2 * chi S x =
        ((∑ x, f x * chi S x) - (∑ x, f (negCube x) * chi S x)) / 2 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl (fun x _ => by ring)
    rw [hsum]
    ring
  rw [hlin, fourier_negCube]
  ring

private lemma odd_coeff_sq_le_one (m : ℕ) : ((1 - (-1 : ℝ) ^ m) / 2) ^ 2 ≤ 1 := by
  rcases Nat.even_or_odd m with hm | hm
  · rw [hm.neg_one_pow]; norm_num
  · rw [hm.neg_one_pow]; norm_num

private lemma neg_odd_pow_le (ρ : ℝ) (m : ℕ) :
    -((-ρ) ^ m * ((1 - (-1 : ℝ) ^ m) / 2) ^ 2) ≤ ρ ^ m := by
  rcases Nat.even_or_odd m with hm | hm
  · rw [hm.neg_one_pow]
    have hpos : 0 ≤ ρ ^ m := hm.pow_nonneg ρ
    linarith
  · rw [hm.neg_one_pow, hm.neg_pow]
    linarith

private lemma fourier_oddPart_sq_le {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) :
    OptInapprox.MaxCut.fourier (oddPart f) S ^ 2 ≤ OptInapprox.MaxCut.fourier f S ^ 2 := by
  rw [fourier_oddPart, mul_pow]
  calc ((1 - (-1 : ℝ) ^ S.card) / 2) ^ 2 * OptInapprox.MaxCut.fourier f S ^ 2
      ≤ 1 * OptInapprox.MaxCut.fourier f S ^ 2 :=
        mul_le_mul_of_nonneg_right (odd_coeff_sq_le_one S.card) (sq_nonneg _)
    _ = OptInapprox.MaxCut.fourier f S ^ 2 := one_mul _

private lemma lowDegInf_oddPart_le {n : ℕ} (k : ℕ) (f : (Fin n → Bool) → ℝ) (i : Fin n) :
    lowDegInf k i (oddPart f) ≤ lowDegInf k i f := by
  unfold lowDegInf
  exact Finset.sum_le_sum (fun S _ => fourier_oddPart_sq_le f S)

private lemma neg_noiseStab_oddPart_le {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (ρ : ℝ) (hρ₀ : -1 < ρ) (hρ₁ : ρ ≤ 0) :
    -noiseStab (-ρ) (oddPart f) ≤ noiseStab ρ f := by
  rw [(proposition_7_1 (oddPart f) (-ρ) (by linarith) (by linarith)).2,
      (proposition_7_1 f ρ (by linarith) (by linarith)).2,
      ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum (fun S _ => ?_)
  rw [fourier_oddPart, mul_pow]
  have h1 : -((-ρ) ^ S.card * (((1 - (-1 : ℝ) ^ S.card) / 2) ^ 2 *
      OptInapprox.MaxCut.fourier f S ^ 2)) =
      (-((-ρ) ^ S.card * ((1 - (-1 : ℝ) ^ S.card) / 2) ^ 2)) *
        OptInapprox.MaxCut.fourier f S ^ 2 := by ring
  rw [h1]
  exact mul_le_mul_of_nonneg_right (neg_odd_pow_le ρ S.card) (sq_nonneg _)

end

theorem solution (hMIS : MajorityIsStablest) (ρ : ℝ) (hρ₀ : -1 < ρ) (hρ₁ : ρ ≤ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ k : ℕ,
      ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ), (∀ x, |f x| ≤ 1) →
        (∀ i, lowDegInf k i f ≤ δ) → 1 - 2 / Real.pi * Real.arccos ρ - ε ≤ noiseStab ρ f := by
  obtain ⟨δ, hδ_pos, k, hk⟩ := prop_7_3_aux hMIS (-ρ) (by linarith) (by linarith) ε hε
  refine ⟨δ, hδ_pos, k, fun n f hf hlow => ?_⟩
  have h73_g := hk n (oddPart f) (abs_oddPart_le_one f hf) (cubeE_oddPart f)
    (fun i => (lowDegInf_oddPart_le k f i).trans (hlow i))
  have hns := neg_noiseStab_oddPart_le f ρ hρ₀ hρ₁
  have harc : 1 - 2 / Real.pi * Real.arccos (-ρ) = -(1 - 2 / Real.pi * Real.arccos ρ) := by
    rw [Real.arccos_neg]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp [hpi]
    ring
  linarith
