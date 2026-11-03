-- Prove2me | solution 1 for OptInapprox.MaxCut.soundness_8_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:25:57.26424+00:00
-- url     : https://prove2.me/submissions/4de2289a-9b38-4d61-8a91-4852174ef463

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_MIS
import Definitions.Def_OptInapprox_MaxCut_Verifier
import Theorems.Thm_OptInapprox_MaxCut_proposition_7_1
import Theorems.Thm_OptInapprox_MaxCut_proposition_7_2
import Theorems.Thm_OptInapprox_MaxCut_cand_card_le
import Theorems.Thm_OptInapprox_MaxCut_eq_6
import Theorems.Thm_OptInapprox_MaxCut_eq_7

open OptInapprox.MaxCut

noncomputable section

namespace Soundness83

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

private lemma prop_7_5_aux (hMIS : MajorityIsStablest) (ρ : ℝ) (hρ₀ : -1 < ρ) (hρ₁ : ρ ≤ 0)
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

private lemma lowDegInf_mono {n : ℕ} {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (i : Fin n)
    (f : (Fin n → Bool) → ℝ) :
    lowDegInf k₁ i f ≤ lowDegInf k₂ i f := by
  unfold lowDegInf
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun S _ _ => sq_nonneg _)
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
  exact ⟨hS.1, hS.2.trans hk⟩

private lemma lowDegInf_le_one {n : ℕ} (k : ℕ) (i : Fin n) (f : (Fin n → Bool) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    lowDegInf k i f ≤ 1 := by
  unfold lowDegInf
  calc ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S ∧ S.card ≤ k),
        OptInapprox.MaxCut.fourier f S ^ 2
      ≤ ∑ S : Finset (Fin n), OptInapprox.MaxCut.fourier f S ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
    _ ≤ 1 := sum_fourier_sq_le_one f hf

private lemma neg_one_le_pow {ρ : ℝ} (hρ₁ : -1 ≤ ρ) (hρ₂ : ρ ≤ 1) (m : ℕ) :
    -1 ≤ ρ ^ m := by
  have habs : |ρ| ≤ 1 := abs_le.mpr ⟨hρ₁, hρ₂⟩
  have hpow : |ρ ^ m| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg ρ) habs
  exact (abs_le.mp hpow).1

private lemma neg_one_le_noiseStab {n : ℕ} {ρ : ℝ} (hρ₁ : -1 ≤ ρ) (hρ₂ : ρ ≤ 1)
    (f : (Fin n → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    -1 ≤ noiseStab ρ f := by
  rw [(proposition_7_1 f ρ hρ₁ hρ₂).2]
  have hle : ∑ S : Finset (Fin n), (-1 : ℝ) * OptInapprox.MaxCut.fourier f S ^ 2 ≤
      ∑ S : Finset (Fin n), ρ ^ S.card * OptInapprox.MaxCut.fourier f S ^ 2 := by
    refine Finset.sum_le_sum (fun S _ => ?_)
    exact mul_le_mul_of_nonneg_right (neg_one_le_pow hρ₁ hρ₂ S.card) (sq_nonneg _)
  rw [← Finset.mul_sum] at hle
  have hsum := sum_fourier_sq_le_one f hf
  linarith

private lemma abs_pm (b : Bool) : |pm b| = 1 := by
  cases b <;> norm_num [pm]

private lemma abs_pm_le_one (b : Bool) : |pm b| ≤ 1 := by
  rw [abs_pm]

private lemma abs_gv_le_one (L : ULC) (F : Fin L.nW → (Fin L.M → Bool) → Bool)
    (v : Fin L.nV) (hd : 0 < (L.nbrs v).card) (z : Fin L.M → Bool) :
    |gv L F v z| ≤ 1 := by
  unfold gv
  rw [abs_mul, abs_inv, Nat.abs_cast]
  have hle : |∑ w ∈ L.nbrs v, pm (F w (compose z (L.σ v w)))| ≤ ((L.nbrs v).card : ℝ) := by
    calc |∑ w ∈ L.nbrs v, pm (F w (compose z (L.σ v w)))|
        ≤ ∑ w ∈ L.nbrs v, |pm (F w (compose z (L.σ v w)))| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ _w ∈ L.nbrs v, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun w _ => abs_pm _)
      _ = ((L.nbrs v).card : ℝ) := by simp
  have hpos : (0 : ℝ) < ((L.nbrs v).card : ℝ) := Nat.cast_pos.mpr hd
  have hmul := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (le_of_lt hpos))
  rwa [inv_mul_cancel₀ (ne_of_gt hpos)] at hmul

private lemma sum_le_filter_card_add_mul {α : Type*} [DecidableEq α] (s : Finset α)
    (g : α → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (hg : ∀ x ∈ s, g x ≤ 1) :
    ∑ x ∈ s, g x ≤ ((s.filter (fun x => τ < g x)).card : ℝ) + (s.card : ℝ) * τ := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun x => τ < g x)]
  have h1 : ∑ x ∈ s.filter (fun x => τ < g x), g x ≤
      ((s.filter (fun x => τ < g x)).card : ℝ) := by
    calc ∑ x ∈ s.filter (fun x => τ < g x), g x
        ≤ ∑ _x ∈ s.filter (fun x => τ < g x), (1 : ℝ) := by
          refine Finset.sum_le_sum (fun x hx => hg x (Finset.mem_filter.mp hx).1)
      _ = ((s.filter (fun x => τ < g x)).card : ℝ) := by simp
  have h2 : ∑ x ∈ s.filter (fun x => ¬ τ < g x), g x ≤ (s.card : ℝ) * τ := by
    calc ∑ x ∈ s.filter (fun x => ¬ τ < g x), g x
        ≤ ∑ _x ∈ s.filter (fun x => ¬ τ < g x), τ := by
          refine Finset.sum_le_sum (fun x hx => not_lt.mp (Finset.mem_filter.mp hx).2)
      _ = ((s.filter (fun x => ¬ τ < g x)).card : ℝ) * τ := by simp [nsmul_eq_mul]
      _ ≤ (s.card : ℝ) * τ := by
          refine mul_le_mul_of_nonneg_right ?_ hτ
          exact_mod_cast Finset.card_filter_le s _
  linarith

private lemma sum_le_filter_le_card_add_mul {α : Type*} [DecidableEq α] (s : Finset α)
    (g : α → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (hg : ∀ x ∈ s, g x ≤ 1) :
    ∑ x ∈ s, g x ≤ ((s.filter (fun x => τ ≤ g x)).card : ℝ) + (s.card : ℝ) * τ := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun x => τ ≤ g x)]
  have h1 : ∑ x ∈ s.filter (fun x => τ ≤ g x), g x ≤
      ((s.filter (fun x => τ ≤ g x)).card : ℝ) := by
    calc ∑ x ∈ s.filter (fun x => τ ≤ g x), g x
        ≤ ∑ _x ∈ s.filter (fun x => τ ≤ g x), (1 : ℝ) := by
          refine Finset.sum_le_sum (fun x hx => hg x (Finset.mem_filter.mp hx).1)
      _ = ((s.filter (fun x => τ ≤ g x)).card : ℝ) := by simp
  have h2 : ∑ x ∈ s.filter (fun x => ¬ τ ≤ g x), g x ≤ (s.card : ℝ) * τ := by
    calc ∑ x ∈ s.filter (fun x => ¬ τ ≤ g x), g x
        ≤ ∑ _x ∈ s.filter (fun x => ¬ τ ≤ g x), τ := by
          refine Finset.sum_le_sum (fun x hx => le_of_lt (not_le.mp (Finset.mem_filter.mp hx).2))
      _ = ((s.filter (fun x => ¬ τ ≤ g x)).card : ℝ) * τ := by simp [nsmul_eq_mul]
      _ ≤ (s.card : ℝ) * τ := by
          refine mul_le_mul_of_nonneg_right ?_ hτ
          exact_mod_cast Finset.card_filter_le s _
  linarith

private lemma exists_card_mul_ge_sum {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    ∃ x ∈ s, ∑ y ∈ s, f y ≤ (s.card : ℝ) * f x := by
  by_contra! h
  have hlt : ∑ y ∈ s, f y < ∑ _y ∈ s, ((s.card : ℝ)⁻¹ * ∑ z ∈ s, f z) := by
    refine Finset.sum_lt_sum_of_nonempty hs (fun x hx => ?_)
    have hcard : (0 : ℝ) < (s.card : ℝ) := Nat.cast_pos.mpr hs.card_pos
    rw [lt_inv_mul_iff₀ hcard]
    exact h x hx
  have hcard0 : (s.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hs.card_pos)
  simp only [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hcard0, one_mul,
    lt_self_iff_false] at hlt

private lemma sum_cand_indicator (L : ULC) (V_good : Finset (Fin L.nV))
    (Cand : Fin L.nW → Finset (Fin L.M)) (N_good : Fin L.nV → Finset (Fin L.nW))
    (labV : Fin L.nV → Fin L.M)
    (hN_cand : ∀ v w, w ∈ N_good v → (L.σ v w).symm (labV v) ∈ Cand w) (w : Fin L.nW) :
    ∑ i ∈ Cand w, ∑ v ∈ V_good,
        (if w ∈ N_good v ∧ L.σ v w i = labV v then (1 : ℝ) else 0) =
      ∑ v ∈ V_good, (if w ∈ N_good v then (1 : ℝ) else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  by_cases hw : w ∈ N_good v
  · have hmem : (L.σ v w).symm (labV v) ∈ Cand w := hN_cand v w hw
    have hrew : ∀ i ∈ Cand w,
        (if w ∈ N_good v ∧ L.σ v w i = labV v then (1 : ℝ) else 0) =
          if i = (L.σ v w).symm (labV v) then (1 : ℝ) else 0 := by
      intro i _
      have heq : (L.σ v w i = labV v) ↔ (i = (L.σ v w).symm (labV v)) :=
        ⟨fun h => (Equiv.eq_symm_apply (L.σ v w)).mpr h,
         fun h => (Equiv.eq_symm_apply (L.σ v w)).mp h⟩
      simp only [hw, true_and, heq]
    rw [Finset.sum_congr rfl hrew, Finset.sum_ite_eq', if_pos hmem, if_pos hw]
  · simp [hw]

private lemma exists_w_label (L : ULC) (j₀ : Fin L.M) (V_good : Finset (Fin L.nV))
    (Cand : Fin L.nW → Finset (Fin L.M)) (N_good : Fin L.nV → Finset (Fin L.nW))
    (labV : Fin L.nV → Fin L.M) (B : ℝ) (hB : 0 ≤ B)
    (hCand_le : ∀ w, ((Cand w).card : ℝ) ≤ B)
    (hN_cand : ∀ v w, w ∈ N_good v → (L.σ v w).symm (labV v) ∈ Cand w) (w : Fin L.nW) :
    ∃ i : Fin L.M,
      ∑ v ∈ V_good, (if w ∈ N_good v then (1 : ℝ) else 0) ≤
        B * ∑ v ∈ V_good, (if w ∈ N_good v ∧ L.σ v w i = labV v then (1 : ℝ) else 0) := by
  let g : Fin L.M → ℝ := fun i =>
    ∑ v ∈ V_good, (if w ∈ N_good v ∧ L.σ v w i = labV v then (1 : ℝ) else 0)
  have hg_nonneg : ∀ i, 0 ≤ g i := fun i =>
    Finset.sum_nonneg (fun v _ => by split_ifs <;> norm_num)
  have hsum := sum_cand_indicator L V_good Cand N_good labV hN_cand w
  change ∑ i ∈ Cand w, g i = ∑ v ∈ V_good, (if w ∈ N_good v then (1 : ℝ) else 0) at hsum
  by_cases hne : (Cand w).Nonempty
  · obtain ⟨i, _, hi⟩ := exists_card_mul_ge_sum (Cand w) hne g
    refine ⟨i, ?_⟩
    calc ∑ v ∈ V_good, (if w ∈ N_good v then (1 : ℝ) else 0)
        = ∑ y ∈ Cand w, g y := hsum.symm
      _ ≤ ((Cand w).card : ℝ) * g i := hi
      _ ≤ B * g i := mul_le_mul_of_nonneg_right (hCand_le w) (hg_nonneg i)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨j₀, ?_⟩
    have h0 : ∑ v ∈ V_good, (if w ∈ N_good v then (1 : ℝ) else 0) = 0 := by
      rw [← hsum, hne, Finset.sum_empty]
    rw [h0]
    exact mul_nonneg hB (hg_nonneg j₀)

private lemma card_E_filter_eq_sum (L : ULC) (P : Fin L.nV × Fin L.nW → Prop) [DecidablePred P] :
    ((L.E.filter P).card : ℝ) =
      ∑ w : Fin L.nW, ∑ v : Fin L.nV, if (v, w) ∈ L.E ∧ P (v, w) then (1 : ℝ) else 0 := by
  have h1 : ((L.E.filter P).card : ℝ) =
      ∑ e : Fin L.nV × Fin L.nW, if e ∈ L.E ∧ P e then (1 : ℝ) else 0 := by
    have h2 : L.E.filter P = Finset.univ.filter (fun e => e ∈ L.E ∧ P e) := by
      ext e; simp
    rw [h2, Finset.card_filter]
    push_cast
    rfl
  rw [h1, Fintype.sum_prod_type, Finset.sum_comm]

private lemma card_E_eq_sum_nbrs (L : ULC) :
    (L.E.card : ℝ) = ∑ v : Fin L.nV, ((L.nbrs v).card : ℝ) := by
  have h1 : (L.E.card : ℝ) =
      ∑ e : Fin L.nV × Fin L.nW, if e ∈ L.E then (1 : ℝ) else 0 := by
    have h2 : L.E = Finset.univ.filter (fun e => e ∈ L.E) := by ext e; simp
    conv_lhs => rw [h2]
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [h1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  unfold ULC.nbrs
  rw [Finset.card_filter]
  push_cast
  rfl

private lemma gamma_algebra (ε δ k_real cardE : ℝ) (hδ : δ ≠ 0) (hk : k_real ≠ 0) :
    (2 * k_real / δ)⁻¹ * (cardE * (ε * δ / 4)) = (ε * δ ^ 2 / (8 * k_real)) * cardE := by
  field_simp [hδ, hk]
  ring

private def candSet (L : ULC) (F : Fin L.nW → (Fin L.M → Bool) → Bool) (k : ℕ) (δ : ℝ)
    (w : Fin L.nW) : Finset (Fin L.M) :=
  Finset.univ.filter (fun i : Fin L.M => δ / 2 ≤ lowDegInf k i (fun x => pm (F w x)))

private def nGoodSet (L : ULC) (F : Fin L.nW → (Fin L.M → Bool) → Bool) (k : ℕ) (δ : ℝ)
    (labV : Fin L.nV → Fin L.M) (v : Fin L.nV) : Finset (Fin L.nW) :=
  (L.nbrs v).filter (fun w => (L.σ v w).symm (labV v) ∈ candSet L F k δ w)

end Soundness83

open Soundness83

theorem solution (hMIS : MajorityIsStablest) (ρ : ℝ) (hρ₁ : -1 < ρ) (hρ₂ : ρ < 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ γ' : ℝ, 0 < γ' ∧ ∀ L : ULC, L.IsVRegular → ∀ F : Fin L.nW → (Fin L.M → Bool) → Bool,
      Real.arccos ρ / Real.pi + ε ≤ accProb L ρ F → γ' ≤ L.OPT := by
  obtain ⟨δ, hδ_pos, k₀, hk₀⟩ := prop_7_5_aux hMIS ρ hρ₁ (le_of_lt hρ₂) ε hε
  let k : ℕ := max k₀ 1
  have hk₀_le : k₀ ≤ k := le_max_left k₀ 1
  have hk_pos : (0 : ℝ) < (k : ℝ) := by
    have : (0 : ℕ) < k := lt_of_lt_of_le Nat.zero_lt_one (le_max_right k₀ 1)
    exact Nat.cast_pos.mpr this
  refine ⟨ε * δ ^ 2 / (8 * (k : ℝ)), by positivity, fun L hreg F hacc => ?_⟩
  obtain ⟨hnV, d, hd, hcard⟩ := hreg
  have hnV_pos : (0 : ℝ) < (L.nV : ℝ) := Nat.cast_pos.mpr hnV
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hgv_le : ∀ v : Fin L.nV, ∀ z : Fin L.M → Bool, |gv L F v z| ≤ 1 := by
    intro v z
    exact abs_gv_le_one L F v (by rw [hcard v]; exact hd) z
  let a : Fin L.nV → ℝ := fun v => 1 / 2 - 1 / 2 * noiseStab ρ (gv L F v)
  have ha_le_one : ∀ v : Fin L.nV, a v ≤ 1 := by
    intro v
    have hns := neg_one_le_noiseStab (ρ := ρ) (by linarith) (by linarith) (gv L F v) (hgv_le v)
    dsimp [a]
    linarith
  let τ : ℝ := Real.arccos ρ / Real.pi + ε / 2
  have hτ_nonneg : 0 ≤ τ := by
    have harc : 0 ≤ Real.arccos ρ := Real.arccos_nonneg ρ
    have hpi : 0 < Real.pi := Real.pi_pos
    have hdiv : 0 ≤ Real.arccos ρ / Real.pi := div_nonneg harc (le_of_lt hpi)
    dsimp [τ]
    linarith
  let V_good : Finset (Fin L.nV) := Finset.univ.filter (fun v : Fin L.nV => τ < a v)
  have hacc_eq : accProb L ρ F = (L.nV : ℝ)⁻¹ * ∑ v : Fin L.nV, a v := by
    rw [eq_6 L ⟨hnV, d, hd, hcard⟩ ρ hρ₁ hρ₂ F]
    dsimp [a]
    simp_rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    have hnV0 : (L.nV : ℝ) ≠ 0 := ne_of_gt hnV_pos
    field_simp [hnV0]
  have hsum_a_ge : (L.nV : ℝ) * (τ + ε / 2) ≤ ∑ v : Fin L.nV, a v := by
    have h1 : τ + ε / 2 ≤ (L.nV : ℝ)⁻¹ * ∑ v : Fin L.nV, a v := by
      have : τ + ε / 2 = Real.arccos ρ / Real.pi + ε := by dsimp [τ]; ring
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hnV_pos)
    rwa [mul_inv_cancel_left₀ (ne_of_gt hnV_pos)] at h2
  have hsum_a_le : ∑ v : Fin L.nV, a v ≤ (V_good.card : ℝ) + (L.nV : ℝ) * τ := by
    have h := sum_le_filter_card_add_mul Finset.univ a τ hτ_nonneg (fun v _ => ha_le_one v)
    simpa [V_good, Finset.card_univ, Fintype.card_fin] using h
  have hV_good_card : (L.nV : ℝ) * (ε / 2) ≤ (V_good.card : ℝ) := by linarith
  have hex_j : ∀ v ∈ V_good, ∃ j : Fin L.M, δ < lowDegInf k j (gv L F v) := by
    intro v hv
    have hlt : τ < a v := (Finset.mem_filter.mp hv).2
    have hns_lt : noiseStab ρ (gv L F v) < 1 - 2 / Real.pi * Real.arccos ρ - ε := by
      dsimp [τ, a] at hlt
      have heq : 2 * (Real.arccos ρ / Real.pi) = 2 / Real.pi * Real.arccos ρ := by ring
      linarith
    by_contra! hle
    have hle₀ : ∀ j : Fin L.M, lowDegInf k₀ j (gv L F v) ≤ δ :=
      fun j => (lowDegInf_mono hk₀_le j (gv L F v)).trans (hle j)
    have hge := hk₀ L.M (gv L F v) (hgv_le v) hle₀
    linarith
  have hV_good_pos : 0 < (V_good.card : ℝ) := by
    have : 0 < (L.nV : ℝ) * (ε / 2) := by positivity
    linarith
  have hV_good_ne : V_good.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hV_good_pos)
  obtain ⟨v₀, hv₀⟩ := hV_good_ne
  obtain ⟨j₀, _⟩ := hex_j v₀ hv₀
  have hex_labV : ∀ v : Fin L.nV, ∃ j : Fin L.M, v ∈ V_good → δ < lowDegInf k j (gv L F v) := by
    intro v
    by_cases hv : v ∈ V_good
    · obtain ⟨j, hj⟩ := hex_j v hv
      exact ⟨j, fun _ => hj⟩
    · exact ⟨j₀, fun h => False.elim (hv h)⟩
  obtain ⟨labV, hlabV⟩ := Classical.skolem.mp hex_labV
  have hCand_le : ∀ w : Fin L.nW, ((candSet L F k δ w).card : ℝ) ≤ 2 * (k : ℝ) / δ :=
    fun w => (cand_card_le (fun x => pm (F w x)) (fun _ => abs_pm_le_one _) k δ hδ_pos).2
  have hN_cand : ∀ v w, w ∈ nGoodSet L F k δ labV v →
      (L.σ v w).symm (labV v) ∈ candSet L F k δ w :=
    fun v w hw => (Finset.mem_filter.mp hw).2
  have hN_good_card : ∀ v ∈ V_good, (d : ℝ) * (δ / 2) ≤ ((nGoodSet L F k δ labV v).card : ℝ) := by
    intro v hv
    have h7 := (eq_7 L F v).2 k (labV v)
    have hcard_v : ((L.nbrs v).card : ℝ) = (d : ℝ) := by exact_mod_cast hcard v
    have hgt : δ ≤ (d : ℝ)⁻¹ * ∑ w ∈ L.nbrs v,
        lowDegInf k ((L.σ v w).symm (labV v)) (fun x => pm (F w x)) := by
      have h1 := le_of_lt (hlabV v hv)
      rw [hcard_v] at h7
      exact h1.trans h7
    have hsum_ge : (d : ℝ) * δ ≤ ∑ w ∈ L.nbrs v,
        lowDegInf k ((L.σ v w).symm (labV v)) (fun x => pm (F w x)) := by
      have hmul := mul_le_mul_of_nonneg_left hgt (le_of_lt hd_pos)
      rwa [mul_inv_cancel_left₀ (ne_of_gt hd_pos)] at hmul
    have hsum_le := sum_le_filter_le_card_add_mul (L.nbrs v)
      (fun w => lowDegInf k ((L.σ v w).symm (labV v)) (fun x => pm (F w x))) (δ / 2) (by linarith)
      (fun w _ => lowDegInf_le_one k _ (fun x => pm (F w x)) (fun _ => abs_pm_le_one _))
    have hfilter_eq : (L.nbrs v).filter
        (fun w => δ / 2 ≤ lowDegInf k ((L.σ v w).symm (labV v)) (fun x => pm (F w x))) =
        nGoodSet L F k δ labV v := by
      ext w
      simp [nGoodSet, candSet]
    rw [hfilter_eq, hcard_v] at hsum_le
    linarith
  have hB_pos : 0 < 2 * (k : ℝ) / δ := by positivity
  have hex_w : ∀ w : Fin L.nW, ∃ i : Fin L.M,
      ∑ v ∈ V_good, (if w ∈ nGoodSet L F k δ labV v then (1 : ℝ) else 0) ≤
        (2 * (k : ℝ) / δ) * ∑ v ∈ V_good,
          (if w ∈ nGoodSet L F k δ labV v ∧ L.σ v w i = labV v then (1 : ℝ) else 0) :=
    fun w => exists_w_label L j₀ V_good (candSet L F k δ) (nGoodSet L F k δ labV) labV
      (2 * (k : ℝ) / δ) (le_of_lt hB_pos) hCand_le hN_cand w
  obtain ⟨labW, hlabW⟩ := Classical.skolem.mp hex_w
  have hsum_w := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin L.nW))) (fun w _ => hlabW w)
  rw [← Finset.mul_sum] at hsum_w
  have hLHS : ∑ w : Fin L.nW, ∑ v ∈ V_good, (if w ∈ nGoodSet L F k δ labV v then (1 : ℝ) else 0) =
      ∑ v ∈ V_good, ((nGoodSet L F k δ labV v).card : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    simp
  have hLHS_ge : ((L.nV : ℝ) * (ε / 2)) * ((d : ℝ) * (δ / 2)) ≤
      ∑ v ∈ V_good, ((nGoodSet L F k δ labV v).card : ℝ) := by
    calc ((L.nV : ℝ) * (ε / 2)) * ((d : ℝ) * (δ / 2))
        ≤ (V_good.card : ℝ) * ((d : ℝ) * (δ / 2)) :=
          mul_le_mul_of_nonneg_right hV_good_card (by positivity)
      _ = ∑ _v ∈ V_good, ((d : ℝ) * (δ / 2)) := by simp [nsmul_eq_mul]
      _ ≤ ∑ v ∈ V_good, ((nGoodSet L F k δ labV v).card : ℝ) := Finset.sum_le_sum hN_good_card
  have hRHS_le : ∑ w : Fin L.nW, ∑ v ∈ V_good,
        (if w ∈ nGoodSet L F k δ labV v ∧ L.σ v w (labW w) = labV v then (1 : ℝ) else 0) ≤
      ((L.E.filter fun e => L.σ e.1 e.2 (labW e.2) = labV e.1).card : ℝ) := by
    rw [card_E_filter_eq_sum]
    refine Finset.sum_le_sum (fun w _ => ?_)
    have hsub : ∑ v ∈ V_good,
          (if w ∈ nGoodSet L F k δ labV v ∧ L.σ v w (labW w) = labV v then (1 : ℝ) else 0) ≤
        ∑ v : Fin L.nV,
          (if w ∈ nGoodSet L F k δ labV v ∧ L.σ v w (labW w) = labV v then (1 : ℝ) else 0) :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => by split_ifs <;> norm_num)
    refine hsub.trans (Finset.sum_le_sum (fun v _ => ?_))
    by_cases h : w ∈ nGoodSet L F k δ labV v ∧ L.σ v w (labW w) = labV v
    · have hw_nbr : w ∈ L.nbrs v := (Finset.mem_filter.mp h.1).1
      have he : (v, w) ∈ L.E := (Finset.mem_filter.mp hw_nbr).2
      rw [if_pos h, if_pos ⟨he, h.2⟩]
    · rw [if_neg h]
      split_ifs <;> norm_num
  have hE_card : (L.E.card : ℝ) = (L.nV : ℝ) * (d : ℝ) := by
    rw [card_E_eq_sum_nbrs]
    have h1 : ∀ v : Fin L.nV, ((L.nbrs v).card : ℝ) = (d : ℝ) := fun v => by exact_mod_cast hcard v
    simp [h1, Finset.card_univ, Fintype.card_fin]
  have hE_pos : 0 < (L.E.card : ℝ) := by
    rw [hE_card]
    positivity
  have hchain : (L.E.card : ℝ) * (ε * δ / 4) ≤
      (2 * (k : ℝ) / δ) * ((L.E.filter fun e => L.σ e.1 e.2 (labW e.2) = labV e.1).card : ℝ) := by
    calc (L.E.card : ℝ) * (ε * δ / 4)
        = ((L.nV : ℝ) * (ε / 2)) * ((d : ℝ) * (δ / 2)) := by rw [hE_card]; ring
      _ ≤ ∑ v ∈ V_good, ((nGoodSet L F k δ labV v).card : ℝ) := hLHS_ge
      _ = ∑ w : Fin L.nW, ∑ v ∈ V_good,
            (if w ∈ nGoodSet L F k δ labV v then (1 : ℝ) else 0) := hLHS.symm
      _ ≤ (2 * (k : ℝ) / δ) * ∑ w : Fin L.nW, ∑ v ∈ V_good,
            (if w ∈ nGoodSet L F k δ labV v ∧ L.σ v w (labW w) = labV v then (1 : ℝ) else 0) :=
          hsum_w
      _ ≤ (2 * (k : ℝ) / δ) *
            ((L.E.filter fun e => L.σ e.1 e.2 (labW e.2) = labV e.1).card : ℝ) :=
          mul_le_mul_of_nonneg_left hRHS_le (le_of_lt hB_pos)
  have hsat : ε * δ ^ 2 / (8 * (k : ℝ)) ≤ L.satFrac (labV, labW) := by
    unfold ULC.satFrac
    rw [le_div_iff₀ hE_pos]
    have hmul := mul_le_mul_of_nonneg_left hchain (le_of_lt (inv_pos.mpr hB_pos))
    rw [inv_mul_cancel_left₀ (ne_of_gt hB_pos)] at hmul
    have heq := gamma_algebra ε δ (k : ℝ) (L.E.card : ℝ) (ne_of_gt hδ_pos) (ne_of_gt hk_pos)
    linarith
  have hopt : L.satFrac (labV, labW) ≤ L.OPT := by
    unfold ULC.OPT
    haveI : Nonempty (Fin L.M) := ⟨j₀⟩
    exact le_ciSup (Set.Finite.bddAbove (Set.toFinite _)) (labV, labW)
  exact hsat.trans hopt
