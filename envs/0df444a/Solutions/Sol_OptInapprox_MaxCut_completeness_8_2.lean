-- Prove2me | solution 1 for OptInapprox.MaxCut.completeness_8_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T00:28:09.725248+00:00
-- url     : https://prove2.me/submissions/d9244bf3-0b00-4a6c-a206-565567bf6950

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Verifier

open OptInapprox.MaxCut

lemma muWeight_nonneg {M : ℕ} {ρ : ℝ} (hρ₁ : -1 < ρ) (hρ₂ : ρ < 0) (μ : Fin M → Bool) :
    0 ≤ muWeight ρ μ := by
  unfold muWeight
  refine Finset.prod_nonneg (fun i _ => ?_)
  cases μ i <;> simp [pm] <;> linarith

lemma ite_xor_self_eq_one_sub_pm (b m : Bool) :
    (if b ≠ xor b m then (1 : ℝ) else 0) = (1 - pm m) / 2 := by
  cases b <;> cases m <;> norm_num [pm]

lemma sum_muWeight_one_sub_pm {M : ℕ} (ρ : ℝ) (i₀ : Fin M) :
    ∑ μ : Fin M → Bool, muWeight ρ μ * ((1 - pm (μ i₀)) / 2) = 1 / 2 - ρ / 2 := by
  have hprod : ∀ μ : Fin M → Bool,
      muWeight ρ μ * ((1 - pm (μ i₀)) / 2) =
      ∏ i : Fin M, ((1 + ρ * pm (μ i)) / 2 * if i = i₀ then (1 - pm (μ i)) / 2 else 1) := by
    intro μ
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ i₀)]
    rfl
  simp_rw [hprod]
  rw [(Fintype.prod_sum (fun (i : Fin M) (b : Bool) =>
    (1 + ρ * pm b) / 2 * if i = i₀ then (1 - pm b) / 2 else 1)).symm]
  have hfactor : ∀ i ∈ (Finset.univ : Finset (Fin M)),
      (∑ b : Bool, (1 + ρ * pm b) / 2 * if i = i₀ then (1 - pm b) / 2 else 1) =
      if i = i₀ then 1 / 2 - ρ / 2 else 1 := by
    intro i _
    rw [Fintype.sum_bool]
    have ht : pm true = -1 := rfl
    have hf : pm false = 1 := rfl
    rw [ht, hf]
    split_ifs <;> ring
  rw [Finset.prod_congr rfl hfactor, Finset.prod_ite_eq', if_pos (Finset.mem_univ i₀)]

noncomputable def edgePairProb (L : ULC) (ρ : ℝ) (lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M))
    (v : Fin L.nV) (w w' : Fin L.nW) : ℝ :=
  (2 ^ L.M : ℝ)⁻¹ * ∑ x : Fin L.M → Bool, ∑ μ : Fin L.M → Bool, muWeight ρ μ *
    (if longCode (lab.2 w) (compose x (L.σ v w)) ≠
      longCode (lab.2 w') (coordMul (compose x (L.σ v w')) μ) then 1 else 0)

lemma sat_pair_prob (L : ULC) (ρ : ℝ) (lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M))
    (v : Fin L.nV) (w w' : Fin L.nW)
    (hw : L.σ v w (lab.2 w) = lab.1 v) (hw' : L.σ v w' (lab.2 w') = lab.1 v) :
    edgePairProb L ρ lab v w w' = 1 / 2 - ρ / 2 := by
  unfold edgePairProb
  have hterm : ∀ (x μ : Fin L.M → Bool),
      (if longCode (lab.2 w) (compose x (L.σ v w)) ≠
        longCode (lab.2 w') (coordMul (compose x (L.σ v w')) μ) then (1 : ℝ) else 0) =
      (1 - pm (μ (lab.2 w'))) / 2 := by
    intro x μ
    change (if x (L.σ v w (lab.2 w)) ≠ xor (x (L.σ v w' (lab.2 w'))) (μ (lab.2 w')) then (1 : ℝ) else 0) =
      (1 - pm (μ (lab.2 w'))) / 2
    simp only [hw, hw', ite_xor_self_eq_one_sub_pm]
  simp_rw [hterm, sum_muWeight_one_sub_pm, Finset.sum_const, Finset.card_univ,
    Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have h2M : (2 : ℝ) ^ L.M ≠ 0 := pow_ne_zero L.M (by norm_num)
  push_cast
  field_simp [h2M]

def satW (L : ULC) (lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M)) (v : Fin L.nV) :
    Finset (Fin L.nW) :=
  (L.nbrs v).filter (fun w => L.σ v w (lab.2 w) = lab.1 v)

lemma card_E_filter_eq_sum_nbrs (L : ULC) (p : Fin L.nV × Fin L.nW → Prop) [DecidablePred p] :
    (L.E.filter p).card = ∑ v : Fin L.nV, ((L.nbrs v).filter (fun w => p (v, w))).card := by
  simp only [ULC.nbrs, Finset.filter_filter, Finset.card_filter]
  have hE : L.E = Finset.univ.filter (fun e => e ∈ L.E) := by ext; simp
  conv_lhs => rw [hE, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun w _ => ?_))
  by_cases he : (v, w) ∈ L.E <;> by_cases hp : p (v, w) <;> simp [he, hp]

lemma card_E_eq_nV_mul_d (L : ULC) {d : ℕ} (hcard : ∀ v, (L.nbrs v).card = d) :
    L.E.card = L.nV * d := by
  have h := card_E_filter_eq_sum_nbrs L (fun _ => True)
  simp only [Finset.filter_true] at h
  rw [h]
  simp [hcard, Finset.card_univ, Fintype.card_fin]

lemma sum_satW_card (L : ULC) (lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M)) :
    ∑ v : Fin L.nV, (satW L lab v).card =
      (L.E.filter (fun e => L.σ e.1 e.2 (lab.2 e.2) = lab.1 e.1)).card := by
  exact (card_E_filter_eq_sum_nbrs L (fun e => L.σ e.1 e.2 (lab.2 e.2) = lab.1 e.1)).symm

lemma satFrac_eq_avg (L : ULC) {d : ℕ} (hnV0 : (L.nV : ℝ) ≠ 0) (hd0 : (d : ℝ) ≠ 0)
    (hcard : ∀ v, (L.nbrs v).card = d)
    (lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M)) :
    (L.nV : ℝ)⁻¹ * ∑ v : Fin L.nV, ((satW L lab v).card : ℝ) / d = L.satFrac lab := by
  unfold ULC.satFrac
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_satW_card L lab, card_E_eq_nV_mul_d L hcard, Nat.cast_mul]
  generalize (((L.E.filter (fun e => L.σ e.1 e.2 (lab.2 e.2) = lab.1 e.1)).card : ℕ) : ℝ) = S
  field_simp [hnV0, hd0]

lemma accProb_eq_sum_edgePairProb (L : ULC) (ρ : ℝ) (lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M)) :
    accProb L ρ (fun w => longCode (lab.2 w)) =
      (L.nV : ℝ)⁻¹ * ∑ v : Fin L.nV, ((L.nbrs v).card : ℝ)⁻¹ ^ 2 *
        ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, edgePairProb L ρ lab v w w' := rfl

theorem solution (L : ULC) (hreg : L.IsVRegular) (ρ : ℝ) (hρ₁ : -1 < ρ) (hρ₂ : ρ < 0)
    (η : ℝ) (lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M)) (hlab : 1 - η ≤ L.satFrac lab) :
    (1 - 2 * η) * (1 / 2 - ρ / 2) ≤ accProb L ρ (fun w => longCode (lab.2 w)) := by
  obtain ⟨hnV, d, hd, hcard⟩ := hreg
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hnV0 : (L.nV : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnV)
  have hρ_pos : 0 < 1 / 2 - ρ / 2 := by linarith
  have hterm_nonneg : ∀ v w w', 0 ≤ edgePairProb L ρ lab v w w' := by
    intro v w w'
    unfold edgePairProb
    refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun μ _ => ?_)))
    refine mul_nonneg (muWeight_nonneg hρ₁ hρ₂ μ) ?_
    split_ifs <;> norm_num
  have hv_bound : ∀ v : Fin L.nV,
      (2 * (((satW L lab v).card : ℝ) / d) - 1) * (1 / 2 - ρ / 2) ≤
        ((L.nbrs v).card : ℝ)⁻¹ ^ 2 * ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, edgePairProb L ρ lab v w w' := by
    intro v
    have hsub : satW L lab v ⊆ L.nbrs v := Finset.filter_subset _ _
    have hsum1 : ∑ w ∈ satW L lab v, ∑ w' ∈ satW L lab v, edgePairProb L ρ lab v w w' ≤
        ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, edgePairProb L ρ lab v w w' := by
      trans ∑ w ∈ satW L lab v, ∑ w' ∈ L.nbrs v, edgePairProb L ρ lab v w w'
      · refine Finset.sum_le_sum (fun w _ => ?_)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w' _ _ => hterm_nonneg v w w')
      · refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => ?_)
        exact Finset.sum_nonneg (fun w' _ => hterm_nonneg v w w')
    have hsum_sat : ∑ w ∈ satW L lab v, ∑ w' ∈ satW L lab v, edgePairProb L ρ lab v w w' =
        ((satW L lab v).card : ℝ) ^ 2 * (1 / 2 - ρ / 2) := by
      have heq : ∀ w ∈ satW L lab v, ∀ w' ∈ satW L lab v, edgePairProb L ρ lab v w w' = 1 / 2 - ρ / 2 := by
        intro w hw w' hw'
        exact sat_pair_prob L ρ lab v w w' (Finset.mem_filter.mp hw).2 (Finset.mem_filter.mp hw').2
      trans ∑ w ∈ satW L lab v, ∑ _w' ∈ satW L lab v, (1 / 2 - ρ / 2)
      · refine Finset.sum_congr rfl (fun w hw => Finset.sum_congr rfl (fun w' hw' => heq w hw w' hw'))
      · rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
        ring
    have hsq : 2 * (((satW L lab v).card : ℝ) / d) - 1 ≤ (((satW L lab v).card : ℝ) / d) ^ 2 := by
      nlinarith [sq_nonneg (((satW L lab v).card : ℝ) / d - 1)]
    calc (2 * (((satW L lab v).card : ℝ) / d) - 1) * (1 / 2 - ρ / 2)
        ≤ (((satW L lab v).card : ℝ) / d) ^ 2 * (1 / 2 - ρ / 2) :=
          mul_le_mul_of_nonneg_right hsq hρ_pos.le
      _ = ((L.nbrs v).card : ℝ)⁻¹ ^ 2 * (((satW L lab v).card : ℝ) ^ 2 * (1 / 2 - ρ / 2)) := by
          rw [hcard v]
          field_simp [hd0]
      _ = ((L.nbrs v).card : ℝ)⁻¹ ^ 2 * ∑ w ∈ satW L lab v, ∑ w' ∈ satW L lab v, edgePairProb L ρ lab v w w' := by
          rw [hsum_sat]
      _ ≤ ((L.nbrs v).card : ℝ)⁻¹ ^ 2 * ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, edgePairProb L ρ lab v w w' := by
          exact mul_le_mul_of_nonneg_left hsum1 (by positivity)
  have hsum_v := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hv_bound v)
  have havg := mul_le_mul_of_nonneg_left hsum_v (by positivity : (0 : ℝ) ≤ (L.nV : ℝ)⁻¹)
  have hsatFrac := satFrac_eq_avg L hnV0 hd0 hcard lab
  have hlhs : (L.nV : ℝ)⁻¹ * ∑ v : Fin L.nV,
        (2 * (((satW L lab v).card : ℝ) / d) - 1) * (1 / 2 - ρ / 2) =
      (2 * L.satFrac lab - 1) * (1 / 2 - ρ / 2) := by
    rw [← Finset.sum_mul, ← mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 : (L.nV : ℝ)⁻¹ * (2 * ∑ v : Fin L.nV, ((satW L lab v).card : ℝ) / d - (L.nV : ℝ) * 1) =
        2 * ((L.nV : ℝ)⁻¹ * ∑ v : Fin L.nV, ((satW L lab v).card : ℝ) / d) - 1 := by
      generalize (∑ v : Fin L.nV, ((satW L lab v).card : ℝ) / d) = S
      field_simp [hnV0]
    rw [h1, hsatFrac]
  rw [hlhs] at havg
  have h1 : (1 - 2 * η) * (1 / 2 - ρ / 2) ≤ (2 * L.satFrac lab - 1) * (1 / 2 - ρ / 2) := by
    refine mul_le_mul_of_nonneg_right ?_ hρ_pos.le
    linarith
  rw [accProb_eq_sum_edgePairProb]
  exact h1.trans havg
