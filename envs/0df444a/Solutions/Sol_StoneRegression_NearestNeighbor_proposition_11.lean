-- Prove2me | solution 1 for StoneRegression.NearestNeighbor.proposition_11
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:51:58.022328+00:00
-- url     : https://prove2.me/submissions/95568871-d8b6-4c17-9c8d-147c7b1082a4

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_NearestNeighbor_Weights



namespace StoneRegression.NearestNeighbor

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

lemma cs_apply {d : ℕ} (bv : Fin d → ℝ) (u : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    coordScale bv u j = bv j * u j := rfl

lemma cs_sq {d : ℕ} (bv : Fin d → ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    ‖coordScale bv u‖ ^ 2 = ∑ j, (bv j * u j) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [cs_apply, Real.norm_eq_abs, sq_abs]

lemma cs_le {d : ℕ} (bv : Fin d → ℝ) (a b : ℝ) (ha : 0 < a) (hbv : ∀ j, a ≤ bv j ∧ bv j ≤ b)
    (u : EuclideanSpace ℝ (Fin d)) : ‖coordScale bv u‖ ≤ b * ‖u‖ := by
  have hsq : ‖coordScale bv u‖ ^ 2 ≤ (b * ‖u‖) ^ 2 := by
    rw [cs_sq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [Real.norm_eq_abs, sq_abs, mul_pow]
    have h1 := hbv j
    have : bv j ^ 2 ≤ b ^ 2 := by nlinarith
    nlinarith [sq_nonneg (u j)]
  by_cases hd : ∃ j : Fin d, True
  · obtain ⟨j, -⟩ := hd
    have hb : 0 ≤ b := by linarith [(hbv j).1, (hbv j).2]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq
  · push_neg at hd
    have : coordScale bv u = 0 := by ext j; exact absurd (hd j) (by simp)
    rw [this, norm_zero]
    have : u = 0 := by ext j; exact absurd (hd j) (by simp)
    simp [this]

lemma cs_ge {d : ℕ} (bv : Fin d → ℝ) (a b : ℝ) (ha : 0 < a) (hbv : ∀ j, a ≤ bv j ∧ bv j ≤ b)
    (u : EuclideanSpace ℝ (Fin d)) : a * ‖u‖ ≤ ‖coordScale bv u‖ := by
  have hsq : (a * ‖u‖) ^ 2 ≤ ‖coordScale bv u‖ ^ 2 := by
    rw [cs_sq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [Real.norm_eq_abs, sq_abs, mul_pow]
    have h1 := hbv j
    have : a ^ 2 ≤ bv j ^ 2 := by nlinarith
    nlinarith [sq_nonneg (u j)]
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 hsq

lemma cs_lin {d : ℕ} (bv : Fin d → ℝ) (r : ℝ) (u v : EuclideanSpace ℝ (Fin d)) :
    coordScale bv v - coordScale bv u = (1 - r) • coordScale bv v + coordScale bv (r • v - u) := by
  ext j
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, cs_apply, smul_eq_mul]
  ring

theorem p10_core {d : ℕ} (a b : ℝ) (bv : Fin d → ℝ) (ha : 0 < a) (hbv : ∀ j, a ≤ bv j ∧ bv j ≤ b)
    (V : Set (EuclideanSpace ℝ (Fin d))) (hV : V ∈ ConeFamily d (a / b))
    (u v : EuclideanSpace ℝ (Fin d)) (hu : u ∈ V) (hv : v ∈ V) (hu0 : 0 < ‖u‖) (huv : ‖u‖ ≤ ‖v‖) :
    ‖coordScale bv v - coordScale bv u‖ < ‖coordScale bv v‖ := by
  have hu0' : u ≠ 0 := norm_pos_iff.1 hu0
  have hvp : 0 < ‖v‖ := lt_of_lt_of_le hu0 huv
  have hv0' : v ≠ 0 := norm_pos_iff.1 hvp
  obtain ⟨j, -⟩ : ∃ j : Fin d, True := by
    by_contra h
    push_neg at h
    exact hu0' (by ext j; exact absurd (h j) (by simp))
  have hb : 0 < b := by linarith [(hbv j).1, (hbv j).2]
  set s := ‖u‖ with hs
  set t := ‖v‖ with ht
  set r := s / t with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := div_le_one_of_le₀ huv (le_of_lt hvp)
  have hcone := hV u hu v hv hu0' hv0'
  set c := a / b with hc
  have hcb : b * c = a := by rw [hc]; field_simp
  have hcpos : 0 < c := by positivity
  -- ‖r v - u‖ < c s
  have hdiff : ‖r • v - u‖ < c * s := by
    have h2 : ‖r • v - u‖ ^ 2 = r ^ 2 * t ^ 2 - 2 * r * inner ℝ u v + s ^ 2 := by
      rw [@norm_sub_sq_real, norm_smul, real_inner_smul_left, real_inner_comm, Real.norm_eq_abs,
        abs_of_nonneg hr0]
      ring
    have hrt : r * t = s := by rw [hr]; field_simp
    have h3 : ‖r • v - u‖ ^ 2 < (c * s) ^ 2 := by
      rw [h2]
      have : r * ((1 - c ^ 2 / 2) * (s * t)) < r * inner ℝ u v := by
        have hrpos : 0 < r := by positivity
        exact mul_lt_mul_of_pos_left hcone hrpos
      have e1 : r ^ 2 * t ^ 2 = s ^ 2 := by rw [← hrt]; ring
      have e2 : r * ((1 - c ^ 2 / 2) * (s * t)) = (1 - c ^ 2 / 2) * s ^ 2 := by
        rw [show r * ((1 - c ^ 2 / 2) * (s * t)) = (1 - c ^ 2 / 2) * s * (r * t) by ring, hrt]; ring
      nlinarith
    exact (sq_lt_sq₀ (norm_nonneg _) (by positivity)).1 h3
  rw [cs_lin bv r u v]
  calc ‖(1 - r) • coordScale bv v + coordScale bv (r • v - u)‖
      ≤ ‖(1 - r) • coordScale bv v‖ + ‖coordScale bv (r • v - u)‖ := norm_add_le _ _
    _ ≤ (1 - r) * ‖coordScale bv v‖ + b * ‖r • v - u‖ := by
        gcongr
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        · exact cs_le bv a b ha hbv _
    _ < (1 - r) * ‖coordScale bv v‖ + b * (c * s) := by gcongr
    _ = (1 - r) * ‖coordScale bv v‖ + r * (a * t) := by
        rw [← mul_assoc, hcb, hr]; field_simp
    _ ≤ (1 - r) * ‖coordScale bv v‖ + r * ‖coordScale bv v‖ := by
        gcongr; exact cs_ge bv a b ha hbv v
    _ = ‖coordScale bv v‖ := by ring


open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable def avgI (G : ℕ → ℝ) (α k : ℕ) : ℝ := (∑ t ∈ Finset.range k, G (α + t)) / (k : ℝ)

lemma avgI_L1 (G : ℕ → ℝ) (hG : Antitone G) (α k : ℕ) (hk : 1 ≤ k) :
    avgI G α (k + 1) ≤ avgI G α k := by
  unfold avgI
  rw [Finset.sum_range_succ]
  have hS : (k : ℝ) * G (α + k) ≤ ∑ t ∈ Finset.range k, G (α + t) := by
    have : ∑ t ∈ Finset.range k, G (α + k) ≤ ∑ t ∈ Finset.range k, G (α + t) :=
      Finset.sum_le_sum (fun t ht => hG (by simp at ht; omega))
    simpa using this
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_le_div_iff₀ (by push_cast; linarith) hk']
  push_cast
  nlinarith

lemma avgI_L2 (G : ℕ → ℝ) (hG : Antitone G) (α k : ℕ) (hk : 1 ≤ k) :
    avgI G (α + 1) k ≤ avgI G α (k + 1) := by
  unfold avgI
  rw [Finset.sum_range_succ']
  have hS : ∑ t ∈ Finset.range k, G (α + 1 + t) ≤ (k : ℝ) * G (α + 0) := by
    have : ∑ t ∈ Finset.range k, G (α + 1 + t) ≤ ∑ t ∈ Finset.range k, G (α + 0) :=
      Finset.sum_le_sum (fun t ht => hG (by omega))
    simpa using this
  have e : ∑ t ∈ Finset.range k, G (α + (t + 1)) = ∑ t ∈ Finset.range k, G (α + 1 + t) :=
    Finset.sum_congr rfl (fun t _ => by congr 1; omega)
  rw [e]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_le_div_iff₀ hk' (by push_cast; linarith)]
  push_cast
  nlinarith

lemma avgI_shift (G : ℕ → ℝ) (hG : Antitone G) (A : ℕ) :
    ∀ j k, 1 ≤ k → avgI G (A + j) k ≤ avgI G A (j + k) := by
  intro j
  induction j with
  | zero => intro k _; simp
  | succ j ih =>
    intro k hk
    calc avgI G (A + (j + 1)) k = avgI G (A + j + 1) k := by rw [add_assoc]
      _ ≤ avgI G (A + j) (k + 1) := avgI_L2 G hG _ k hk
      _ ≤ avgI G A (j + (k + 1)) := ih (k + 1) (by omega)
      _ = avgI G A (j + 1 + k) := by congr 1; omega

lemma avgI_ext (G : ℕ → ℝ) (hG : Antitone G) (A L : ℕ) (hL : 1 ≤ L) :
    ∀ j, avgI G A (L + j) ≤ avgI G A L := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    calc avgI G A (L + (j + 1)) = avgI G A (L + j + 1) := by rw [add_assoc]
      _ ≤ avgI G A (L + j) := avgI_L1 G hG _ _ (by omega)
      _ ≤ _ := ih

lemma avgI_main (G : ℕ → ℝ) (hG : Antitone G) (α k A L : ℕ) (hαA : A ≤ α) (hk : 1 ≤ k)
    (hL : 1 ≤ L) (hAL : A + L ≤ α + k) : avgI G α k ≤ avgI G A L := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hαA
  obtain ⟨j', hj'⟩ := Nat.exists_eq_add_of_le (show L ≤ j + k by omega)
  calc avgI G (A + j) k ≤ avgI G A (j + k) := avgI_shift G hG A j k hk
    _ = avgI G A (L + j') := by rw [hj']
    _ ≤ avgI G A L := avgI_ext G hG A L hL j'

lemma avgI_anti (G : ℕ → ℝ) (hG : Antitone G) (L : ℕ) : Antitone (fun r => avgI G r L) := by
  intro r r' h
  unfold avgI
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum (fun t _ => hG (by omega))

lemma rank_sum {ι : Type*} [DecidableEq ι] (h : ℕ → ℝ) (hh : Antitone h) (w : ι → ℝ) :
    ∀ N (S : Finset ι), S.card = N → ∀ k : ι → ℕ,
      (∀ i ∈ S, (S.filter (fun l => l ≠ i ∧ w l ≤ w i)).card ≤ k i) →
      ∑ i ∈ S, h (k i) ≤ ∑ r ∈ Finset.range S.card, h r := by
  intro N
  induction N with
  | zero => intro S hS k _; rw [Finset.card_eq_zero.1 hS]; simp
  | succ N ih =>
    intro S hS k hk
    have hne : S.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image S w hne
    have hcardE : (S.erase i0).card = N := by rw [Finset.card_erase_of_mem hi0]; omega
    have hfil : S.filter (fun l => l ≠ i0 ∧ w l ≤ w i0) = S.erase i0 := by
      ext l; simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨h1, h2, hmax l h1⟩
    have hk0 : N ≤ k i0 := by have := hk i0 hi0; rw [hfil, hcardE] at this; exact this
    have hrest : ∑ i ∈ S.erase i0, h (k i) ≤ ∑ r ∈ Finset.range (S.erase i0).card, h r := by
      apply ih _ hcardE k
      intro i hi
      refine le_trans (Finset.card_le_card ?_) (hk i (Finset.mem_of_mem_erase hi))
      intro l hl
      simp only [Finset.mem_filter] at hl ⊢
      exact ⟨Finset.mem_of_mem_erase hl.1, hl.2⟩
    rw [← Finset.add_sum_erase S _ hi0, hS, Finset.sum_range_succ, add_comm]
    rw [hcardE] at hrest
    exact add_le_add hrest (hh hk0)

lemma sum_tail (G : ℕ → ℝ) (hG0 : ∀ m, 0 ≤ G m) (hG1 : ∀ M, ∑ m ∈ Finset.range M, G m ≤ 1)
    (t p : ℕ) : ∑ r ∈ Finset.range p, G (r + t) ≤ 1 - ∑ m ∈ Finset.range t, G m := by
  have := hG1 (t + p)
  rw [Finset.sum_range_add] at this
  have e : ∑ r ∈ Finset.range p, G (r + t) = ∑ x ∈ Finset.range p, G (t + x) :=
    Finset.sum_congr rfl (fun r _ => by rw [add_comm])
  linarith

lemma C_sub (G : ℕ → ℝ) (hG : Antitone G) (t q : ℕ) (ht : t ≤ q) :
    ∑ m ∈ Finset.range q, G m ≤ ∑ m ∈ Finset.range t, G m + ∑ m ∈ Finset.range (q - t), G m := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [Finset.sum_range_add, Nat.add_sub_cancel_left]
  gcongr with x _
  exact hG (by omega)

lemma cone_sum (G : ℕ → ℝ) (hG : Antitone G) (hG0 : ∀ m, 0 ≤ G m)
    (hG1 : ∀ M, ∑ m ∈ Finset.range M, G m ≤ 1) (p q : ℕ) :
    ∑ r ∈ Finset.range p, avgI G r (q + 1) ≤ 1 - (∑ m ∈ Finset.range q, G m) / 2 := by
  set C : ℕ → ℝ := fun t => ∑ m ∈ Finset.range t, G m with hC
  have hq : (0 : ℝ) < (q + 1 : ℕ) := by positivity
  have e1 : ∑ r ∈ Finset.range p, avgI G r (q + 1) =
      (∑ t ∈ Finset.range (q + 1), ∑ r ∈ Finset.range p, G (r + t)) / ((q + 1 : ℕ) : ℝ) := by
    unfold avgI
    rw [← Finset.sum_div, Finset.sum_comm]
  have e2 : ∑ t ∈ Finset.range (q + 1), ∑ r ∈ Finset.range p, G (r + t) ≤
      ∑ t ∈ Finset.range (q + 1), (1 - C t) :=
    Finset.sum_le_sum (fun t _ => sum_tail G hG0 hG1 t p)
  have e3 : ((q + 1 : ℕ) : ℝ) * C q ≤ 2 * ∑ t ∈ Finset.range (q + 1), C t := by
    have hr := Finset.sum_range_reflect C (q + 1)
    have : ∑ t ∈ Finset.range (q + 1), C q ≤
        ∑ t ∈ Finset.range (q + 1), (C t + C (q + 1 - 1 - t)) := by
      apply Finset.sum_le_sum
      intro t ht
      simp only [Finset.mem_range] at ht
      have := C_sub G hG t q (by omega)
      simp only [hC]
      rw [show q + 1 - 1 - t = q - t by omega]
      exact this
    rw [Finset.sum_add_distrib, hr] at this
    simp at this
    push_cast at this ⊢
    linarith
  rw [e1, div_le_iff₀ hq]
  have e4 : ∑ t ∈ Finset.range (q + 1), (1 - C t) = ((q + 1 : ℕ) : ℝ) - ∑ t ∈ Finset.range (q + 1), C t := by
    rw [Finset.sum_sub_distrib]; simp
  have : (1 - C q / 2) * ((q + 1 : ℕ) : ℝ) = ((q + 1 : ℕ) : ℝ) - ((q + 1 : ℕ) : ℝ) * C q / 2 := by ring
  show _ ≤ (1 - C q / 2) * _
  linarith

/-- covering existence -/
lemma cover_exists {d : ℕ} (c : ℝ) (hc : 0 < c) : ∃ k, ∃ V : Fin k → Set (EuclideanSpace ℝ (Fin d)),
    (∀ m, V m ∈ ConeFamily d c) ∧ (⋃ m, V m) = Set.univ := by
  classical
  obtain ⟨t, ht, hcov⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin d)) 1).elim_nhds_subcover
    (fun p => Metric.ball p (c / 2)) (fun p _ => Metric.ball_mem_nhds p (by positivity))
  let cone : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)) :=
    fun p => {w | w = 0 ∨ dist (‖w‖⁻¹ • w) p < c / 2}
  have hn1 : ∀ w : EuclideanSpace ℝ (Fin d), w ≠ 0 → ‖‖w‖⁻¹ • w‖ = 1 := by
    intro w hw; rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)]
  have hcone : ∀ p, cone p ∈ ConeFamily d c := by
    intro p u hu v hv hu0 hv0
    rcases hu with hu | hu
    · exact absurd hu hu0
    rcases hv with hv | hv
    · exact absurd hv hv0
    have hd : dist (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) < c := by
      calc _ ≤ dist (‖u‖⁻¹ • u) p + dist (‖v‖⁻¹ • v) p := dist_triangle_right _ _ _
        _ < c / 2 + c / 2 := add_lt_add hu hv
        _ = c := by ring
    rw [dist_eq_norm] at hd
    have hsq : ‖‖u‖⁻¹ • u - ‖v‖⁻¹ • v‖ ^ 2 < c ^ 2 := by
      have := norm_nonneg (‖u‖⁻¹ • u - ‖v‖⁻¹ • v)
      nlinarith
    rw [@norm_sub_sq_real, hn1 u hu0, hn1 v hv0, real_inner_smul_left,
      real_inner_smul_right] at hsq
    have hnu : 0 < ‖u‖ := norm_pos_iff.2 hu0
    have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have key : (1 - c ^ 2 / 2) < ‖u‖⁻¹ * (‖v‖⁻¹ * inner ℝ u v) := by nlinarith
    have : ‖u‖⁻¹ * (‖v‖⁻¹ * inner ℝ u v) = inner ℝ u v / (‖u‖ * ‖v‖) := by
      field_simp
    rw [this, lt_div_iff₀ (by positivity)] at key
    exact key
  let V : Fin (t.card + 1) → Set (EuclideanSpace ℝ (Fin d)) :=
    Fin.cons ({0} : Set (EuclideanSpace ℝ (Fin d))) (fun m => cone (t.equivFin.symm m).1)
  refine ⟨t.card + 1, V, ?_, ?_⟩
  · intro m
    refine Fin.cases ?_ (fun m => ?_) m
    · intro u hu v hv hu0 hv0
      exact absurd hu hu0
    · simp only [V, Fin.cons_succ]
      exact hcone _
  · apply Set.eq_univ_of_forall
    intro w
    rw [Set.mem_iUnion]
    by_cases hw : w = 0
    · exact ⟨0, by simp [V, hw]⟩
    · have hs : ‖w‖⁻¹ • w ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
        simp [hn1 w hw]
      have := hcov hs
      simp only [Set.mem_iUnion] at this
      obtain ⟨p, hp, hb⟩ := this
      refine ⟨Fin.succ (t.equivFin ⟨p, hp⟩), ?_⟩
      simp only [V, Fin.cons_succ, Equiv.symm_apply_apply]
      exact Or.inr hb


noncomputable def Gs (c : ℕ → ℕ → ℝ) (n : ℕ) (m : ℕ) : ℝ := c n (m + 1)

lemma Gs_nonneg {c : ℕ → ℕ → ℝ} {n : ℕ} (hc : IsCoeffRow c n) (m : ℕ) : 0 ≤ Gs c n m := by
  unfold Gs
  by_cases h : m + 1 ≤ n
  · exact le_trans hc.2.1 (hc.1 (m+1) n (by omega) h le_rfl)
  · rw [hc.2.2.1 _ (by omega)]

lemma Gs_anti {c : ℕ → ℕ → ℝ} {n : ℕ} (hc : IsCoeffRow c n) : Antitone (Gs c n) := by
  intro m m' h
  by_cases h' : m' + 1 ≤ n
  · exact hc.1 (m+1) (m'+1) (by omega) (by omega) h'
  · show c n (m'+1) ≤ c n (m+1)
    rw [hc.2.2.1 _ (by omega)]; exact Gs_nonneg hc m

lemma Gs_le_one {c : ℕ → ℕ → ℝ} {n : ℕ} (hc : IsCoeffRow c n) (M : ℕ) :
    ∑ m ∈ Finset.range M, Gs c n m ≤ 1 := by
  have htot : ∑ m ∈ Finset.range n, Gs c n m = 1 := by
    rw [← hc.2.2.2, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    unfold Gs; rw [add_comm]
  calc _ ≤ ∑ m ∈ Finset.range (max M n), Gs c n m :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (le_max_left _ _))
          (fun m _ _ => Gs_nonneg hc m)
    _ = 1 := by
        obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (le_max_right M n)
        rw [hj, Finset.sum_range_add, htot]
        have : ∑ x ∈ Finset.range j, Gs c n (n + x) = 0 :=
          Finset.sum_eq_zero (fun x _ => by unfold Gs; exact hc.2.2.1 _ (by omega))
        rw [this, add_zero]

lemma W_gen (c : ℕ → ℕ → ℝ) (n : ℕ) (hc : IsCoeffRow c n) (A B : ℕ) (T' T L : ℕ) (hL : 1 ≤ L)
    (h1 : T' ≤ A) (h2 : T ≤ A + B) (hTL : T' + L ≤ T + 1) :
    (∑ m ∈ Finset.Ico (1 + A) (1 + A + (1 + B)), c n m) / ((1 + B : ℕ) : ℝ) ≤ avgI (Gs c n) T' L := by
  have e : (∑ m ∈ Finset.Ico (1 + A) (1 + A + (1 + B)), c n m) / ((1 + B : ℕ) : ℝ)
      = avgI (Gs c n) A (1 + B) := by
    unfold avgI
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    congr 1
    refine Finset.sum_congr rfl (fun t _ => ?_)
    unfold Gs; congr 1; omega
  rw [e]
  exact avgI_main _ (Gs_anti hc) A (1 + B) T' L h1 (by omega) hL (by omega)

lemma card_le_lt_eq {n : ℕ} (i : Fin n) (r : Fin n → ℝ) (T : Finset (Fin n))
    (h : ∀ l ∈ T, l ≠ i ∧ r l ≤ r i) :
    T.card ≤ (Finset.univ.filter fun l => l ≠ i ∧ r l < r i).card +
      (Finset.univ.filter fun l => l ≠ i ∧ r l = r i).card := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro l hl
  obtain ⟨h1, h2⟩ := h l hl
  rcases lt_or_eq_of_le h2 with h3 | h3
  · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h3⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h3⟩)

lemma W_bound {d n : ℕ} (c : ℕ → ℕ → ℝ) (s : ScaleSeq d) (hc : IsCoeffRow c n)
    (p : EuclideanSpace ℝ (Fin d)) (y : Fin n → EuclideanSpace ℝ (Fin d)) (i : Fin n)
    (T' T : Finset (Fin n)) (L : ℕ) (hL : 1 ≤ L)
    (h' : ∀ l ∈ T', l ≠ i ∧ rho (s n p y) (y l) p < rho (s n p y) (y i) p)
    (h : ∀ l ∈ T, l ≠ i ∧ rho (s n p y) (y l) p ≤ rho (s n p y) (y i) p)
    (hTL : T'.card + L ≤ T.card + 1) :
    nnWeights c s n p y i ≤ avgI (Gs c n) T'.card L := by
  unfold nnWeights nnNu nnLam
  refine W_gen c n hc _ _ T'.card T.card L hL ?_ (card_le_lt_eq i (fun l => rho (s n p y) (y l) p) T h) hTL
  exact Finset.card_le_card (fun l hl => Finset.mem_filter.2 ⟨Finset.mem_univ _, h' l hl⟩)

def good {d n : ℕ} (sx : Fin d → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin d) : Prop :=
  0 < sx j ∧ ∃ k l, xs k j ≠ xs l j

open Classical in
noncomputable def phi {d n : ℕ} (sx : Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => if good sx xs j then (y j - x j) / sx j else 0)

open Classical in
noncomputable def bvec {d n : ℕ} (sx si : Fin d → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d)) (a : ℝ) :
    Fin d → ℝ :=
  fun j => if good sx xs j then sx j / si j else a

lemma phi_good {d n : ℕ} (sx : Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (y : EuclideanSpace ℝ (Fin d)) (j : Fin d)
    (h : good sx xs j) : phi sx x xs y j = (y j - x j) / sx j := by
  simp [phi, h]

lemma phi_bad {d n : ℕ} (sx : Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (y : EuclideanSpace ℝ (Fin d)) (j : Fin d)
    (h : ¬ good sx xs j) : phi sx x xs y j = 0 := by
  simp [phi, h]

lemma bvec_good {d n : ℕ} (sx si : Fin d → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (j : Fin d) (h : good sx xs j) : bvec sx si xs a j = sx j / si j := by
  simp [bvec, h]

lemma bvec_bad {d n : ℕ} (sx si : Fin d → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (j : Fin d) (h : ¬ good sx xs j) : bvec sx si xs a j = a := by
  simp [bvec, h]

lemma cs_sub {d : ℕ} (bv : Fin d → ℝ) (u v : EuclideanSpace ℝ (Fin d)) :
    coordScale bv (u - v) = coordScale bv u - coordScale bv v := by
  ext j; simp only [PiLp.sub_apply, cs_apply]; ring

lemma cs_zero {d : ℕ} (bv : Fin d → ℝ) : coordScale bv (0 : EuclideanSpace ℝ (Fin d)) = 0 := by
  ext j; simp [cs_apply]

section geo
variable {d : ℕ} (s : ScaleSeq d) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (h7 : Cond7 s a b)
  {n : ℕ} (hn : 1 ≤ n) (x : EuclideanSpace ℝ (Fin d)) (xs : Fin n → EuclideanSpace ℝ (Fin d))
  (i : Fin n)
include ha hab h7 hn

lemma si_pos_of_good (j : Fin d) (hg : good (s n x xs) xs j) :
    0 < s n (xs i) (Function.update xs i x) j := by
  have h := (h7 n hn x xs i j hg.2).2
  have hb : 0 < b := by linarith
  by_contra hneg
  push_neg at hneg
  have : b * s n (xs i) (Function.update xs i x) j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb.le hneg
  linarith [hg.1]

lemma good_of_si_pos (j : Fin d) (hd : ∃ k l, xs k j ≠ xs l j)
    (hsi : 0 < s n (xs i) (Function.update xs i x) j) : good (s n x xs) xs j := by
  have h := (h7 n hn x xs i j hd).1
  exact ⟨by nlinarith, hd⟩

lemma bvec_bounds : ∀ j, a ≤ bvec (s n x xs) (s n (xs i) (Function.update xs i x)) xs a j ∧
    bvec (s n x xs) (s n (xs i) (Function.update xs i x)) xs a j ≤ b := by
  intro j
  by_cases hg : good (s n x xs) xs j
  · rw [bvec_good _ _ _ _ _ hg]
    have hsi := si_pos_of_good s a b ha hab h7 hn x xs i j hg
    have h := h7 n hn x xs i j hg.2
    exact ⟨(le_div_iff₀ hsi).2 h.1, (div_le_iff₀ hsi).2 h.2⟩
  · rw [bvec_bad _ _ _ _ _ hg]; exact ⟨le_rfl, hab⟩

lemma rho_eq_cs (k : Fin n) :
    rho (s n (xs i) (Function.update xs i x)) (xs k) (xs i) =
      ‖coordScale (bvec (s n x xs) (s n (xs i) (Function.update xs i x)) xs a)
        (phi (s n x xs) x xs (xs k) - phi (s n x xs) x xs (xs i))‖ := by
  rw [rho, ← Real.sqrt_sq (norm_nonneg _), cs_sq, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [PiLp.sub_apply]
  by_cases hg : good (s n x xs) xs j
  · have hsi := si_pos_of_good s a b ha hab h7 hn x xs i j hg
    rw [if_pos hsi, bvec_good _ _ _ _ _ hg, phi_good _ _ _ _ _ hg, phi_good _ _ _ _ _ hg]
    have := hg.1
    field_simp
    ring
  · rw [bvec_bad _ _ _ _ _ hg, phi_bad _ _ _ _ _ hg, phi_bad _ _ _ _ _ hg]
    by_cases hsi : 0 < s n (xs i) (Function.update xs i x) j
    · have hdeg : ¬ ∃ k l, xs k j ≠ xs l j := fun hd =>
        hg (good_of_si_pos s a b ha hab h7 hn x xs i j hd hsi)
      push_neg at hdeg
      rw [if_pos hsi, hdeg k i]
      simp
    · rw [if_neg hsi]; simp

lemma rho_ge_cs :
    ‖coordScale (bvec (s n x xs) (s n (xs i) (Function.update xs i x)) xs a)
        (phi (s n x xs) x xs (xs i))‖ ≤ rho (s n (xs i) (Function.update xs i x)) x (xs i) := by
  rw [rho, ← Real.sqrt_sq (norm_nonneg _), cs_sq, Finset.sum_filter]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum (fun j _ => ?_)
  by_cases hg : good (s n x xs) xs j
  · have hsi := si_pos_of_good s a b ha hab h7 hn x xs i j hg
    rw [if_pos hsi, bvec_good _ _ _ _ _ hg, phi_good _ _ _ _ _ hg]
    have := hg.1
    apply le_of_eq
    field_simp
    ring
  · rw [bvec_bad _ _ _ _ _ hg, phi_bad _ _ _ _ _ hg]
    split_ifs <;> simp [sq_nonneg]

end geo


lemma cs_neg {d : ℕ} (bv : Fin d → ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    coordScale bv (-u) = -coordScale bv u := by
  ext j; simp only [PiLp.neg_apply, cs_apply]; ring

theorem p12_aux {d : ℕ} (s : ScaleSeq d) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (h7 : Cond7 s a b)
    (c : ℕ → ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (hc : IsCoeffRow c n)
    (x : EuclideanSpace ℝ (Fin d)) (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (K : ℕ) (V : Fin K → Set (EuclideanSpace ℝ (Fin d)))
    (hV : ∀ m, V m ∈ ConeFamily d (a / b)) (hU : (⋃ m, V m) = Set.univ) :
    (∑ i, swapW (nnWeights c s) n x xs i) ≤ (K : ℝ) := by
  classical
  have hb : 0 < b := by linarith
  have hc0 : 0 < a / b := div_pos ha hb
  have hc1 : a / b ≤ 1 := (div_le_one hb).2 hab
  set sx := s n x xs with hsx
  let ph : Fin n → EuclideanSpace ℝ (Fin d) := fun i => phi sx x xs (xs i)
  have hmo : ∀ w : EuclideanSpace ℝ (Fin d), ∃ m, w ∈ V m := fun w => by
    have : w ∈ ⋃ m, V m := by rw [hU]; exact Set.mem_univ w
    exact Set.mem_iUnion.1 this
  let mo : EuclideanSpace ℝ (Fin d) → Fin K := fun w => (hmo w).choose
  have hmo' : ∀ w, w ∈ V (mo w) := fun w => (hmo w).choose_spec
  let Z := Finset.univ.filter (fun i => ph i = 0)
  obtain ⟨q, hq⟩ : ∃ q, q = Z.card := ⟨_, rfl⟩
  let G := Gs c n
  let C := ∑ m ∈ Finset.range q, G m
  let U := fun i => swapW (nnWeights c s) n x xs i
  let bv := fun i : Fin n => bvec sx (s n (xs i) (Function.update xs i x)) xs a
  -- distances
  have hrho : ∀ i k : Fin n, k ≠ i →
      rho (s n (xs i) (Function.update xs i x)) (Function.update xs i x k) (xs i) =
        ‖coordScale (bv i) (ph k - ph i)‖ := by
    intro i k hki
    rw [Function.update_of_ne hki]
    exact rho_eq_cs s a b ha hab h7 hn x xs i k
  have hrhoi : ∀ i : Fin n, ‖coordScale (bv i) (ph i)‖ ≤
      rho (s n (xs i) (Function.update xs i x)) (Function.update xs i x i) (xs i) := by
    intro i
    rw [Function.update_self]
    exact rho_ge_cs s a b ha hab h7 hn x xs i
  have hrho0 : ∀ i : Fin n, 0 ≤
      rho (s n (xs i) (Function.update xs i x)) (Function.update xs i x i) (xs i) :=
    fun i => Real.sqrt_nonneg _
  -- zero points
  have hZ : ∀ i ∈ Z, U i ≤ avgI G 0 q := by
    intro i hi
    have hq1 : 1 ≤ q := hq ▸ Finset.card_pos.2 ⟨i, hi⟩
    have hphi : ph i = 0 := (Finset.mem_filter.1 hi).2
    have := W_bound c s hc (xs i) (Function.update xs i x) i ∅ (Z.erase i) q hq1
      (by simp) (by
        intro l hl
        have hli := Finset.ne_of_mem_erase hl
        have hphl : ph l = 0 := (Finset.mem_filter.1 (Finset.mem_of_mem_erase hl)).2
        refine ⟨hli, ?_⟩
        rw [hrho i l hli, hphl, hphi, sub_zero, cs_zero, norm_zero]
        exact hrho0 i)
      (by rw [Finset.card_erase_of_mem hi, ← hq]; simp; omega)
    simp only [Finset.card_empty] at this
    exact this
  -- positive points
  let P : Fin K → Finset (Fin n) := fun m =>
    (Finset.univ.filter (fun l => ¬ ph l = 0)).filter (fun l => mo (ph l) = m)
  have hP : ∀ i, ¬ ph i = 0 → U i ≤
      avgI G ((P (mo (ph i))).filter (fun l => l ≠ i ∧ ‖ph l‖ ≤ ‖ph i‖)).card (q + 1) := by
    intro i hi
    set T' := (P (mo (ph i))).filter (fun l => l ≠ i ∧ ‖ph l‖ ≤ ‖ph i‖) with hT'
    have h' : ∀ l ∈ T', l ≠ i ∧
        rho (s n (xs i) (Function.update xs i x)) (Function.update xs i x l) (xs i) <
        rho (s n (xs i) (Function.update xs i x)) (Function.update xs i x i) (xs i) := by
      intro l hl
      simp only [hT', P, Finset.mem_filter, Finset.mem_univ, true_and] at hl
      obtain ⟨⟨hl0, hlm⟩, hli, hle⟩ := hl
      refine ⟨hli, ?_⟩
      rw [hrho i l hli, cs_sub, norm_sub_rev]
      refine lt_of_lt_of_le ?_ (hrhoi i)
      have hu : ph l ∈ V (mo (ph i)) := hlm ▸ hmo' (ph l)
      exact p10_core a b (bv i) ha (bvec_bounds s a b ha hab h7 hn x xs i) _ (hV _) (ph l) (ph i)
        hu (hmo' (ph i)) (norm_pos_iff.2 hl0) hle
    have hdisj : Disjoint T' Z := by
      rw [Finset.disjoint_left]
      intro l hl hlZ
      simp only [hT', P, Finset.mem_filter, Finset.mem_univ, true_and] at hl
      exact hl.1.1 (Finset.mem_filter.1 hlZ).2
    have := W_bound c s hc (xs i) (Function.update xs i x) i T' (T' ∪ Z) (q + 1) (by omega) h'
      (by
        intro l hl
        rcases Finset.mem_union.1 hl with hl | hl
        · exact ⟨(h' l hl).1, le_of_lt (h' l hl).2⟩
        · have hphl : ph l = 0 := (Finset.mem_filter.1 hl).2
          have hli : l ≠ i := fun e => hi (e ▸ hphl)
          refine ⟨hli, ?_⟩
          rw [hrho i l hli, hphl, zero_sub, cs_neg, norm_neg]
          exact hrhoi i)
      (by rw [Finset.card_union_of_disjoint hdisj, ← hq]; omega)
    exact this
  -- sums
  have hsplit : ∑ i, U i = ∑ i ∈ Z, U i + ∑ i ∈ Finset.univ.filter (fun i => ¬ ph i = 0), U i :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hZsum : ∑ i ∈ Z, U i ≤ C := by
    calc ∑ i ∈ Z, U i ≤ ∑ i ∈ Z, avgI G 0 q := Finset.sum_le_sum hZ
      _ = C := by
        rw [Finset.sum_const, nsmul_eq_mul, ← hq]
        unfold avgI
        simp only [zero_add]
        by_cases hq0 : q = 0
        · subst hq0; simp [C]
        · have : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
          rw [mul_div_cancel₀ _ this]
  have hcone : ∀ m, ∑ i ∈ P m, U i ≤ 1 - C / 2 := by
    intro m
    calc ∑ i ∈ P m, U i ≤ ∑ i ∈ P m,
          avgI G ((P m).filter (fun l => l ≠ i ∧ ‖ph l‖ ≤ ‖ph i‖)).card (q + 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' := Finset.mem_filter.1 hi
          have hi0 : ¬ ph i = 0 := (Finset.mem_filter.1 hi'.1).2
          have := hP i hi0
          rw [hi'.2] at this
          exact this
      _ ≤ ∑ r ∈ Finset.range (P m).card, avgI G r (q + 1) :=
          rank_sum (fun r => avgI G r (q + 1)) (avgI_anti G (Gs_anti hc) (q + 1))
            (fun l => ‖ph l‖) _ (P m) rfl _ (fun i _ => le_rfl)
      _ ≤ 1 - C / 2 := cone_sum G (Gs_anti hc) (Gs_nonneg hc) (Gs_le_one hc) _ q
  have hPsum : ∑ i ∈ Finset.univ.filter (fun i => ¬ ph i = 0), U i ≤ (K : ℝ) * (1 - C / 2) := by
    rw [← Finset.sum_fiberwise (Finset.univ.filter (fun i => ¬ ph i = 0)) (fun i => mo (ph i)) U]
    calc _ ≤ ∑ m : Fin K, (1 - C / 2) := Finset.sum_le_sum (fun m _ => hcone m)
      _ = _ := by simp; ring
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun m _ => Gs_nonneg hc m)
  have hC1 : C ≤ 1 := Gs_le_one hc q
  have hK1 : 1 ≤ K := Fin.pos (mo 0)
  show ∑ i, U i ≤ (K : ℝ)
  rw [hsplit]
  by_cases hpos : ∃ i, ¬ ph i = 0
  · obtain ⟨i, hi⟩ := hpos
    have hK2 : 2 ≤ K := by
      by_contra hK2
      have : Subsingleton (Fin K) := Fin.subsingleton_iff_le_one.2 (by omega)
      have heq : mo (-(ph i)) = mo (ph i) := Subsingleton.elim _ _
      have h1 := hmo' (-(ph i))
      rw [heq] at h1
      have hw : 0 < ‖ph i‖ := norm_pos_iff.2 hi
      have := hV _ (ph i) (hmo' (ph i)) (-(ph i)) h1 hi (neg_ne_zero.2 hi)
      rw [inner_neg_right, real_inner_self_eq_norm_sq, norm_neg] at this
      have hcc : (a / b) ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have hK2' : (2 : ℝ) ≤ K := by exact_mod_cast hK2
    nlinarith
  · push_neg at hpos
    have : Finset.univ.filter (fun i => ¬ ph i = 0) = ∅ := by
      ext i; simp [hpos i]
    rw [this, Finset.sum_empty]
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    linarith


theorem p12_core {d : ℕ} (s : ScaleSeq d) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (h7 : Cond7 s a b)
    (c : ℕ → ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (hc : IsCoeffRow c n)
    (x : EuclideanSpace ℝ (Fin d)) (xs : Fin n → EuclideanSpace ℝ (Fin d)) :
    (∑ i, swapW (nnWeights c s) n x xs i) ≤ (beta d (a / b) : ℝ) := by
  have hc0 : 0 < a / b := div_pos ha (by linarith)
  obtain ⟨V, hV, hU⟩ : ∃ V : Fin (beta d (a / b)) → Set (EuclideanSpace ℝ (Fin d)),
      (∀ m, V m ∈ ConeFamily d (a / b)) ∧ (⋃ m, V m) = Set.univ :=
    Nat.sInf_mem (cover_exists (d := d) (a / b) hc0)
  exact p12_aux s a b ha hab h7 c n hn hc x xs _ V hV hU


open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

lemma swap_apply {E : Type*} [MeasurableSpace E] (e : ℕ ≃ ℕ) (ω : ℕ → E) (b : ℕ) :
    MeasurableEquiv.piCongrLeft (fun _ : ℕ => E) e ω b = ω (e.symm b) := by
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

lemma swap_mp {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (e : ℕ ≃ ℕ) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ℕ => EuclideanSpace ℝ (Fin d)) e)
      (StoneRegression.Criterion.xLaw μ) (StoneRegression.Criterion.xLaw μ) :=
  ⟨(MeasurableEquiv.piCongrLeft _ e).measurable, Measure.infinitePi_map_piCongrLeft (fun _ => μ) e⟩

lemma meas_coord {d : ℕ} (j : Fin d) : Measurable (fun u : EuclideanSpace ℝ (Fin d) => u j) := by
  fun_prop

lemma rho_meas {d n : ℕ} (S : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) → Fin d → ℝ)
    (hS : Measurable S) (U V : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    (hU : Measurable U) (hV : Measurable V) :
    Measurable (fun p => rho (S p) (U p) (V p)) := by
  unfold rho
  simp_rw [Finset.sum_filter]
  apply Measurable.sqrt
  apply Finset.measurable_sum
  intro j _
  apply Measurable.ite
  · exact measurableSet_lt measurable_const ((measurable_pi_apply j).comp hS)
  · exact ((((meas_coord j).comp hU).sub ((meas_coord j).comp hV)).div ((measurable_pi_apply j).comp hS)).pow_const 2
  · exact measurable_const


lemma nnW_meas {d n : ℕ} (c : ℕ → ℕ → ℝ) (s : ScaleSeq d)
    (hs1 : Measurable (fun p : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) => s n p.1 p.2))
    (i : Fin n) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) =>
      nnWeights c s n p.1 p.2 i) := by
  have hR : ∀ l : Fin n, Measurable (fun p : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) =>
      rho (s n p.1 p.2) (p.2 l) p.1) :=
    fun l => rho_meas _ hs1 _ _ ((measurable_pi_apply l).comp measurable_snd) measurable_fst
  have hNu : Measurable (fun p : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) =>
      nnNu (s n p.1 p.2) p.1 p.2 i) := by
    unfold nnNu
    simp_rw [Finset.card_filter]
    apply Measurable.add measurable_const
    apply Finset.measurable_sum
    intro l _
    apply Measurable.ite _ measurable_const measurable_const
    exact (MeasurableSet.const _).inter (measurableSet_lt (hR l) (hR i))
  have hLam : Measurable (fun p : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) =>
      nnLam (s n p.1 p.2) p.1 p.2 i) := by
    unfold nnLam
    simp_rw [Finset.card_filter]
    apply Measurable.add measurable_const
    apply Finset.measurable_sum
    intro l _
    apply Measurable.ite _ measurable_const measurable_const
    exact (MeasurableSet.const _).inter (measurableSet_eq_fun (hR l) (hR i))
  let g : ℕ × ℕ → ℝ := fun q => (∑ m ∈ Finset.Ico q.1 (q.1 + q.2), c n m) / (q.2 : ℝ)
  have : (fun p : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) =>
      nnWeights c s n p.1 p.2 i) =
      g ∘ (fun p => (nnNu (s n p.1 p.2) p.1 p.2 i, nnLam (s n p.1 p.2) p.1 p.2 i)) := rfl
  rw [this]
  exact (measurable_of_countable g).comp (hNu.prodMk hLam)

lemma nnW_nonneg {d n : ℕ} (c : ℕ → ℕ → ℝ) (s : ScaleSeq d) (hc : IsCoeffRow c n)
    (x : EuclideanSpace ℝ (Fin d)) (xs : Fin n → EuclideanSpace ℝ (Fin d)) (i : Fin n) :
    0 ≤ nnWeights c s n x xs i := by
  unfold nnWeights
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro m hm
  have h1 : 1 ≤ m := le_trans (by unfold nnNu; omega) (Finset.mem_Ico.1 hm).1
  have := Gs_nonneg hc (m - 1)
  unfold Gs at this
  rwa [Nat.sub_add_cancel h1] at this

theorem p11_core {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (s : ScaleSeq d) (a b : ℝ) (hs : IsRegular μ s a b)
    (c : ℕ → ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (hc : IsCoeffRow c n)
    (f : EuclideanSpace ℝ (Fin d) → ℝ≥0) (hf : Measurable f) :
    ∫⁻ ω, ∑ i : Fin n, ENNReal.ofReal (StoneRegression.Criterion.wAt (nnWeights c s) n ω i) *
      (f (ω (i.val + 1)) : ℝ≥0∞) ∂(StoneRegression.Criterion.xLaw μ) ≤
      (beta d (a / b) : ℝ≥0∞) * ∫⁻ x, (f x : ℝ≥0∞) ∂μ := by
  obtain ⟨hmeas, hs0, -, -, ha, hab, h7⟩ := hs
  have hsamp : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) =>
      (ω 0, StoneRegression.Criterion.sample ω n)) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_lambda _ (fun l => measurable_pi_apply _))
  let F : Fin n → (ℕ → EuclideanSpace ℝ (Fin d)) → ℝ≥0∞ := fun i ω =>
    ENNReal.ofReal (StoneRegression.Criterion.wAt (nnWeights c s) n ω i) * (f (ω (i.val + 1)) : ℝ≥0∞)
  let Gf : Fin n → (ℕ → EuclideanSpace ℝ (Fin d)) → ℝ≥0∞ := fun i ω =>
    ENNReal.ofReal (swapW (nnWeights c s) n (ω 0) (StoneRegression.Criterion.sample ω n) i) *
      (f (ω 0) : ℝ≥0∞)
  have hF : ∀ i : Fin n, Measurable (F i) := by
    intro i
    exact (ENNReal.measurable_ofReal.comp ((nnW_meas c s (hmeas n) i).comp hsamp)).mul
      (measurable_coe_nnreal_ennreal.comp (hf.comp (measurable_pi_apply _)))
  have hpt : ∀ i : Fin n, ∀ ω, F i (MeasurableEquiv.piCongrLeft (fun _ : ℕ => EuclideanSpace ℝ (Fin d))
      (Equiv.swap 0 (i.val + 1)) ω) = Gf i ω := by
    intro i ω
    have h1 : StoneRegression.Criterion.sample (MeasurableEquiv.piCongrLeft (fun _ : ℕ => EuclideanSpace ℝ (Fin d))
        (Equiv.swap 0 (i.val + 1)) ω) n =
        Function.update (StoneRegression.Criterion.sample ω n) i (ω 0) := by
      funext l
      simp only [StoneRegression.Criterion.sample]
      rw [swap_apply]
      by_cases hl : l = i
      · subst hl; simp
      · rw [Function.update_of_ne hl]
        have : (l.val + 1) ≠ i.val + 1 := by intro h; exact hl (Fin.ext (by omega))
        rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne (Nat.succ_ne_zero _) this]
        rfl
    simp only [F, Gf, StoneRegression.Criterion.wAt, swapW]
    rw [h1, swap_apply, swap_apply, Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right]
    rfl
  have hG : ∀ i : Fin n, Measurable (Gf i) := by
    intro i
    have : Gf i = fun ω => F i (MeasurableEquiv.piCongrLeft (fun _ : ℕ => EuclideanSpace ℝ (Fin d))
        (Equiv.swap 0 (i.val + 1)) ω) := funext (fun ω => (hpt i ω).symm)
    rw [this]
    exact (hF i).comp (MeasurableEquiv.measurable _)
  have hswap : ∀ i : Fin n, ∫⁻ ω, F i ω ∂(StoneRegression.Criterion.xLaw μ) =
      ∫⁻ ω, Gf i ω ∂(StoneRegression.Criterion.xLaw μ) := by
    intro i
    rw [← (swap_mp μ (Equiv.swap 0 (i.val + 1))).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _)]
    exact lintegral_congr (fun ω => hpt i ω)
  show ∫⁻ ω, ∑ i : Fin n, F i ω ∂(StoneRegression.Criterion.xLaw μ) ≤ _
  rw [lintegral_finset_sum _ (fun i _ => hF i)]
  simp_rw [hswap]
  rw [← lintegral_finset_sum _ (fun i _ => hG i)]
  have hbound : ∀ ω : ℕ → EuclideanSpace ℝ (Fin d), ∑ i : Fin n, Gf i ω ≤
      (beta d (a / b) : ℝ≥0∞) * (f (ω 0) : ℝ≥0∞) := by
    intro ω
    simp only [Gf, swapW]
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => nnW_nonneg c s hc _ _ i)]
    gcongr
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (p12_core s a b ha hab h7 c n hn hc (ω 0) (StoneRegression.Criterion.sample ω n))
  calc ∫⁻ ω, ∑ i : Fin n, Gf i ω ∂(StoneRegression.Criterion.xLaw μ)
      ≤ ∫⁻ ω, (beta d (a / b) : ℝ≥0∞) * (f (ω 0) : ℝ≥0∞) ∂(StoneRegression.Criterion.xLaw μ) :=
        lintegral_mono hbound
    _ = (beta d (a / b) : ℝ≥0∞) * ∫⁻ ω, (f (ω 0) : ℝ≥0∞) ∂(StoneRegression.Criterion.xLaw μ) :=
        lintegral_const_mul _ (measurable_coe_nnreal_ennreal.comp (hf.comp (measurable_pi_apply 0)))
    _ = (beta d (a / b) : ℝ≥0∞) * ∫⁻ x, (f x : ℝ≥0∞) ∂μ := by
        congr 1
        exact (measurePreserving_eval_infinitePi (μ := fun _ : ℕ => μ) 0).lintegral_comp
          (measurable_coe_nnreal_ennreal.comp hf)

end StoneRegression.NearestNeighbor

open StoneRegression.NearestNeighbor
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem solution {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (s : ScaleSeq d) (a b : ℝ) (hs : IsRegular μ s a b)
    (c : ℕ → ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (hc : IsCoeffRow c n)
    (f : EuclideanSpace ℝ (Fin d) → ℝ≥0) (hf : Measurable f) (hfi : ∫⁻ x, (f x : ℝ≥0∞) ∂μ < ∞) :
    ∫⁻ ω, ∑ i : Fin n, ENNReal.ofReal (StoneRegression.Criterion.wAt (nnWeights c s) n ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(StoneRegression.Criterion.xLaw μ) ≤
      (beta d (a / b) : ℝ≥0∞) * ∫⁻ x, (f x : ℝ≥0∞) ∂μ := by
  exact p11_core μ s a b hs c n hn hc f hf
