-- Prove2me | solution 1 for RawBlending.UB.lemma_3_d
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:26:46.915295+00:00
-- url     : https://prove2.me/submissions/88677967-4d6b-407b-8727-4dc7f8963402

import Mathlib
import Definitions.Def_RawBlending_UB_Model

noncomputable section

open Filter Set Supermodularity.Monotonicity

namespace RawBlending.UB.Lemma3d

/-! ### Section 1: Basic orthant, Shape, and 2D convex-supermodular helpers -/

private lemma mem_orthant_iff (x : Vec) : x ∈ orthant ↔ 0 ≤ x.1 ∧ 0 ≤ x.2 := by
  simp [orthant, Prod.le_def]

private lemma orthant_convex : Convex ℝ orthant :=
  convex_Ici (0 : Vec)

private lemma shape_add_linear (k1 k2 c : ℝ) (f : Vec → ℝ) (hf : Shape f) :
    Shape (fun w : Vec => k1 * w.1 + k2 * w.2 + c + f w) := by
  obtain ⟨hc, hcont, hsm⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · have hlin : ConvexOn ℝ orthant (fun w : Vec => k1 * w.1 + k2 * w.2 + c) := by
      refine ⟨orthant_convex, fun x _ y _ a b _ _ hab => le_of_eq ?_⟩
      simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
      linear_combination -c * hab
    exact hlin.add hc
  · have : Continuous (fun w : Vec => k1 * w.1 + k2 * w.2 + c) := by fun_prop
    exact this.continuousOn.add hcont
  · intro x hx y hy
    have h := hsm hx hy
    have e1 : (x ⊔ y).1 + (x ⊓ y).1 = x.1 + y.1 := by
      simp only [Prod.fst_sup, Prod.fst_inf]; exact max_add_min x.1 y.1
    have e2 : (x ⊔ y).2 + (x ⊓ y).2 = x.2 + y.2 := by
      simp only [Prod.snd_sup, Prod.snd_inf]; exact max_add_min x.2 y.2
    beta_reduce
    linear_combination h - k1 * e1 - k2 * e2

private lemma shape_add_const (c : ℝ) (f : Vec → ℝ) (hf : Shape f) :
    Shape (fun w : Vec => f w + c) := by
  have h := shape_add_linear 0 0 c f hf
  convert h using 1
  ext w
  ring

private lemma shape_expect {α : Type*} (μ : FinLaw α) (hμ : μ.IsProb)
    (F : α → Vec → ℝ) (hF : ∀ a ∈ μ.supp, Shape (F a)) :
    Shape (fun y => μ.expect (fun a => F a y)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨orthant_convex, fun x hx y hy a b ha hb hab => ?_⟩
    simp only [FinLaw.expect, smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    have hw : 0 ≤ μ.weight i := hμ.1 i hi
    have hci := (hF i hi).1.2 hx hy ha hb hab
    simp only [smul_eq_mul] at hci
    nlinarith
  · simp only [FinLaw.expect]
    exact continuousOn_finsetSum _ fun i hi => continuousOn_const.mul (hF i hi).2.1
  · intro x hx y hy
    simp only [FinLaw.expect]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    have hw : 0 ≤ μ.weight i := hμ.1 i hi
    have hsmi := (hF i hi).2.2 hx hy
    nlinarith

private lemma supermodular_flip_pair {f : Vec → ℝ} (hsm : SupermodularOn f orthant)
    {a1 b1 a2 b2 : ℝ} (ha1 : 0 ≤ a1) (hb1 : 0 ≤ b1) (ha2 : 0 ≤ a2) (hb2 : 0 ≤ b2) :
    f (min a1 b1, max a2 b2) + f (max a1 b1, min a2 b2) ≤ f (a1, a2) + f (b1, b2) := by
  rcases le_total a1 b1 with h1 | h1 <;> rcases le_total a2 b2 with h2 | h2
  · simp only [min_eq_left h1, max_eq_right h1, min_eq_left h2, max_eq_right h2]
    have h := hsm ((mem_orthant_iff (a1, b2)).2 ⟨ha1, hb2⟩) ((mem_orthant_iff (b1, a2)).2 ⟨hb1, ha2⟩)
    have hsup : ((a1, b2) : Vec) ⊔ (b1, a2) = (b1, b2) := by
      ext
      · simp [max_eq_right h1]
      · simp [max_eq_left h2]
    have hinf : ((a1, b2) : Vec) ⊓ (b1, a2) = (a1, a2) := by
      ext
      · simp [min_eq_left h1]
      · simp [min_eq_right h2]
    rw [hsup, hinf] at h
    linarith
  · simp only [min_eq_left h1, max_eq_right h1, min_eq_right h2, max_eq_left h2]
    exact le_rfl
  · simp only [min_eq_right h1, max_eq_left h1, min_eq_left h2, max_eq_right h2]
    linarith
  · simp only [min_eq_right h1, max_eq_left h1, min_eq_right h2, max_eq_left h2]
    have h := hsm ((mem_orthant_iff (b1, a2)).2 ⟨hb1, ha2⟩) ((mem_orthant_iff (a1, b2)).2 ⟨ha1, hb2⟩)
    have hsup : ((b1, a2) : Vec) ⊔ (a1, b2) = (a1, a2) := by
      ext
      · simp [max_eq_right h1]
      · simp [max_eq_left h2]
    have hinf : ((b1, a2) : Vec) ⊓ (a1, b2) = (b1, b2) := by
      ext
      · simp [min_eq_left h1]
      · simp [min_eq_right h2]
    rw [hsup, hinf] at h
    linarith

private lemma rect_sum_le {f : Vec → ℝ} (hc : ConvexOn ℝ orthant f)
    (hsm : SupermodularOn f orthant) {u v wA wB : Vec}
    (hu : u ∈ orthant) (hv : v ∈ orthant) (huv : u ≤ v)
    (hA1 : u.1 ≤ wA.1 ∧ wA.1 ≤ v.1) (hA2 : u.2 ≤ wA.2 ∧ wA.2 ≤ v.2)
    (hsum : wA + wB = u + v) :
    f wA + f wB ≤ f u + f v := by
  have hu' := (mem_orthant_iff u).1 hu
  have hv' := (mem_orthant_iff v).1 hv
  have huv1 : u.1 ≤ v.1 := huv.1
  have huv2 : u.2 ≤ v.2 := huv.2
  have hsum1 : wA.1 + wB.1 = u.1 + v.1 := congrArg Prod.fst hsum
  have hsum2 : wA.2 + wB.2 = u.2 + v.2 := congrArg Prod.snd hsum
  let s : ℝ := if u.1 = v.1 then 0 else (wA.1 - u.1) / (v.1 - u.1)
  let t : ℝ := if u.2 = v.2 then 0 else (wA.2 - u.2) / (v.2 - u.2)
  have hs0 : 0 ≤ s := by
    dsimp only [s]; split_ifs with h
    · exact le_rfl
    · exact div_nonneg (by linarith) (sub_nonneg.2 huv1)
  have hs1 : s ≤ 1 := by
    dsimp only [s]; split_ifs with h
    · exact zero_le_one
    · rw [div_le_one (lt_of_le_of_ne huv1 h |> sub_pos.2)]; linarith
  have ht0 : 0 ≤ t := by
    dsimp only [t]; split_ifs with h
    · exact le_rfl
    · exact div_nonneg (by linarith) (sub_nonneg.2 huv2)
  have ht1 : t ≤ 1 := by
    dsimp only [t]; split_ifs with h
    · exact zero_le_one
    · rw [div_le_one (lt_of_le_of_ne huv2 h |> sub_pos.2)]; linarith
  have hwA1 : wA.1 = (1 - s) * u.1 + s * v.1 := by
    dsimp only [s]; split_ifs with h
    · linarith
    · have hne : v.1 - u.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
      field_simp [hne]; ring
  have hwA2 : wA.2 = (1 - t) * u.2 + t * v.2 := by
    dsimp only [t]; split_ifs with h
    · linarith
    · have hne : v.2 - u.2 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
      field_simp [hne]; ring
  have hwB1 : wB.1 = s * u.1 + (1 - s) * v.1 := by linarith
  have hwB2 : wB.2 = t * u.2 + (1 - t) * v.2 := by linarith
  have hc1_mem : (u.1, v.2) ∈ orthant := (mem_orthant_iff _).2 ⟨hu'.1, hv'.2⟩
  have hc2_mem : (v.1, u.2) ∈ orthant := (mem_orthant_iff _).2 ⟨hv'.1, hu'.2⟩
  have hsm_uv : f (u.1, v.2) + f (v.1, u.2) ≤ f u + f v := by
    have h := hsm hc1_mem hc2_mem
    have hsup : ((u.1, v.2) : Vec) ⊔ (v.1, u.2) = v := by
      ext <;> [simp [max_eq_right huv1]; simp [max_eq_left huv2]]
    have hinf : ((u.1, v.2) : Vec) ⊓ (v.1, u.2) = u := by
      ext <;> [simp [min_eq_left huv1]; simp [min_eq_right huv2]]
    rw [hsup, hinf] at h
    linarith
  rcases le_total s t with hst | hts
  · rcases eq_or_lt_of_le ht0 with ht_zero | ht_pos
    · have hs_zero : s = 0 := le_antisymm (by linarith) hs0
      have : wA = u := by ext <;> simp [hwA1, hwA2, hs_zero, ← ht_zero]
      have : wB = v := by ext <;> simp [hwB1, hwB2, hs_zero, ← ht_zero]
      simp [*]
    · let r := s / t
      have hr0 : 0 ≤ r := div_nonneg hs0 (le_of_lt ht_pos)
      have hr1 : r ≤ 1 := (div_le_one ht_pos).2 hst
      have h1r : 0 ≤ 1 - r := sub_nonneg.2 hr1
      have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht1
      let mA : Vec := (1 - r) • (u.1, v.2) + r • v
      let mB : Vec := (1 - r) • (v.1, u.2) + r • u
      have hmA_mem : mA ∈ orthant := orthant_convex hc1_mem hv h1r hr0 (by ring)
      have hmB_mem : mB ∈ orthant := orthant_convex hc2_mem hu h1r hr0 (by ring)
      have hwA_eq : wA = (1 - t) • u + t • mA := by
        ext
        · simp only [mA, Prod.fst_add, Prod.smul_fst, smul_eq_mul, r]
          rw [hwA1]; field_simp [ne_of_gt ht_pos]; ring
        · simp only [mA, Prod.snd_add, Prod.smul_snd, smul_eq_mul, r]
          rw [hwA2]; field_simp [ne_of_gt ht_pos]; ring
      have hwB_eq : wB = (1 - t) • v + t • mB := by
        ext
        · simp only [mB, Prod.fst_add, Prod.smul_fst, smul_eq_mul, r]
          rw [hwB1]; field_simp [ne_of_gt ht_pos]; ring
        · simp only [mB, Prod.snd_add, Prod.smul_snd, smul_eq_mul, r]
          rw [hwB2]; field_simp [ne_of_gt ht_pos]; ring
      have h1 := hc.2 hu hmA_mem h1t (le_of_lt ht_pos) (by ring)
      have h2 := hc.2 hc1_mem hv h1r hr0 (by ring)
      have h3 := hc.2 hv hmB_mem h1t (le_of_lt ht_pos) (by ring)
      have h4 := hc.2 hc2_mem hu h1r hr0 (by ring)
      rw [← hwA_eq] at h1
      rw [← hwB_eq] at h3
      simp only [smul_eq_mul] at h1 h2 h3 h4
      have ht_r : t * r = s := mul_div_cancel₀ s (ne_of_gt ht_pos)
      have hA_le : f wA ≤ (1 - t) * f u + (t - s) * f (u.1, v.2) + s * f v := by
        calc f wA ≤ (1 - t) * f u + t * f mA := h1
          _ ≤ (1 - t) * f u + t * ((1 - r) * f (u.1, v.2) + r * f v) := by
              have := mul_le_mul_of_nonneg_left h2 (le_of_lt ht_pos); linarith
          _ = (1 - t) * f u + (t - s) * f (u.1, v.2) + s * f v := by
              linear_combination (f v - f (u.1, v.2)) * ht_r
      have hB_le : f wB ≤ (1 - t) * f v + (t - s) * f (v.1, u.2) + s * f u := by
        calc f wB ≤ (1 - t) * f v + t * f mB := h3
          _ ≤ (1 - t) * f v + t * ((1 - r) * f (v.1, u.2) + r * f u) := by
              have := mul_le_mul_of_nonneg_left h4 (le_of_lt ht_pos); linarith
          _ = (1 - t) * f v + (t - s) * f (v.1, u.2) + s * f u := by
              linear_combination (f u - f (v.1, u.2)) * ht_r
      nlinarith
  · rcases eq_or_lt_of_le hs0 with hs_zero | hs_pos
    · have ht_zero : t = 0 := le_antisymm (by linarith) ht0
      have : wA = u := by ext <;> simp [hwA1, hwA2, ← hs_zero, ht_zero]
      have : wB = v := by ext <;> simp [hwB1, hwB2, ← hs_zero, ht_zero]
      simp [*]
    · let r := t / s
      have hr0 : 0 ≤ r := div_nonneg ht0 (le_of_lt hs_pos)
      have hr1 : r ≤ 1 := (div_le_one hs_pos).2 hts
      have h1r : 0 ≤ 1 - r := sub_nonneg.2 hr1
      have h1s : 0 ≤ 1 - s := sub_nonneg.2 hs1
      let mA : Vec := (1 - r) • (v.1, u.2) + r • v
      let mB : Vec := (1 - r) • (u.1, v.2) + r • u
      have hmA_mem : mA ∈ orthant := orthant_convex hc2_mem hv h1r hr0 (by ring)
      have hmB_mem : mB ∈ orthant := orthant_convex hc1_mem hu h1r hr0 (by ring)
      have hwA_eq : wA = (1 - s) • u + s • mA := by
        ext
        · simp only [mA, Prod.fst_add, Prod.smul_fst, smul_eq_mul, r]
          rw [hwA1]; field_simp [ne_of_gt hs_pos]; ring
        · simp only [mA, Prod.snd_add, Prod.smul_snd, smul_eq_mul, r]
          rw [hwA2]; field_simp [ne_of_gt hs_pos]; ring
      have hwB_eq : wB = (1 - s) • v + s • mB := by
        ext
        · simp only [mB, Prod.fst_add, Prod.smul_fst, smul_eq_mul, r]
          rw [hwB1]; field_simp [ne_of_gt hs_pos]; ring
        · simp only [mB, Prod.snd_add, Prod.smul_snd, smul_eq_mul, r]
          rw [hwB2]; field_simp [ne_of_gt hs_pos]; ring
      have h1 := hc.2 hu hmA_mem h1s (le_of_lt hs_pos) (by ring)
      have h2 := hc.2 hc2_mem hv h1r hr0 (by ring)
      have h3 := hc.2 hv hmB_mem h1s (le_of_lt hs_pos) (by ring)
      have h4 := hc.2 hc1_mem hu h1r hr0 (by ring)
      rw [← hwA_eq] at h1
      rw [← hwB_eq] at h3
      simp only [smul_eq_mul] at h1 h2 h3 h4
      have hs_r : s * r = t := mul_div_cancel₀ t (ne_of_gt hs_pos)
      have hA_le : f wA ≤ (1 - s) * f u + (s - t) * f (v.1, u.2) + t * f v := by
        calc f wA ≤ (1 - s) * f u + s * f mA := h1
          _ ≤ (1 - s) * f u + s * ((1 - r) * f (v.1, u.2) + r * f v) := by
              have := mul_le_mul_of_nonneg_left h2 (le_of_lt hs_pos); linarith
          _ = (1 - s) * f u + (s - t) * f (v.1, u.2) + t * f v := by
              linear_combination (f v - f (v.1, u.2)) * hs_r
      have hB_le : f wB ≤ (1 - s) * f v + (s - t) * f (u.1, v.2) + t * f u := by
        calc f wB ≤ (1 - s) * f v + s * f mB := h3
          _ ≤ (1 - s) * f v + s * ((1 - r) * f (u.1, v.2) + r * f u) := by
              have := mul_le_mul_of_nonneg_left h4 (le_of_lt hs_pos); linarith
          _ = (1 - s) * f v + (s - t) * f (u.1, v.2) + t * f u := by
              linear_combination (f u - f (u.1, v.2)) * hs_r
      nlinarith

/-! ### Section 2: Structure of `U` (minimization over `E2`) -/

private lemma E2_self_mem {a1 a2 D R : ℝ} {y : Vec} (hy : y ∈ orthant)
    (hD : 0 ≤ D) (hR : 0 ≤ R) : y ∈ E2 a1 a2 y D R := by
  refine ⟨hy, le_rfl, ?_, ?_⟩ <;> linarith

private lemma E2_subset_orthant {a1 a2 D R : ℝ} {y : Vec} :
    E2 a1 a2 y D R ⊆ orthant := fun _ hw => hw.1

private lemma E2_isCompact {a1 a2 D R : ℝ} {y : Vec} :
    IsCompact (E2 a1 a2 y D R) := by
  have hbox : IsCompact (Set.Icc (0 : ℝ) y.1 ×ˢ Set.Icc (0 : ℝ) y.2) :=
    isCompact_Icc.prod isCompact_Icc
  have hsub : E2 a1 a2 y D R ⊆ Set.Icc (0 : ℝ) y.1 ×ˢ Set.Icc (0 : ℝ) y.2 := by
    intro w hw
    exact ⟨⟨hw.1.1, hw.2.1.1⟩, ⟨hw.1.2, hw.2.1.2⟩⟩
  have hcl : IsClosed (E2 a1 a2 y D R) := by
    have h1 : IsClosed {w : Vec | 0 ≤ w} := isClosed_Ici
    have h2 : IsClosed {w : Vec | w ≤ y} := isClosed_Iic
    have h3 : IsClosed {w : Vec | a1 * y.1 + a2 * y.2 - D ≤ a1 * w.1 + a2 * w.2} :=
      isClosed_le continuous_const (by fun_prop)
    have h4 : IsClosed {w : Vec | y.1 + y.2 - R ≤ w.1 + w.2} :=
      isClosed_le continuous_const (by fun_prop)
    simpa [E2, Set.ofPred_and] using h1.inter (h2.inter (h3.inter h4))
  exact hbox.of_isClosed_subset hcl hsub

private lemma U_attained {f : Vec → ℝ} (hcont : ContinuousOn f orthant)
    (a1 a2 : ℝ) {D R : ℝ} (hD : 0 ≤ D) (hR : 0 ≤ R) {y : Vec} (hy : y ∈ orthant) :
    ∃ w ∈ E2 a1 a2 y D R,
      sInf (f '' E2 a1 a2 y D R) = f w ∧ ∀ w' ∈ E2 a1 a2 y D R, f w ≤ f w' := by
  have hne : (E2 a1 a2 y D R).Nonempty := ⟨y, E2_self_mem hy hD hR⟩
  obtain ⟨w, hw, hmin⟩ := E2_isCompact.exists_isMinOn hne (hcont.mono E2_subset_orthant)
  have hleast : IsLeast (f '' E2 a1 a2 y D R) (f w) := by
    refine ⟨⟨w, hw, rfl⟩, ?_⟩
    rintro _ ⟨w', hw', rfl⟩
    exact hmin hw'
  exact ⟨w, hw, hleast.csInf_eq, fun w' hw' => hmin hw'⟩

private lemma U_convexOn {f : Vec → ℝ} (hc : ConvexOn ℝ orthant f)
    (hcont : ContinuousOn f orthant) {a1 a2 D R : ℝ} (hD : 0 ≤ D) (hR : 0 ≤ R) :
    ConvexOn ℝ orthant (fun y => sInf (f '' E2 a1 a2 y D R)) := by
  refine ⟨orthant_convex, fun y1 hy1 y2 hy2 a b ha hb hab => ?_⟩
  obtain ⟨w1, hw1, hU1, _⟩ := U_attained hcont a1 a2 hD hR hy1
  obtain ⟨w2, hw2, hU2, _⟩ := U_attained hcont a1 a2 hD hR hy2
  have hy_mem : a • y1 + b • y2 ∈ orthant := orthant_convex hy1 hy2 ha hb hab
  obtain ⟨w, _, hU, hmin⟩ := U_attained hcont a1 a2 hD hR hy_mem
  have hw_mem : a • w1 + b • w2 ∈ E2 a1 a2 (a • y1 + b • y2) D R := by
    refine ⟨orthant_convex hw1.1 hw2.1 ha hb hab, ?_, ?_, ?_⟩
    · constructor
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        linarith [mul_le_mul_of_nonneg_left hw1.2.1.1 ha, mul_le_mul_of_nonneg_left hw2.2.1.1 hb]
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        linarith [mul_le_mul_of_nonneg_left hw1.2.1.2 ha, mul_le_mul_of_nonneg_left hw2.2.1.2 hb]
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      have h1 := mul_le_mul_of_nonneg_left hw1.2.2.1 ha
      have h2 := mul_le_mul_of_nonneg_left hw2.2.2.1 hb
      have hD_split : D = a * D + b * D := by linear_combination -D * hab
      linarith
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      have h1 := mul_le_mul_of_nonneg_left hw1.2.2.2 ha
      have h2 := mul_le_mul_of_nonneg_left hw2.2.2.2 hb
      have hR_split : R = a * R + b * R := by linear_combination -R * hab
      linarith
  have hconv := hc.2 hw1.1 hw2.1 ha hb hab
  simp only [smul_eq_mul] at hconv ⊢
  rw [hU, hU1, hU2]
  linarith [hmin _ hw_mem]

private lemma abs_max_zero_sub_max_zero_le (a b : ℝ) :
    |max a 0 - max b 0| ≤ |a - b| := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · simp [max_eq_right ha, max_eq_right hb]
  · simp only [max_eq_right ha, max_eq_left hb, zero_sub, abs_neg]
    rw [abs_of_nonneg hb, abs_of_nonpos (by linarith)]; linarith
  · simp only [max_eq_left ha, max_eq_right hb, sub_zero]
    rw [abs_of_nonneg ha, abs_of_nonneg (by linarith)]; linarith
  · simp [max_eq_left ha, max_eq_left hb]

private lemma proj_E2 {a1 a2 D R : ℝ} (ha1 : 0 < a1) (ha2 : 0 < a2)
    {y y' w : Vec} (hy' : y' ∈ orthant) (hw : w ∈ E2 a1 a2 y D R) :
    let w' : Vec := (max (y'.1 - (y.1 - w.1)) 0, max (y'.2 - (y.2 - w.2)) 0)
    w' ∈ E2 a1 a2 y' D R ∧ dist w' w ≤ dist y' y := by
  intro w'
  have hy'_nonneg := (mem_orthant_iff y').1 hy'
  have hw0 := (mem_orthant_iff w).1 hw.1
  have hwy := hw.2.1
  have h1 : y'.1 - w'.1 ≤ y.1 - w.1 := by
    dsimp only [w']
    have := le_max_left (y'.1 - (y.1 - w.1)) 0
    linarith
  have h2 : y'.2 - w'.2 ≤ y.2 - w.2 := by
    dsimp only [w']
    have := le_max_left (y'.2 - (y.2 - w.2)) 0
    linarith
  refine ⟨⟨⟨le_max_right _ _, le_max_right _ _⟩, ⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact max_le (by linarith [hwy.1]) hy'_nonneg.1
  · exact max_le (by linarith [hwy.2]) hy'_nonneg.2
  · nlinarith [hw.2.2.1]
  · linarith [hw.2.2.2]
  · rw [Prod.dist_eq, Prod.dist_eq]
    refine max_le_max ?_ ?_
    · rw [Real.dist_eq, Real.dist_eq]
      have hw1_eq : w.1 = max w.1 0 := (max_eq_left hw0.1).symm
      have heq : y'.1 - (y.1 - w.1) - w.1 = y'.1 - y.1 := by ring
      have hle := abs_max_zero_sub_max_zero_le (y'.1 - (y.1 - w.1)) w.1
      rw [heq] at hle
      dsimp only [w']
      rwa [← hw1_eq] at hle
    · rw [Real.dist_eq, Real.dist_eq]
      have hw2_eq : w.2 = max w.2 0 := (max_eq_left hw0.2).symm
      have heq : y'.2 - (y.2 - w.2) - w.2 = y'.2 - y.2 := by ring
      have hle := abs_max_zero_sub_max_zero_le (y'.2 - (y.2 - w.2)) w.2
      rw [heq] at hle
      dsimp only [w']
      rwa [← hw2_eq] at hle

private lemma U_continuousOn {f : Vec → ℝ} (hcont : ContinuousOn f orthant)
    {a1 a2 D R : ℝ} (ha1 : 0 < a1) (ha2 : 0 < a2) (hD : 0 ≤ D) (hR : 0 ≤ R) :
    ContinuousOn (fun y => sInf (f '' E2 a1 a2 y D R)) orthant := by
  intro y0 hy0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  let K : Set Vec := Set.Icc (0 : ℝ) (y0.1 + 1) ×ˢ Set.Icc (0 : ℝ) (y0.2 + 1)
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hK_sub : K ⊆ orthant := fun u hu => (mem_orthant_iff u).2 ⟨hu.1.1, hu.2.1⟩
  have huc : UniformContinuousOn f K :=
    hK_compact.uniformContinuousOn_of_continuous (hcont.mono hK_sub)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ0, hδ0, hδ0_prop⟩ := huc ε hε
  refine ⟨min 1 δ0, lt_min zero_lt_one hδ0, fun y hy hdist => ?_⟩
  have hd1 : dist y y0 < 1 := lt_of_lt_of_le hdist (min_le_left _ _)
  have hd0 : dist y y0 < δ0 := lt_of_lt_of_le hdist (min_le_right _ _)
  have hy_le : y.1 ≤ y0.1 + 1 ∧ y.2 ≤ y0.2 + 1 := by
    rw [Prod.dist_eq] at hd1
    have h1 : |y.1 - y0.1| < 1 := by simpa [Real.dist_eq] using lt_of_le_of_lt (le_max_left _ _) hd1
    have h2 : |y.2 - y0.2| < 1 := by simpa [Real.dist_eq] using lt_of_le_of_lt (le_max_right _ _) hd1
    exact ⟨by linarith [(abs_lt.1 h1).2], by linarith [(abs_lt.1 h2).2]⟩
  obtain ⟨w0, hw0, hU0, hmin0⟩ := U_attained hcont a1 a2 hD hR hy0
  obtain ⟨w, hw, hU, hmin⟩ := U_attained hcont a1 a2 hD hR hy
  have hw0_K : w0 ∈ K := ⟨⟨hw0.1.1, by linarith [hw0.2.1.1]⟩, ⟨hw0.1.2, by linarith [hw0.2.1.2]⟩⟩
  have hw_K : w ∈ K := ⟨⟨hw.1.1, by linarith [hw.2.1.1]⟩, ⟨hw.1.2, by linarith [hw.2.1.2]⟩⟩
  obtain ⟨hw0'_E2, hw0'_dist⟩ := proj_E2 ha1 ha2 hy hw0
  obtain ⟨hw'_E2, hw'_dist⟩ := proj_E2 ha1 ha2 hy0 hw
  set w0' : Vec := (max (y.1 - (y0.1 - w0.1)) 0, max (y.2 - (y0.2 - w0.2)) 0)
  set w' : Vec := (max (y0.1 - (y.1 - w.1)) 0, max (y0.2 - (y.2 - w.2)) 0)
  have hw0'_K : w0' ∈ K :=
    ⟨⟨hw0'_E2.1.1, by linarith [hw0'_E2.2.1.1]⟩, ⟨hw0'_E2.1.2, by linarith [hw0'_E2.2.1.2]⟩⟩
  have hw'_K : w' ∈ K :=
    ⟨⟨hw'_E2.1.1, by linarith [hw'_E2.2.1.1]⟩, ⟨hw'_E2.1.2, by linarith [hw'_E2.2.1.2]⟩⟩
  have hdiff1 : dist (f w0') (f w0) < ε :=
    hδ0_prop w0' hw0'_K w0 hw0_K (lt_of_le_of_lt hw0'_dist hd0)
  have hdiff2 : dist (f w') (f w) < ε :=
    hδ0_prop w' hw'_K w hw_K (lt_of_le_of_lt hw'_dist (by rwa [dist_comm]))
  rw [Real.dist_eq] at hdiff1 hdiff2 ⊢
  rw [hU, hU0]
  have hle1 : f w ≤ f w0' := hmin w0' hw0'_E2
  have hle2 : f w0 ≤ f w' := hmin0 w' hw'_E2
  rw [abs_lt]
  exact ⟨by linarith [(abs_lt.1 hdiff2).2], by linarith [(abs_lt.1 hdiff1).2]⟩

/-! #### Master Lemma for supermodularity of `U` -/

private lemma E2_pair_le {f : Vec → ℝ} (hc : ConvexOn ℝ orthant f)
    (hsm : SupermodularOn f orthant) {a1 a2 D R x1 x1' x2 x2' : ℝ}
    (ha1 : 0 < a1) (ha12 : a1 < a2)
    (hx1 : x1 ≤ x1') (hx2 : x2 ≤ x2')
    {wL wH : Vec}
    (hwL : wL ∈ E2 a1 a2 (x1, x2) D R) (hwH : wH ∈ E2 a1 a2 (x1', x2') D R)
    (hord1 : wL.1 ≤ wH.1) (hord2 : wL.2 ≤ wH.2) :
    ∃ wA ∈ E2 a1 a2 (x1, x2') D R, ∃ wB ∈ E2 a1 a2 (x1', x2) D R,
      f wA + f wB ≤ f wL + f wH := by
  have ha2 : 0 < a2 := by linarith
  have hda : 0 < a2 - a1 := sub_pos.2 ha12
  set zL1 := x1 - wL.1
  set zL2 := x2 - wL.2
  set zH1 := x1' - wH.1
  set zH2 := x2' - wH.2
  have hzL1 : 0 ≤ zL1 := sub_nonneg.2 hwL.2.1.1
  have hzL2 : 0 ≤ zL2 := sub_nonneg.2 hwL.2.1.2
  have hzH1 : 0 ≤ zH1 := sub_nonneg.2 hwH.2.1.1
  have hzH2 : 0 ≤ zH2 := sub_nonneg.2 hwH.2.1.2
  have hDL : a1 * zL1 + a2 * zL2 ≤ D := by linarith [hwL.2.2.1]
  have hDH : a1 * zH1 + a2 * zH2 ≤ D := by linarith [hwH.2.2.1]
  have hRL : zL1 + zL2 ≤ R := by linarith [hwL.2.2.2]
  have hRH : zH1 + zH2 ≤ R := by linarith [hwH.2.2.2]
  set M1 := min (wH.1 - wL.1) zL1
  set M2 := min (wH.2 - wL.2) zL2
  have hM1 : 0 ≤ M1 := le_min (sub_nonneg.2 hord1) hzL1
  have hM2 : 0 ≤ M2 := le_min (sub_nonneg.2 hord2) hzL2
  have hzL1_M1 : zL1 - M1 ≤ zH1 := by
    have : M1 = wH.1 - wL.1 ∨ M1 = zL1 := min_choice _ _
    rcases this with h | h <;> linarith
  have hzL2_M2 : zL2 - M2 ≤ zH2 := by
    have : M2 = wH.2 - wL.2 ∨ M2 = zL2 := min_choice _ _
    rcases this with h | h <;> linarith
  set AD := a1 * zL1 + a2 * zH2 - D
  set BD := D - (a1 * zH1 + a2 * zL2)
  set AR := zL1 + zH2 - R
  set BR := R - (zH1 + zL2)
  have hAD_BD : AD ≤ BD := by linarith
  have hAR_BR : AR ≤ BR := by linarith
  have hAD_M1 : AD ≤ a1 * M1 := by
    have := mul_le_mul_of_nonneg_left hzL1_M1 (le_of_lt ha1); linarith
  have hAR_M1 : AR ≤ M1 := by linarith
  have hM2_BD : -a2 * M2 ≤ BD := by
    have := mul_le_mul_of_nonneg_left hzL2_M2 (le_of_lt ha2); linarith
  have hM2_BR : -M2 ≤ BR := by linarith
  -- Choose v and u via Fourier-Motzkin
  set v := max (max AR (-M2)) (max (AD / a2) (AD / a1))
  have hv_BR : v ≤ BR := by
    refine max_le (max_le hAR_BR hM2_BR) (max_le ?_ ?_)
    · rw [div_le_iff₀ ha2]; linarith [mul_le_mul_of_nonneg_left hRH (le_of_lt ha2)]
    · rw [div_le_iff₀ ha1]; linarith [mul_le_mul_of_nonneg_left hRL (le_of_lt ha1)]
  have hv_M1 : v ≤ M1 := by
    refine max_le (max_le hAR_M1 (by linarith)) (max_le ?_ ?_)
    · rw [div_le_iff₀ ha2]
      have := mul_le_mul_of_nonneg_right (le_of_lt ha12) hM1; linarith
    · rw [div_le_iff₀ ha1]; linarith
  have hv_U3 : v ≤ (BD + (a2 - a1) * M1) / a2 := by
    rw [le_div_iff₀ ha2]
    have hdaM1 : 0 ≤ (a2 - a1) * M1 := mul_nonneg (le_of_lt hda) hM1
    have h1 : AR * a2 ≤ BD + (a2 - a1) * M1 := by
      have hm := mul_le_mul_of_nonneg_left hzL1_M1 (le_of_lt hda)
      have hr := mul_le_mul_of_nonneg_left hRH (le_of_lt ha2)
      linarith
    have h2 : (-M2) * a2 ≤ BD + (a2 - a1) * M1 := by linarith
    have h3 : (AD / a2) * a2 ≤ BD + (a2 - a1) * M1 := by
      rw [div_mul_cancel₀ _ (ne_of_gt ha2)]; linarith
    have h4 : (AD / a1) * a2 ≤ BD + (a2 - a1) * M1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ ha1]
      have ha := mul_le_mul_of_nonneg_left hAD_M1 (le_of_lt hda)
      have hb := mul_le_mul_of_nonneg_left hAD_BD (le_of_lt ha1)
      linarith
    have hv_le : v * a2 ≤ BD + (a2 - a1) * M1 := by
      dsimp only [v]
      rcases max_choice (max AR (-M2)) (max (AD / a2) (AD / a1)) with h | h <;> rw [h]
      · rcases max_choice AR (-M2) with h' | h' <;> rw [h'] <;> linarith
      · rcases max_choice (AD / a2) (AD / a1) with h' | h' <;> rw [h'] <;> linarith
    exact hv_le
  have hv_U4 : v ≤ (BD + (a2 - a1) * M2) / a1 := by
    rw [le_div_iff₀ ha1]
    have hdaM2 : 0 ≤ (a2 - a1) * M2 := mul_nonneg (le_of_lt hda) hM2
    have h1 : AR * a1 ≤ BD + (a2 - a1) * M2 := by
      have hm := mul_le_mul_of_nonneg_left hzL2_M2 (le_of_lt hda)
      have hr := mul_le_mul_of_nonneg_left hRL (le_of_lt ha1)
      linarith
    have h2 : (-M2) * a1 ≤ BD + (a2 - a1) * M2 := by linarith
    have h3 : (AD / a2) * a1 ≤ BD + (a2 - a1) * M2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ ha2]
      have ha := mul_le_mul_of_nonneg_left hM2_BD (le_of_lt hda)
      have hb := mul_le_mul_of_nonneg_left hAD_BD (le_of_lt ha1)
      linarith
    have h4 : (AD / a1) * a1 ≤ BD + (a2 - a1) * M2 := by
      rw [div_mul_cancel₀ _ (ne_of_gt ha1)]; linarith
    dsimp only [v]
    rcases max_choice (max AR (-M2)) (max (AD / a2) (AD / a1)) with h | h <;> rw [h]
    · rcases max_choice AR (-M2) with h' | h' <;> rw [h'] <;> linarith
    · rcases max_choice (AD / a2) (AD / a1) with h' | h' <;> rw [h'] <;> linarith
  have hv_AR : AR ≤ v := le_trans (le_max_left _ _) (le_max_left _ _)
  have hv_M2 : -M2 ≤ v := le_trans (le_max_right _ _) (le_max_left _ _)
  have hv_AD2 : AD / a2 ≤ v := le_trans (le_max_left _ _) (le_max_right _ _)
  have hv_AD1 : AD / a1 ≤ v := le_trans (le_max_right _ _) (le_max_right _ _)
  set u := max AD (max (a2 * v - (a2 - a1) * M1) (a1 * v - (a2 - a1) * M2))
  have hu_AD : AD ≤ u := le_max_left _ _
  have hu_L1 : a2 * v - (a2 - a1) * M1 ≤ u := le_trans (le_max_left _ _) (le_max_right _ _)
  have hu_L2 : a1 * v - (a2 - a1) * M2 ≤ u := le_trans (le_max_right _ _) (le_max_right _ _)
  have hu_BD : u ≤ BD := by
    refine max_le hAD_BD (max_le ?_ ?_)
    · have := (le_div_iff₀ ha2).1 hv_U3; linarith
    · have := (le_div_iff₀ ha1).1 hv_U4; linarith
  have hu_a2v : u ≤ a2 * v := by
    refine max_le ?_ (max_le ?_ ?_)
    · have := (div_le_iff₀ ha2).1 hv_AD2; linarith
    · have := mul_nonneg (le_of_lt hda) hM1; linarith
    · have := mul_le_mul_of_nonneg_left hv_M2 (le_of_lt hda); linarith
  have hu_a1v : u ≤ a1 * v := by
    refine max_le ?_ (max_le ?_ ?_)
    · have := (div_le_iff₀ ha1).1 hv_AD1; linarith
    · have := mul_le_mul_of_nonneg_left hv_M1 (le_of_lt hda); linarith
    · have := mul_nonneg (le_of_lt hda) hM2; linarith
  set p1 := (a2 * v - u) / (a2 - a1)
  set p2 := (a1 * v - u) / (a2 - a1)
  have hp1_nonneg : 0 ≤ p1 := div_nonneg (by linarith) (le_of_lt hda)
  have hp2_nonneg : 0 ≤ p2 := div_nonneg (by linarith) (le_of_lt hda)
  have hp1_le : p1 ≤ M1 := by rw [div_le_iff₀ hda]; linarith
  have hp2_le : p2 ≤ M2 := by rw [div_le_iff₀ hda]; linarith
  have hp_D : a1 * p1 - a2 * p2 = u := by
    dsimp only [p1, p2]; field_simp [ne_of_gt hda]; ring
  have hp_R : p1 - p2 = v := by
    dsimp only [p1, p2]; field_simp [ne_of_gt hda]; ring
  let wA : Vec := (wL.1 + p1, wH.2 - p2)
  let wB : Vec := (wH.1 - p1, wL.2 + p2)
  have hp1_dw : p1 ≤ wH.1 - wL.1 := le_trans hp1_le (min_le_left _ _)
  have hp1_zL : p1 ≤ zL1 := le_trans hp1_le (min_le_right _ _)
  have hp2_dw : p2 ≤ wH.2 - wL.2 := le_trans hp2_le (min_le_left _ _)
  have hp2_zL : p2 ≤ zL2 := le_trans hp2_le (min_le_right _ _)
  have hwA_mem : wA ∈ E2 a1 a2 (x1, x2') D R := by
    refine ⟨⟨by linarith [hwL.1.1], by linarith [hwL.1.2]⟩,
      ⟨by linarith, by linarith [hwH.2.1.2]⟩, ?_, ?_⟩
    · dsimp only [wA]; linarith [hp_D, hu_AD]
    · dsimp only [wA]; linarith [hp_R, hv_AR]
  have hwB_mem : wB ∈ E2 a1 a2 (x1', x2) D R := by
    refine ⟨⟨by linarith [hwL.1.1], by linarith [hwL.1.2]⟩,
      ⟨by linarith [hwH.2.1.1], by linarith⟩, ?_, ?_⟩
    · dsimp only [wB]; linarith [hp_D, hu_BD]
    · dsimp only [wB]; linarith [hp_R, hv_BR]
  refine ⟨wA, hwA_mem, wB, hwB_mem, ?_⟩
  exact rect_sum_le hc hsm hwL.1 hwH.1 ⟨hord1, hord2⟩
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    (by ext <;> (simp only [wA, wB, Prod.fst_add, Prod.snd_add]; ring))

private lemma E2_pair_ge {f : Vec → ℝ} (hsm : SupermodularOn f orthant)
    {a1 a2 D R x1 x1' x2 x2' : ℝ}
    (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hx1 : x1 ≤ x1') (hx2 : x2 ≤ x2')
    {wL wH : Vec}
    (hwL : wL ∈ E2 a1 a2 (x1, x2) D R) (hwH : wH ∈ E2 a1 a2 (x1', x2') D R)
    (hord1 : wH.1 ≤ wL.1) (hord2 : wH.2 ≤ wL.2) :
    ∃ wA ∈ E2 a1 a2 (x1, x2') D R, ∃ wB ∈ E2 a1 a2 (x1', x2) D R,
      f wA + f wB ≤ f wL + f wH := by
  let wA : Vec := (wL.1, wH.2)
  let wB : Vec := (wH.1, wL.2)
  have hwA_mem : wA ∈ E2 a1 a2 (x1, x2') D R := by
    refine ⟨⟨hwL.1.1, hwH.1.2⟩, ⟨hwL.2.1.1, hwH.2.1.2⟩, ?_, ?_⟩
    · dsimp only [wA]; nlinarith [hwH.2.2.1]
    · dsimp only [wA]; linarith [hwH.2.2.2]
  have hwB_mem : wB ∈ E2 a1 a2 (x1', x2) D R := by
    refine ⟨⟨hwH.1.1, hwL.1.2⟩, ⟨hwH.2.1.1, hwL.2.1.2⟩, ?_, ?_⟩
    · dsimp only [wB]; nlinarith [hwH.2.2.1]
    · dsimp only [wB]; linarith [hwH.2.2.2]
  refine ⟨wA, hwA_mem, wB, hwB_mem, ?_⟩
  have h := hsm hwA_mem.1 hwB_mem.1
  have hsup : wA ⊔ wB = wL := by
    ext <;> [simp [wA, wB, max_eq_left hord1]; simp [wA, wB, max_eq_right hord2]]
  have hinf : wA ⊓ wB = wH := by
    ext <;> [simp [wA, wB, min_eq_right hord1]; simp [wA, wB, min_eq_left hord2]]
  rw [hsup, hinf] at h
  exact h

private lemma E2_pair_incomp3 {f : Vec → ℝ} (hc : ConvexOn ℝ orthant f)
    {a1 a2 D R x1 x1' x2 x2' : ℝ}
    (ha1 : 0 < a1) (ha12 : a1 < a2)
    (hx1 : x1 ≤ x1') (hx2 : x2 ≤ x2')
    {wL wH : Vec}
    (hwL : wL ∈ E2 a1 a2 (x1, x2) D R) (hwH : wH ∈ E2 a1 a2 (x1', x2') D R)
    (h1 : wH.1 < wL.1) (h2 : wL.2 < wH.2) :
    ∃ wA ∈ E2 a1 a2 (x1, x2') D R, ∃ wB ∈ E2 a1 a2 (x1', x2) D R,
      f wA + f wB ≤ f wL + f wH := by
  have ha2 : 0 < a2 := by linarith
  set c1 := wL.1 - wH.1
  set c2 := wH.2 - wL.2
  have hc1 : 0 < c1 := sub_pos.2 h1
  have hc2 : 0 < c2 := sub_pos.2 h2
  set Δ1 := x1' - x1
  set Δ2 := x2' - x2
  have hΔ1 : 0 ≤ Δ1 := sub_nonneg.2 hx1
  have hΔ2 : 0 ≤ Δ2 := sub_nonneg.2 hx2
  set zL1 := x1 - wL.1
  set zL2 := x2 - wL.2
  set zH1 := x1' - wH.1
  set zH2 := x2' - wH.2
  have hzL1 : 0 ≤ zL1 := sub_nonneg.2 hwL.2.1.1
  have hzL2 : 0 ≤ zL2 := sub_nonneg.2 hwL.2.1.2
  have hzH1 : 0 ≤ zH1 := sub_nonneg.2 hwH.2.1.1
  have hzH2 : 0 ≤ zH2 := sub_nonneg.2 hwH.2.1.2
  have hDL : a1 * zL1 + a2 * zL2 ≤ D := by linarith [hwL.2.2.1]
  have hDH : a1 * zH1 + a2 * zH2 ≤ D := by linarith [hwH.2.2.1]
  have hRL : zL1 + zL2 ≤ R := by linarith [hwL.2.2.2]
  have hRH : zH1 + zH2 ≤ R := by linarith [hwH.2.2.2]
  set Smax := min 1 (zL2 / c2)
  have hSmax0 : 0 ≤ Smax := le_min zero_le_one (div_nonneg hzL2 (le_of_lt hc2))
  have hSmax1 : Smax ≤ 1 := min_le_left _ _
  have hSmax_c2 : Smax * c2 ≤ zL2 := by
    have := (le_div_iff₀ hc2).1 (min_le_right 1 (zL2 / c2))
    linarith
  -- Endpoint feasibility at Smax for zB: zB2(Smax) ≤ zH2
  have hzB2_Smax : zL2 - Smax * c2 ≤ zH2 := by
    dsimp only [Smax]
    rcases min_choice 1 (zL2 / c2) with h | h
    · rw [h]; linarith
    · rw [h, div_mul_cancel₀ _ (ne_of_gt hc2)]; linarith
  have hzB1_Smax : zL1 + Δ1 + Smax * c1 ≤ zH1 := by
    have : Smax * c1 ≤ c1 := mul_le_of_le_one_left (le_of_lt hc1) hSmax1
    linarith
  have hDB_Smax : a1 * (zL1 + Δ1 + Smax * c1) + a2 * (zL2 - Smax * c2) ≤ D := by
    have := mul_le_mul_of_nonneg_left hzB1_Smax (le_of_lt ha1)
    have := mul_le_mul_of_nonneg_left hzB2_Smax (le_of_lt ha2)
    linarith
  have hRB_Smax : (zL1 + Δ1 + Smax * c1) + (zL2 - Smax * c2) ≤ R := by linarith
  -- Construct s ∈ [0, Smax]
  suffices ∃ s : ℝ, 0 ≤ s ∧ s ≤ Smax ∧
      a1 * (zH1 - Δ1 - s * c1) + a2 * (zH2 + s * c2) ≤ D ∧
      (zH1 - Δ1 - s * c1) + (zH2 + s * c2) ≤ R ∧
      a1 * (zL1 + Δ1 + s * c1) + a2 * (zL2 - s * c2) ≤ D ∧
      (zL1 + Δ1 + s * c1) + (zL2 - s * c2) ≤ R by
    obtain ⟨s, hs0, hsM, hDA, hRA, hDB, hRB⟩ := this
    have hs1 : s ≤ 1 := le_trans hsM hSmax1
    have h1s : 0 ≤ 1 - s := sub_nonneg.2 hs1
    let wA : Vec := s • wL + (1 - s) • wH
    let wB : Vec := (1 - s) • wL + s • wH
    have hwA_mem : wA ∈ E2 a1 a2 (x1, x2') D R := by
      refine ⟨orthant_convex hwL.1 hwH.1 hs0 h1s (by ring), ⟨?_, ?_⟩, ?_, ?_⟩
      · simp only [wA, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        have := mul_le_mul_of_nonneg_left hwL.2.1.1 hs0
        have := mul_le_mul_of_nonneg_left (show wH.1 ≤ x1 by linarith) h1s
        linarith
      · simp only [wA, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        have := mul_le_mul_of_nonneg_left (show wL.2 ≤ x2' by linarith [hwL.2.1.2]) hs0
        have := mul_le_mul_of_nonneg_left hwH.2.1.2 h1s
        linarith
      · simp only [wA, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        have e1 : x1 - (s * wL.1 + (1 - s) * wH.1) = zH1 - Δ1 - s * c1 := by
          dsimp only [zH1, Δ1, c1]; ring
        have e2 : x2' - (s * wL.2 + (1 - s) * wH.2) = zH2 + s * c2 := by
          dsimp only [zH2, c2]; ring
        linarith [hDA, e1, e2]
      · simp only [wA, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        have e1 : x1 - (s * wL.1 + (1 - s) * wH.1) = zH1 - Δ1 - s * c1 := by
          dsimp only [zH1, Δ1, c1]; ring
        have e2 : x2' - (s * wL.2 + (1 - s) * wH.2) = zH2 + s * c2 := by
          dsimp only [zH2, c2]; ring
        linarith [hRA, e1, e2]
    have hwB_mem : wB ∈ E2 a1 a2 (x1', x2) D R := by
      refine ⟨orthant_convex hwL.1 hwH.1 h1s hs0 (by ring), ⟨?_, ?_⟩, ?_, ?_⟩
      · simp only [wB, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        have := mul_le_mul_of_nonneg_left (show wL.1 ≤ x1' by linarith [hwL.2.1.1]) h1s
        have := mul_le_mul_of_nonneg_left hwH.2.1.1 hs0
        linarith
      · simp only [wB, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        have : s * c2 ≤ zL2 := le_trans (mul_le_mul_of_nonneg_right hsM (le_of_lt hc2)) hSmax_c2
        linarith
      · simp only [wB, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        have e1 : x1' - ((1 - s) * wL.1 + s * wH.1) = zL1 + Δ1 + s * c1 := by
          dsimp only [zL1, Δ1, c1]; ring
        have e2 : x2 - ((1 - s) * wL.2 + s * wH.2) = zL2 - s * c2 := by
          dsimp only [zL2, c2]; ring
        linarith [hDB, e1, e2]
      · simp only [wB, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        have e1 : x1' - ((1 - s) * wL.1 + s * wH.1) = zL1 + Δ1 + s * c1 := by
          dsimp only [zL1, Δ1, c1]; ring
        have e2 : x2 - ((1 - s) * wL.2 + s * wH.2) = zL2 - s * c2 := by
          dsimp only [zL2, c2]; ring
        linarith [hRB, e1, e2]
    refine ⟨wA, hwA_mem, wB, hwB_mem, ?_⟩
    have hcA := hc.2 hwL.1 hwH.1 hs0 h1s (by ring)
    have hcB := hc.2 hwL.1 hwH.1 h1s hs0 (by ring)
    simp only [smul_eq_mul] at hcA hcB
    linarith
  -- Split into 3 slope regimes for s
  have ha1Δ1 : 0 ≤ a1 * Δ1 := mul_nonneg (le_of_lt ha1) hΔ1
  by_cases hDslope : a2 * c2 ≤ a1 * c1
  · -- Regime 3a: take s = 0
    have hRslope : c2 ≤ c1 := by
      have : a1 * c2 < a2 * c2 := mul_lt_mul_of_pos_right ha12 hc2
      exact le_of_lt ((mul_lt_mul_iff_right₀ ha1).1 (lt_of_lt_of_le this hDslope))
    have hDB0 : a1 * (zL1 + Δ1 + 0 * c1) + a2 * (zL2 - 0 * c2) ≤ D := by
      have := mul_le_mul_of_nonneg_left (sub_nonneg.2 hDslope) hSmax0
      linarith [hDB_Smax]
    have hRB0 : (zL1 + Δ1 + 0 * c1) + (zL2 - 0 * c2) ≤ R := by
      have := mul_le_mul_of_nonneg_left (sub_nonneg.2 hRslope) hSmax0
      linarith [hRB_Smax]
    exact ⟨0, le_rfl, hSmax0, by linarith, by linarith, hDB0, hRB0⟩
  · push Not at hDslope
    have hDpos : 0 < a2 * c2 - a1 * c1 := sub_pos.2 hDslope
    by_cases hRslope : c2 ≤ c1
    · -- Regime 3b: take s = max 0 ((DL + a1*Δ1 - D) / (a2*c2 - a1*c1))
      set sD := (a1 * zL1 + a2 * zL2 + a1 * Δ1 - D) / (a2 * c2 - a1 * c1)
      set s := max 0 sD
      have hs0 : 0 ≤ s := le_max_left _ _
      have hsM : s ≤ Smax := max_le hSmax0 ((div_le_iff₀ hDpos).2 (by linarith [hDB_Smax]))
      have hDB : a1 * (zL1 + Δ1 + s * c1) + a2 * (zL2 - s * c2) ≤ D := by
        have := (div_le_iff₀ hDpos).1 (le_max_right 0 sD)
        linarith
      have hDA : a1 * (zH1 - Δ1 - s * c1) + a2 * (zH2 + s * c2) ≤ D := by
        dsimp only [s]
        rcases max_choice 0 sD with h | h
        · rw [h]; linarith
        · rw [h]
          have hmul : sD * (a2 * c2 - a1 * c1) = a1 * zL1 + a2 * zL2 + a1 * Δ1 - D :=
            div_mul_cancel₀ _ (ne_of_gt hDpos)
          linarith
      have hRA : (zH1 - Δ1 - s * c1) + (zH2 + s * c2) ≤ R := by
        have := mul_le_mul_of_nonneg_left (sub_nonneg.2 hRslope) hs0; linarith
      have hRB : (zL1 + Δ1 + s * c1) + (zL2 - s * c2) ≤ R := by
        have := mul_le_mul_of_nonneg_left (sub_nonneg.2 hRslope) (sub_nonneg.2 hsM)
        linarith [hRB_Smax]
      exact ⟨s, hs0, hsM, hDA, hRA, hDB, hRB⟩
    · -- Regime 3c: c1 < c2 and a1*c1 < a2*c2
      push Not at hRslope
      have hRpos : 0 < c2 - c1 := sub_pos.2 hRslope
      set sD := (a1 * zL1 + a2 * zL2 + a1 * Δ1 - D) / (a2 * c2 - a1 * c1)
      set sR := (zL1 + zL2 + Δ1 - R) / (c2 - c1)
      set s := max 0 (max sD sR)
      have hs0 : 0 ≤ s := le_max_left _ _
      have hsM : s ≤ Smax := max_le hSmax0 (max_le
        ((div_le_iff₀ hDpos).2 (by linarith [hDB_Smax]))
        ((div_le_iff₀ hRpos).2 (by linarith [hRB_Smax])))
      have hsD : sD ≤ s := le_trans (le_max_left _ _) (le_max_right _ _)
      have hsR : sR ≤ s := le_trans (le_max_right _ _) (le_max_right _ _)
      have hDB : a1 * (zL1 + Δ1 + s * c1) + a2 * (zL2 - s * c2) ≤ D := by
        have := (div_le_iff₀ hDpos).1 hsD; linarith
      have hRB : (zL1 + Δ1 + s * c1) + (zL2 - s * c2) ≤ R := by
        have := (div_le_iff₀ hRpos).1 hsR; linarith
      have hcross1 : sD * (c2 - c1) ≤ R - (zH1 + zH2) + Δ1 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hDpos]
        have h1 : (a1 * zL1 + a2 * zL2 + a1 * Δ1 - D) * (c2 - c1) ≤ (a1 * Δ1) * (c2 - c1) :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hRpos)
        have h2 : Δ1 * (a2 * c2 - a1 * c1) ≤ (R - (zH1 + zH2) + Δ1) * (a2 * c2 - a1 * c1) :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hDpos)
        have h3 : 0 ≤ Δ1 * ((a2 - a1) * c2) :=
          mul_nonneg hΔ1 (mul_nonneg (sub_nonneg.2 (le_of_lt ha12)) (le_of_lt hc2))
        linarith
      have hcross2 : sR * (a2 * c2 - a1 * c1) ≤ D - (a1 * zH1 + a2 * zH2) + a1 * Δ1 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hRpos]
        have eR : zH1 + zH2 = zL1 + zL2 + Δ1 + Δ2 - (c2 - c1) := by
          dsimp only [zH1, zH2, zL1, zL2, Δ1, Δ2, c1, c2]; ring
        have eD : a1 * zH1 + a2 * zH2 = a1 * zL1 + a2 * zL2 + a1 * Δ1 + a2 * Δ2 - (a2 * c2 - a1 * c1) := by
          dsimp only [zH1, zH2, zL1, zL2, Δ1, Δ2, c1, c2]; ring
        have h_L : zL1 + zL2 + Δ1 - R ≤ (c2 - c1) - Δ2 := by linarith
        have h_R : (a2 * c2 - a1 * c1) - a2 * Δ2 ≤ D - (a1 * zH1 + a2 * zH2) + a1 * Δ1 := by linarith
        have h1 := mul_le_mul_of_nonneg_right h_L (le_of_lt hDpos)
        have h2 := mul_le_mul_of_nonneg_right h_R (le_of_lt hRpos)
        have h3 : 0 ≤ Δ2 * ((a2 - a1) * c1) :=
          mul_nonneg hΔ2 (mul_nonneg (sub_nonneg.2 (le_of_lt ha12)) (le_of_lt hc1))
        linarith
      have hDA : a1 * (zH1 - Δ1 - s * c1) + a2 * (zH2 + s * c2) ≤ D := by
        dsimp only [s]
        rcases max_choice 0 (max sD sR) with h | h <;> rw [h]
        · linarith
        · rcases max_choice sD sR with h' | h' <;> rw [h']
          · have hmul : sD * (a2 * c2 - a1 * c1) = a1 * zL1 + a2 * zL2 + a1 * Δ1 - D :=
              div_mul_cancel₀ _ (ne_of_gt hDpos)
            linarith
          · linarith
      have hRA : (zH1 - Δ1 - s * c1) + (zH2 + s * c2) ≤ R := by
        dsimp only [s]
        rcases max_choice 0 (max sD sR) with h | h <;> rw [h]
        · linarith
        · rcases max_choice sD sR with h' | h' <;> rw [h']
          · linarith
          · have hmul : sR * (c2 - c1) = zL1 + zL2 + Δ1 - R :=
              div_mul_cancel₀ _ (ne_of_gt hRpos)
            linarith
      exact ⟨s, hs0, hsM, hDA, hRA, hDB, hRB⟩

private lemma E2_pair_incomp4 {f : Vec → ℝ} (hc : ConvexOn ℝ orthant f)
    {a1 a2 D R x1 x1' x2 x2' : ℝ}
    (ha1 : 0 < a1) (ha12 : a1 < a2)
    (hx1 : x1 ≤ x1') (hx2 : x2 ≤ x2')
    {wL wH : Vec}
    (hwL : wL ∈ E2 a1 a2 (x1, x2) D R) (hwH : wH ∈ E2 a1 a2 (x1', x2') D R)
    (h1 : wL.1 < wH.1) (h2 : wH.2 < wL.2) :
    ∃ wA ∈ E2 a1 a2 (x1, x2') D R, ∃ wB ∈ E2 a1 a2 (x1', x2) D R,
      f wA + f wB ≤ f wL + f wH := by
  have ha2 : 0 < a2 := by linarith
  set c1 := wH.1 - wL.1
  set c2 := wL.2 - wH.2
  have hc1 : 0 < c1 := sub_pos.2 h1
  have hc2 : 0 < c2 := sub_pos.2 h2
  set Δ1 := x1' - x1
  set Δ2 := x2' - x2
  have hΔ1 : 0 ≤ Δ1 := sub_nonneg.2 hx1
  have hΔ2 : 0 ≤ Δ2 := sub_nonneg.2 hx2
  set zL1 := x1 - wL.1
  set zL2 := x2 - wL.2
  set zH1 := x1' - wH.1
  set zH2 := x2' - wH.2
  have hzL1 : 0 ≤ zL1 := sub_nonneg.2 hwL.2.1.1
  have hzL2 : 0 ≤ zL2 := sub_nonneg.2 hwL.2.1.2
  have hzH1 : 0 ≤ zH1 := sub_nonneg.2 hwH.2.1.1
  have hzH2 : 0 ≤ zH2 := sub_nonneg.2 hwH.2.1.2
  have hDL : a1 * zL1 + a2 * zL2 ≤ D := by linarith [hwL.2.2.1]
  have hDH : a1 * zH1 + a2 * zH2 ≤ D := by linarith [hwH.2.2.1]
  have hRL : zL1 + zL2 ≤ R := by linarith [hwL.2.2.2]
  have hRH : zH1 + zH2 ≤ R := by linarith [hwH.2.2.2]
  set Tmax := min 1 (zL1 / c1)
  have hTmax0 : 0 ≤ Tmax := le_min zero_le_one (div_nonneg hzL1 (le_of_lt hc1))
  have hTmax1 : Tmax ≤ 1 := min_le_left _ _
  have hTmax_c1 : Tmax * c1 ≤ zL1 := by
    have := (le_div_iff₀ hc1).1 (min_le_right 1 (zL1 / c1))
    linarith
  have hzA1_Tmax : zL1 - Tmax * c1 ≤ zH1 := by
    dsimp only [Tmax]
    rcases min_choice 1 (zL1 / c1) with h | h
    · rw [h]; linarith
    · rw [h, div_mul_cancel₀ _ (ne_of_gt hc1)]; linarith
  have hzA2_Tmax : zL2 + Δ2 + Tmax * c2 ≤ zH2 := by
    have : Tmax * c2 ≤ c2 := mul_le_of_le_one_left (le_of_lt hc2) hTmax1
    linarith
  have hDA_Tmax : a1 * (zL1 - Tmax * c1) + a2 * (zL2 + Δ2 + Tmax * c2) ≤ D := by
    have := mul_le_mul_of_nonneg_left hzA1_Tmax (le_of_lt ha1)
    have := mul_le_mul_of_nonneg_left hzA2_Tmax (le_of_lt ha2)
    linarith
  have hRA_Tmax : (zL1 - Tmax * c1) + (zL2 + Δ2 + Tmax * c2) ≤ R := by linarith
  suffices ∃ t : ℝ, 0 ≤ t ∧ t ≤ Tmax ∧
      a1 * (zL1 - t * c1) + a2 * (zL2 + Δ2 + t * c2) ≤ D ∧
      (zL1 - t * c1) + (zL2 + Δ2 + t * c2) ≤ R ∧
      a1 * (zH1 + t * c1) + a2 * (zH2 - Δ2 - t * c2) ≤ D ∧
      (zH1 + t * c1) + (zH2 - Δ2 - t * c2) ≤ R by
    obtain ⟨t, ht0, htM, hDA, hRA, hDB, hRB⟩ := this
    have ht1 : t ≤ 1 := le_trans htM hTmax1
    have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht1
    let wA : Vec := (1 - t) • wL + t • wH
    let wB : Vec := t • wL + (1 - t) • wH
    have hwA_mem : wA ∈ E2 a1 a2 (x1, x2') D R := by
      refine ⟨orthant_convex hwL.1 hwH.1 h1t ht0 (by ring), ⟨?_, ?_⟩, ?_, ?_⟩
      · simp only [wA, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        have : t * c1 ≤ zL1 := le_trans (mul_le_mul_of_nonneg_right htM (le_of_lt hc1)) hTmax_c1
        linarith
      · simp only [wA, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        have := mul_le_mul_of_nonneg_left (show wL.2 ≤ x2' by linarith [hwL.2.1.2]) h1t
        have := mul_le_mul_of_nonneg_left hwH.2.1.2 ht0
        linarith
      · simp only [wA, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        have e1 : x1 - ((1 - t) * wL.1 + t * wH.1) = zL1 - t * c1 := by
          dsimp only [zL1, c1]; ring
        have e2 : x2' - ((1 - t) * wL.2 + t * wH.2) = zL2 + Δ2 + t * c2 := by
          dsimp only [zL2, Δ2, c2]; ring
        linarith [hDA, e1, e2]
      · simp only [wA, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        have e1 : x1 - ((1 - t) * wL.1 + t * wH.1) = zL1 - t * c1 := by
          dsimp only [zL1, c1]; ring
        have e2 : x2' - ((1 - t) * wL.2 + t * wH.2) = zL2 + Δ2 + t * c2 := by
          dsimp only [zL2, Δ2, c2]; ring
        linarith [hRA, e1, e2]
    have hwB_mem : wB ∈ E2 a1 a2 (x1', x2) D R := by
      refine ⟨orthant_convex hwL.1 hwH.1 ht0 h1t (by ring), ⟨?_, ?_⟩, ?_, ?_⟩
      · simp only [wB, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        have := mul_le_mul_of_nonneg_left (show wL.1 ≤ x1' by linarith [hwL.2.1.1]) ht0
        have := mul_le_mul_of_nonneg_left hwH.2.1.1 h1t
        linarith
      · simp only [wB, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        have := mul_le_mul_of_nonneg_left hwL.2.1.2 ht0
        have := mul_le_mul_of_nonneg_left (show wH.2 ≤ x2 by linarith [hwL.2.1.2]) h1t
        linarith
      · simp only [wB, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        have e1 : x1' - (t * wL.1 + (1 - t) * wH.1) = zH1 + t * c1 := by
          dsimp only [zH1, c1]; ring
        have e2 : x2 - (t * wL.2 + (1 - t) * wH.2) = zH2 - Δ2 - t * c2 := by
          dsimp only [zH2, Δ2, c2]; ring
        linarith [hDB, e1, e2]
      · simp only [wB, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        have e1 : x1' - (t * wL.1 + (1 - t) * wH.1) = zH1 + t * c1 := by
          dsimp only [zH1, c1]; ring
        have e2 : x2 - (t * wL.2 + (1 - t) * wH.2) = zH2 - Δ2 - t * c2 := by
          dsimp only [zH2, Δ2, c2]; ring
        linarith [hRB, e1, e2]
    refine ⟨wA, hwA_mem, wB, hwB_mem, ?_⟩
    have hcA := hc.2 hwL.1 hwH.1 h1t ht0 (by ring)
    have hcB := hc.2 hwL.1 hwH.1 ht0 h1t (by ring)
    simp only [smul_eq_mul] at hcA hcB
    linarith
  -- Split into 3 slope regimes for t
  have ha2Δ2 : 0 ≤ a2 * Δ2 := mul_nonneg (le_of_lt ha2) hΔ2
  by_cases hRslope : c1 ≤ c2
  · -- Regime 4a: take t = 0
    have hDslope : a1 * c1 ≤ a2 * c2 := by
      have h1 : a1 * c1 ≤ a1 * c2 := mul_le_mul_of_nonneg_left hRslope (le_of_lt ha1)
      have h2 : a1 * c2 ≤ a2 * c2 := mul_le_mul_of_nonneg_right (le_of_lt ha12) (le_of_lt hc2)
      linarith
    have hDA0 : a1 * (zL1 - 0 * c1) + a2 * (zL2 + Δ2 + 0 * c2) ≤ D := by
      have := mul_le_mul_of_nonneg_left (sub_nonneg.2 hDslope) hTmax0
      linarith [hDA_Tmax]
    have hRA0 : (zL1 - 0 * c1) + (zL2 + Δ2 + 0 * c2) ≤ R := by
      have := mul_le_mul_of_nonneg_left (sub_nonneg.2 hRslope) hTmax0
      linarith [hRA_Tmax]
    exact ⟨0, le_rfl, hTmax0, hDA0, hRA0, by linarith, by linarith⟩
  · push Not at hRslope
    have hRpos : 0 < c1 - c2 := sub_pos.2 hRslope
    by_cases hDslope : a1 * c1 ≤ a2 * c2
    · -- Regime 4b: take t = max 0 ((RL + Δ2 - R) / (c1 - c2))
      set tR := (zL1 + zL2 + Δ2 - R) / (c1 - c2)
      set t := max 0 tR
      have ht0 : 0 ≤ t := le_max_left _ _
      have htM : t ≤ Tmax := max_le hTmax0 ((div_le_iff₀ hRpos).2 (by linarith [hRA_Tmax]))
      have hRA : (zL1 - t * c1) + (zL2 + Δ2 + t * c2) ≤ R := by
        have := (div_le_iff₀ hRpos).1 (le_max_right 0 tR); linarith
      have hRB : (zH1 + t * c1) + (zH2 - Δ2 - t * c2) ≤ R := by
        dsimp only [t]
        rcases max_choice 0 tR with h | h
        · rw [h]; linarith
        · rw [h]
          have hmul : tR * (c1 - c2) = zL1 + zL2 + Δ2 - R :=
            div_mul_cancel₀ _ (ne_of_gt hRpos)
          linarith
      have hDA : a1 * (zL1 - t * c1) + a2 * (zL2 + Δ2 + t * c2) ≤ D := by
        have := mul_le_mul_of_nonneg_left (sub_nonneg.2 hDslope) (sub_nonneg.2 htM)
        linarith [hDA_Tmax]
      have hDB : a1 * (zH1 + t * c1) + a2 * (zH2 - Δ2 - t * c2) ≤ D := by
        have := mul_le_mul_of_nonneg_left (sub_nonneg.2 hDslope) ht0
        linarith
      exact ⟨t, ht0, htM, hDA, hRA, hDB, hRB⟩
    · -- Regime 4c: a2*c2 < a1*c1 and c2 < c1
      push Not at hDslope
      have hDpos : 0 < a1 * c1 - a2 * c2 := sub_pos.2 hDslope
      set tD := (a1 * zL1 + a2 * zL2 + a2 * Δ2 - D) / (a1 * c1 - a2 * c2)
      set tR := (zL1 + zL2 + Δ2 - R) / (c1 - c2)
      set t := max 0 (max tD tR)
      have ht0 : 0 ≤ t := le_max_left _ _
      have htM : t ≤ Tmax := max_le hTmax0 (max_le
        ((div_le_iff₀ hDpos).2 (by linarith [hDA_Tmax]))
        ((div_le_iff₀ hRpos).2 (by linarith [hRA_Tmax])))
      have htD : tD ≤ t := le_trans (le_max_left _ _) (le_max_right _ _)
      have htR : tR ≤ t := le_trans (le_max_right _ _) (le_max_right _ _)
      have hDA : a1 * (zL1 - t * c1) + a2 * (zL2 + Δ2 + t * c2) ≤ D := by
        have := (div_le_iff₀ hDpos).1 htD; linarith
      have hRA : (zL1 - t * c1) + (zL2 + Δ2 + t * c2) ≤ R := by
        have := (div_le_iff₀ hRpos).1 htR; linarith
      have hcross1 : tD * (c1 - c2) ≤ R - (zH1 + zH2) + Δ2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hDpos]
        have eR : zH1 + zH2 = zL1 + zL2 + Δ1 + Δ2 - (c1 - c2) := by
          dsimp only [zH1, zH2, zL1, zL2, Δ1, Δ2, c1, c2]; ring
        have eD : a1 * zH1 + a2 * zH2 = a1 * zL1 + a2 * zL2 + a1 * Δ1 + a2 * Δ2 - (a1 * c1 - a2 * c2) := by
          dsimp only [zH1, zH2, zL1, zL2, Δ1, Δ2, c1, c2]; ring
        have h_L : a1 * zL1 + a2 * zL2 + a2 * Δ2 - D ≤ (a1 * c1 - a2 * c2) - a1 * Δ1 := by linarith
        have h_R : (c1 - c2) - Δ1 ≤ R - (zH1 + zH2) + Δ2 := by linarith
        have h1 := mul_le_mul_of_nonneg_right h_L (le_of_lt hRpos)
        have h2 := mul_le_mul_of_nonneg_right h_R (le_of_lt hDpos)
        have h3 : 0 ≤ Δ1 * ((a2 - a1) * c2) :=
          mul_nonneg hΔ1 (mul_nonneg (sub_nonneg.2 (le_of_lt ha12)) (le_of_lt hc2))
        linarith
      have hcross2 : tR * (a1 * c1 - a2 * c2) ≤ D - (a1 * zH1 + a2 * zH2) + a2 * Δ2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hRpos]
        have h1 : (zL1 + zL2 + Δ2 - R) * (a1 * c1 - a2 * c2) ≤ Δ2 * (a1 * c1 - a2 * c2) :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hDpos)
        have h2 : (a2 * Δ2) * (c1 - c2) ≤ (D - (a1 * zH1 + a2 * zH2) + a2 * Δ2) * (c1 - c2) :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hRpos)
        have h3 : 0 ≤ Δ2 * ((a2 - a1) * c1) :=
          mul_nonneg hΔ2 (mul_nonneg (sub_nonneg.2 (le_of_lt ha12)) (le_of_lt hc1))
        linarith
      have hDB : a1 * (zH1 + t * c1) + a2 * (zH2 - Δ2 - t * c2) ≤ D := by
        dsimp only [t]
        rcases max_choice 0 (max tD tR) with h | h <;> rw [h]
        · linarith
        · rcases max_choice tD tR with h' | h' <;> rw [h']
          · have hmul : tD * (a1 * c1 - a2 * c2) = a1 * zL1 + a2 * zL2 + a2 * Δ2 - D :=
              div_mul_cancel₀ _ (ne_of_gt hDpos)
            linarith
          · linarith
      have hRB : (zH1 + t * c1) + (zH2 - Δ2 - t * c2) ≤ R := by
        dsimp only [t]
        rcases max_choice 0 (max tD tR) with h | h <;> rw [h]
        · linarith
        · rcases max_choice tD tR with h' | h' <;> rw [h']
          · linarith
          · have hmul : tR * (c1 - c2) = zL1 + zL2 + Δ2 - R :=
              div_mul_cancel₀ _ (ne_of_gt hRpos)
            linarith
      exact ⟨t, ht0, htM, hDA, hRA, hDB, hRB⟩

private lemma U_supermodularOn {f : Vec → ℝ} (hf : Shape f)
    {a1 a2 D R : ℝ} (ha1 : 0 < a1) (ha12 : a1 < a2) (hD : 0 ≤ D) (hR : 0 ≤ R) :
    SupermodularOn (fun y => sInf (f '' E2 a1 a2 y D R)) orthant := by
  obtain ⟨hc, hcont, hsm⟩ := hf
  have ha2 : 0 < a2 := by linarith
  have hrect : ∀ x1 x1' x2 x2' : ℝ, 0 ≤ x1 → x1 ≤ x1' → 0 ≤ x2 → x2 ≤ x2' →
      sInf (f '' E2 a1 a2 (x1, x2') D R) + sInf (f '' E2 a1 a2 (x1', x2) D R) ≤
        sInf (f '' E2 a1 a2 (x1, x2) D R) + sInf (f '' E2 a1 a2 (x1', x2') D R) := by
    intro x1 x1' x2 x2' hx1 hx1' hx2 hx2'
    have hL_mem : ((x1, x2) : Vec) ∈ orthant := (mem_orthant_iff _).2 ⟨hx1, hx2⟩
    have hH_mem : ((x1', x2') : Vec) ∈ orthant := (mem_orthant_iff _).2 ⟨by linarith, by linarith⟩
    have hA_mem : ((x1, x2') : Vec) ∈ orthant := (mem_orthant_iff _).2 ⟨hx1, by linarith⟩
    have hB_mem : ((x1', x2) : Vec) ∈ orthant := (mem_orthant_iff _).2 ⟨by linarith, hx2⟩
    obtain ⟨wL, hwL, hUL, _⟩ := U_attained hcont a1 a2 hD hR hL_mem
    obtain ⟨wH, hwH, hUH, _⟩ := U_attained hcont a1 a2 hD hR hH_mem
    obtain ⟨_, _, hUA, hminA⟩ := U_attained hcont a1 a2 hD hR hA_mem
    obtain ⟨_, _, hUB, hminB⟩ := U_attained hcont a1 a2 hD hR hB_mem
    have hpair : ∃ wA ∈ E2 a1 a2 (x1, x2') D R, ∃ wB ∈ E2 a1 a2 (x1', x2) D R,
        f wA + f wB ≤ f wL + f wH := by
      rcases le_or_gt wL.1 wH.1 with h1 | h1 <;> rcases le_or_gt wL.2 wH.2 with h2 | h2
      · exact E2_pair_le hc hsm ha1 ha12 hx1' hx2' hwL hwH h1 h2
      · rcases eq_or_lt_of_le h1 with h1e | h1s
        · exact E2_pair_ge hsm ha1 ha2 hx1' hx2' hwL hwH (le_of_eq h1e.symm) (le_of_lt h2)
        · exact E2_pair_incomp4 hc ha1 ha12 hx1' hx2' hwL hwH h1s h2
      · rcases eq_or_lt_of_le h2 with h2e | h2s
        · exact E2_pair_ge hsm ha1 ha2 hx1' hx2' hwL hwH (le_of_lt h1) (le_of_eq h2e.symm)
        · exact E2_pair_incomp3 hc ha1 ha12 hx1' hx2' hwL hwH h1 h2s
      · exact E2_pair_ge hsm ha1 ha2 hx1' hx2' hwL hwH (le_of_lt h1) (le_of_lt h2)
    obtain ⟨wA, hwA, wB, hwB, hle⟩ := hpair
    rw [hUL, hUH, hUA, hUB]
    linarith [hminA wA hwA, hminB wB hwB]
  intro x hx y hy
  have hx' := (mem_orthant_iff x).1 hx
  have hy' := (mem_orthant_iff y).1 hy
  rcases le_total x.1 y.1 with h1 | h1 <;> rcases le_total x.2 y.2 with h2 | h2
  · have hsup : x ⊔ y = y := by ext <;> [simp [max_eq_right h1]; simp [max_eq_right h2]]
    have hinf : x ⊓ y = x := by ext <;> [simp [min_eq_left h1]; simp [min_eq_left h2]]
    rw [hsup, hinf, add_comm]
  · have hsup : x ⊔ y = (y.1, x.2) := by ext <;> [simp [max_eq_right h1]; simp [max_eq_left h2]]
    have hinf : x ⊓ y = (x.1, y.2) := by ext <;> [simp [min_eq_left h1]; simp [min_eq_right h2]]
    rw [hsup, hinf]
    have := hrect x.1 y.1 y.2 x.2 hx'.1 h1 hy'.2 h2
    simp only [Prod.eta] at this
    linarith
  · have hsup : x ⊔ y = (x.1, y.2) := by ext <;> [simp [max_eq_left h1]; simp [max_eq_right h2]]
    have hinf : x ⊓ y = (y.1, x.2) := by ext <;> [simp [min_eq_right h1]; simp [min_eq_left h2]]
    rw [hsup, hinf]
    have := hrect y.1 x.1 x.2 y.2 hy'.1 h1 hx'.2 h2
    simp only [Prod.eta] at this
    linarith
  · have hsup : x ⊔ y = x := by ext <;> [simp [max_eq_left h1]; simp [max_eq_left h2]]
    have hinf : x ⊓ y = y := by ext <;> [simp [min_eq_right h1]; simp [min_eq_right h2]]
    rw [hsup, hinf]

private lemma U_shape {f : Vec → ℝ} (hf : Shape f)
    {a1 a2 D R : ℝ} (ha1 : 0 < a1) (ha12 : a1 < a2) (hD : 0 ≤ D) (hR : 0 ≤ R) :
    Shape (fun y => sInf (f '' E2 a1 a2 y D R)) :=
  ⟨U_convexOn hf.1 hf.2.1 hD hR, U_continuousOn hf.2.1 ha1 (by linarith) hD hR,
    U_supermodularOn hf ha1 ha12 hD hR⟩

/-! ### Section 3: Structure and linear lower bounds for `J` and `Gbar` -/

private lemma J_shape (d : Data) (t : ℕ) (hH : H d t) : Shape (J d t) := by
  have h := shape_add_linear (d.a1 * p d t + d.h1 t - d.c1 (t + 1))
    (d.a2 * p d t + d.h2 t - d.c2 (t + 1)) 0 (V d (t + 1)) hH.1
  convert h using 1
  ext w
  simp [J, Jstep]

private lemma J_linear_lower (d : Data) (t : ℕ) (hH : H d t) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ w ∈ orthant,
      (d.a1 * p d t + d.h1 t - ε) * w.1 + (d.a2 * p d t + d.h2 t - ε) * w.2 + C ≤ J d t w := by
  have hJshape : Shape (J d t) := J_shape d t hH
  obtain ⟨_, hg1, hg2⟩ := hH
  -- 1D lower bound along axis 1
  have h1 : ∃ C1 : ℝ, ∀ s : ℝ, 0 ≤ s → (d.a1 * p d t + d.h1 t - ε) * s + C1 ≤ J d t (s, 0) := by
    have hev := hg1 ε hε 0 le_rfl
    rw [Filter.eventually_atTop] at hev
    obtain ⟨S0, hS0⟩ := hev
    let S := max S0 1
    have hS_pos : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    let g : ℝ → ℝ := fun s => J d t (s, 0) - (d.a1 * p d t + d.h1 t - ε) * s
    have hg_cont : ContinuousOn g (Set.Icc 0 S) := by
      have h1 : ContinuousOn (fun s : ℝ => J d t (s, 0)) (Set.Icc 0 S) :=
        hJshape.2.1.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun s hs => (mem_orthant_iff _).2 ⟨hs.1, le_rfl⟩)
      exact h1.sub (by fun_prop)
    obtain ⟨m, _, hm⟩ := isCompact_Icc.exists_isMinOn ⟨0, le_rfl, le_of_lt hS_pos⟩ hg_cont
    refine ⟨min (g m) 0, fun s hs => ?_⟩
    by_cases hsS : s ≤ S
    · have := hm ⟨hs, hsS⟩
      have hle : min (g m) 0 ≤ g s := le_trans (min_le_left _ _) this
      dsimp only [g] at hle; linarith
    · push Not at hsS
      have hs0 : 0 < s := lt_trans hS_pos hsS
      have hsS0 : S0 ≤ s := le_trans (le_max_left _ _) (le_of_lt hsS)
      have hdiv := hS0 s hsS0
      rw [le_div_iff₀ hs0] at hdiv
      have hmin0 : min (g m) 0 ≤ 0 := min_le_right _ _
      simp only [J, Jstep, mul_zero, add_zero]
      linarith
  -- 1D lower bound along axis 2
  have h2 : ∃ C2 : ℝ, ∀ s : ℝ, 0 ≤ s → (d.a2 * p d t + d.h2 t - ε) * s + C2 ≤ J d t (0, s) := by
    have hev := hg2 ε hε 0 le_rfl
    rw [Filter.eventually_atTop] at hev
    obtain ⟨S0, hS0⟩ := hev
    let S := max S0 1
    have hS_pos : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    let g : ℝ → ℝ := fun s => J d t (0, s) - (d.a2 * p d t + d.h2 t - ε) * s
    have hg_cont : ContinuousOn g (Set.Icc 0 S) := by
      have h1 : ContinuousOn (fun s : ℝ => J d t (0, s)) (Set.Icc 0 S) :=
        hJshape.2.1.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun s hs => (mem_orthant_iff _).2 ⟨le_rfl, hs.1⟩)
      exact h1.sub (by fun_prop)
    obtain ⟨m, _, hm⟩ := isCompact_Icc.exists_isMinOn ⟨0, le_rfl, le_of_lt hS_pos⟩ hg_cont
    refine ⟨min (g m) 0, fun s hs => ?_⟩
    by_cases hsS : s ≤ S
    · have := hm ⟨hs, hsS⟩
      have hle : min (g m) 0 ≤ g s := le_trans (min_le_left _ _) this
      dsimp only [g] at hle; linarith
    · push Not at hsS
      have hs0 : 0 < s := lt_trans hS_pos hsS
      have hsS0 : S0 ≤ s := le_trans (le_max_left _ _) (le_of_lt hsS)
      have hdiv := hS0 s hsS0
      rw [le_div_iff₀ hs0] at hdiv
      have hmin0 : min (g m) 0 ≤ 0 := min_le_right _ _
      simp only [J, Jstep, mul_zero, zero_add]
      linarith
  obtain ⟨C1, hC1⟩ := h1
  obtain ⟨C2, hC2⟩ := h2
  refine ⟨C1 + C2 - J d t (0, 0), fun w hw => ?_⟩
  have hw' := (mem_orthant_iff w).1 hw
  have hsm := hJshape.2.2 ((mem_orthant_iff (w.1, 0)).2 ⟨hw'.1, le_rfl⟩)
    ((mem_orthant_iff (0, w.2)).2 ⟨le_rfl, hw'.2⟩)
  have hsup : ((w.1, 0) : Vec) ⊔ (0, w.2) = w := by
    ext <;> [simp [max_eq_left hw'.1]; simp [max_eq_right hw'.2]]
  have hinf : ((w.1, 0) : Vec) ⊓ (0, w.2) = (0, 0) := by
    ext <;> [simp [min_eq_right hw'.1]; simp [min_eq_left hw'.2]]
  rw [hsup, hinf] at hsm
  linarith [hC1 w.1 hw'.1, hC2 w.2 hw'.2]

private lemma Gbar_linear_lower (d : Data) (hd : d.Standing) (t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ d.T) (hH : H d t)
    {ε : ℝ} (hε : 0 < ε) (hε_le : ε ≤ d.a1 * p d t) :
    ∃ C : ℝ, ∀ y ∈ orthant,
      (d.c1 t + d.h1 t - ε) * y.1 + (d.c2 t + d.h2 t - ε) * y.2 + C ≤ Gbar d t y := by
  have ⟨_, ha1, ha12, hper, _⟩ := hd
  obtain ⟨hσ, he, hh1, hh2, _, _, hDR_prob, hDR_nn, _⟩ := hper t ht htT
  have hp : 0 < p d t := by unfold p; linarith
  have hk1_nn : 0 ≤ d.a1 * p d t + d.h1 t - ε := by linarith
  have hk2_nn : 0 ≤ d.a2 * p d t + d.h2 t - ε := by nlinarith
  obtain ⟨CJ, hCJ⟩ := J_linear_lower d t hH hε
  let k1 := d.a1 * p d t + d.h1 t - ε
  let k2 := d.a2 * p d t + d.h2 t - ε
  let Cbar := CJ + (d.DR t).expect (fun z => -(k1 + k2) * z.2 + d.σ t * z.1)
  refine ⟨Cbar, fun y hy => ?_⟩
  have hU_lb : ∀ z ∈ (d.DR t).supp,
      k1 * y.1 + k2 * y.2 + CJ - (k1 + k2) * z.2 ≤ U d t y z.1 z.2 := by
    intro z hz
    have hz_nn := hDR_nn z hz
    refine le_csInf ⟨J d t y, y, E2_self_mem hy hz_nn.1 hz_nn.2, rfl⟩ ?_
    rintro _ ⟨w, hw, rfl⟩
    have hw1_lb : y.1 - z.2 ≤ w.1 := by linarith [hw.2.1.2, hw.2.2.2]
    have hw2_lb : y.2 - z.2 ≤ w.2 := by linarith [hw.2.1.1, hw.2.2.2]
    have hJw := hCJ w hw.1
    dsimp only [J, k1, k2] at hJw ⊢
    nlinarith
  have hexp_lb :
      k1 * y.1 + k2 * y.2 + Cbar ≤
        (d.DR t).expect (fun z => U d t y z.1 z.2 + d.σ t * z.1) := by
    have hsum1 : (d.DR t).expect (fun z => (k1 * y.1 + k2 * y.2 + CJ) + (-(k1 + k2) * z.2 + d.σ t * z.1))
        = k1 * y.1 + k2 * y.2 + Cbar := by
      simp only [FinLaw.expect, Cbar, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hDR_prob.2, one_mul]
      ring
    rw [← hsum1]
    simp only [FinLaw.expect]
    refine Finset.sum_le_sum fun z hz => ?_
    have hw := hDR_prob.1 z hz
    have hlb := hU_lb z hz
    nlinarith
  simp only [Gbar, Gbarstep]
  dsimp only [k1, k2, U] at hexp_lb
  linarith

private lemma Gbar_coercive (d : Data) (hd : d.Standing) (t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ d.T) (hH : H d t) :
    ∃ α1 α2 C : ℝ, 0 < α1 ∧ 0 < α2 ∧ ∀ y ∈ orthant, α1 * y.1 + α2 * y.2 + C ≤ Gbar d t y := by
  have ⟨_, ha1, _, hper, _⟩ := hd
  obtain ⟨hσ, he, _, _, hch1, hch2, _⟩ := hper t ht htT
  have hp : 0 < p d t := by unfold p; linarith
  let ε := min (d.a1 * p d t) (min ((d.c1 t + d.h1 t) / 2) ((d.c2 t + d.h2 t) / 2))
  have hε : 0 < ε := by positivity
  have hε_le : ε ≤ d.a1 * p d t := min_le_left _ _
  have hε1 : ε ≤ (d.c1 t + d.h1 t) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε2 : ε ≤ (d.c2 t + d.h2 t) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨C, hC⟩ := Gbar_linear_lower d hd t ht htT hH hε hε_le
  refine ⟨(d.c1 t + d.h1 t) / 2, (d.c2 t + d.h2 t) / 2, C, by linarith, by linarith, fun y hy => ?_⟩
  have hy' := (mem_orthant_iff y).1 hy
  have := hC y hy
  nlinarith

private lemma Gbar_shape (d : Data) (hd : d.Standing) (t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ d.T) (hH : H d t) : Shape (Gbar d t) := by
  have ⟨_, ha1, ha12, hper, _⟩ := hd
  obtain ⟨_, _, _, _, _, _, hDR_prob, hDR_nn, _⟩ := hper t ht htT
  have hJ : Shape (J d t) := J_shape d t hH
  have hexp : Shape (fun y => (d.DR t).expect (fun z => U d t y z.1 z.2 + d.σ t * z.1)) :=
    shape_expect (d.DR t) hDR_prob _ fun z hz =>
      shape_add_const (d.σ t * z.1) _ (U_shape hJ ha1 ha12 (hDR_nn z hz).1 (hDR_nn z hz).2)
  have h := shape_add_linear (d.c1 t - d.a1 * p d t) (d.c2 t - d.a2 * p d t) 0 _ hexp
  convert h using 1
  ext y
  simp [Gbar, Gbarstep, U]

/-! ### Section 4: Exact convex-lattice reformulation of `Vstep` -/

private def inCap (x w : ℝ) : WithTop ℝ → Prop
  | ⊤ => x ≤ w
  | (r : ℝ) => x ≤ w ∧ w ≤ x + r

private lemma capAt_inCap {y x : ℝ} (hxy : x ≤ y) {q : WithTop ℝ} (hq : (0 : WithTop ℝ) ≤ q) :
    inCap x (capAt y x q) q := by
  cases q with
  | top => exact hxy
  | coe r =>
    have hr : 0 ≤ r := WithTop.coe_le_coe.1 hq
    exact ⟨le_min hxy (by linarith), min_le_right _ _⟩

private lemma inCap_self {x : ℝ} {q : WithTop ℝ} (hq : (0 : WithTop ℝ) ≤ q) :
    inCap x x q := by
  cases q with
  | top => exact le_rfl
  | coe r =>
    have hr : 0 ≤ r := WithTop.coe_le_coe.1 hq
    exact ⟨le_rfl, by linarith⟩

private lemma inCap_le_left {x w : ℝ} {q : WithTop ℝ} (h : inCap x w q) : x ≤ w := by
  cases q with
  | top => exact h
  | coe r => exact h.1

private lemma oneD_cap_opt {Φ : ℝ → ℝ} (hc : ConvexOn ℝ (Set.Ici 0) Φ)
    (hcont : ContinuousOn Φ (Set.Ici 0)) {α C : ℝ} (hα : 0 < α)
    (hcoer : ∀ u : ℝ, 0 ≤ u → α * u + C ≤ Φ u) {x : ℝ} (hx : 0 ≤ x) :
    ∃ y : ℝ, x ≤ y ∧ ∀ q : WithTop ℝ, (0 : WithTop ℝ) ≤ q →
      ∀ w : ℝ, inCap x w q → Φ (capAt y x q) ≤ Φ w := by
  let M := max 0 ((Φ 0 - C) / α)
  have hM : 0 ≤ M := le_max_left _ _
  have hIcc_sub : Set.Icc (0 : ℝ) M ⊆ Set.Ici 0 := fun _ h => h.1
  obtain ⟨u0, hu0_mem, hu0_min⟩ :=
    isCompact_Icc.exists_isMinOn ⟨0, le_rfl, hM⟩ (hcont.mono hIcc_sub)
  have hu0_glob : ∀ u : ℝ, 0 ≤ u → Φ u0 ≤ Φ u := by
    intro u hu
    by_cases huM : u ≤ M
    · exact hu0_min ⟨hu, huM⟩
    · push Not at huM
      have h1 : (Φ 0 - C) / α < u := lt_of_le_of_lt (le_max_right _ _) huM
      have h2 : Φ 0 < α * u + C := by
        have := (div_lt_iff₀ hα).1 h1; linarith
      have h3 : Φ u0 ≤ Φ 0 := hu0_min ⟨le_rfl, hM⟩
      linarith [hcoer u hu]
  have hinc : ∀ a b : ℝ, u0 ≤ a → a ≤ b → Φ a ≤ Φ b := by
    intro a b hua hab
    rcases eq_or_lt_of_le (le_trans hua hab) with heq | hlt
    · have : a = b := le_antisymm hab (by linarith)
      rw [this]
    · let t := (a - u0) / (b - u0)
      have hbu : 0 < b - u0 := sub_pos.2 hlt
      have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.2 hua) (le_of_lt hbu)
      have ht1 : t ≤ 1 := (div_le_one hbu).2 (by linarith)
      have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht1
      have ha_eq : (1 - t) • u0 + t • b = a := by
        simp only [smul_eq_mul, t]; field_simp [ne_of_gt hbu]; ring
      have hconv := hc.2 hu0_mem.1 (le_trans hu0_mem.1 (le_trans hua hab)) h1t ht0 (by ring)
      rw [ha_eq] at hconv
      simp only [smul_eq_mul] at hconv
      have hminb := hu0_glob b (le_trans hu0_mem.1 (le_trans hua hab))
      nlinarith
  have hdec : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ u0 → Φ b ≤ Φ a := by
    intro a b ha hab hbu
    rcases eq_or_lt_of_le (le_trans hab hbu) with heq | hlt
    · have : a = b := le_antisymm hab (by linarith)
      rw [this]
    · let t := (b - a) / (u0 - a)
      have hua : 0 < u0 - a := sub_pos.2 hlt
      have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.2 hab) (le_of_lt hua)
      have ht1 : t ≤ 1 := (div_le_one hua).2 (by linarith)
      have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht1
      have hb_eq : (1 - t) • a + t • u0 = b := by
        simp only [smul_eq_mul, t]; field_simp [ne_of_gt hua]; ring
      have hconv := hc.2 ha hu0_mem.1 h1t ht0 (by ring)
      rw [hb_eq] at hconv
      simp only [smul_eq_mul] at hconv
      have hmina := hu0_glob a ha
      nlinarith
  refine ⟨max x u0, le_max_left _ _, fun q hq w hw => ?_⟩
  cases q with
  | top =>
    simp only [capAt]
    have hxw : x ≤ w := hw
    rcases le_total u0 x with hux | hxu
    · rw [max_eq_left hux]; exact hinc x w hux hxw
    · rw [max_eq_right hxu]; exact hu0_glob w (le_trans hx hxw)
  | coe r =>
    simp only [capAt]
    have hr : 0 ≤ r := WithTop.coe_le_coe.1 hq
    rcases le_total u0 x with hux | hxu
    · rw [max_eq_left hux, min_eq_left (by linarith)]
      exact hinc x w hux hw.1
    · rw [max_eq_right hxu]
      rcases le_total u0 (x + r) with hur | hru
      · rw [min_eq_left hur]; exact hu0_glob w (le_trans hx hw.1)
      · rw [min_eq_right hru]; exact hdec w (x + r) (le_trans hx hw.1) hw.2 hru

private def Fobj (μ1 μ2 : FinLaw (WithTop ℝ)) (f : Vec → ℝ)
    (p : (WithTop ℝ → ℝ) × (WithTop ℝ → ℝ)) : ℝ :=
  μ1.expect (fun q1 => μ2.expect (fun q2 => f (p.1 q1, p.2 q2)))

private def Box (μ1 μ2 : FinLaw (WithTop ℝ)) (x : Vec) :
    Set ((WithTop ℝ → ℝ) × (WithTop ℝ → ℝ)) :=
  {p | (∀ q1 ∈ μ1.supp, inCap x.1 (p.1 q1) q1) ∧ (∀ q2 ∈ μ2.supp, inCap x.2 (p.2 q2) q2)}

private lemma Box_nonempty {μ1 μ2 : FinLaw (WithTop ℝ)}
    (h1nn : ∀ q ∈ μ1.supp, (0 : WithTop ℝ) ≤ q)
    (h2nn : ∀ q ∈ μ2.supp, (0 : WithTop ℝ) ≤ q) (x : Vec) :
    (Box μ1 μ2 x).Nonempty :=
  ⟨(fun _ => x.1, fun _ => x.2),
    fun q1 hq1 => inCap_self (h1nn q1 hq1),
    fun q2 hq2 => inCap_self (h2nn q2 hq2)⟩

private lemma Fobj_bddBelow {μ1 μ2 : FinLaw (WithTop ℝ)} {f : Vec → ℝ}
    (h1p : μ1.IsProb) (h2p : μ2.IsProb)
    {α1 α2 C : ℝ} (hα1 : 0 < α1) (hα2 : 0 < α2)
    (hcoer : ∀ u ∈ orthant, α1 * u.1 + α2 * u.2 + C ≤ f u)
    {x : Vec} (hx : x ∈ orthant) :
    BddBelow (Fobj μ1 μ2 f '' Box μ1 μ2 x) := by
  refine ⟨C, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hx' := (mem_orthant_iff x).1 hx
  have hge : ∀ q1 ∈ μ1.supp, C ≤ μ2.expect (fun q2 => f (p.1 q1, p.2 q2)) := by
    intro q1 hq1
    have h1 : 0 ≤ p.1 q1 := le_trans hx'.1 (inCap_le_left (hp.1 q1 hq1))
    calc C = μ2.expect (fun _ => C) := by
          simp [FinLaw.expect, ← Finset.sum_mul, h2p.2]
      _ ≤ μ2.expect (fun q2 => f (p.1 q1, p.2 q2)) := by
          refine Finset.sum_le_sum fun q2 hq2 => ?_
          have h2 : 0 ≤ p.2 q2 := le_trans hx'.2 (inCap_le_left (hp.2 q2 hq2))
          have hf := hcoer (p.1 q1, p.2 q2) ((mem_orthant_iff _).2 ⟨h1, h2⟩)
          have hC_le : C ≤ f (p.1 q1, p.2 q2) := by nlinarith
          exact mul_le_mul_of_nonneg_left hC_le (h2p.1 q2 hq2)
  calc C = μ1.expect (fun _ => C) := by
        simp [FinLaw.expect, ← Finset.sum_mul, h1p.2]
    _ ≤ Fobj μ1 μ2 f p := by
        refine Finset.sum_le_sum fun q1 hq1 =>
          mul_le_mul_of_nonneg_left (hge q1 hq1) (h1p.1 q1 hq1)

private lemma V_eq_sInf_Box {μ1 μ2 : FinLaw (WithTop ℝ)} {f : Vec → ℝ}
    (h1p : μ1.IsProb) (h2p : μ2.IsProb)
    (h1nn : ∀ q ∈ μ1.supp, (0 : WithTop ℝ) ≤ q)
    (h2nn : ∀ q ∈ μ2.supp, (0 : WithTop ℝ) ≤ q)
    (hf : Shape f) {α1 α2 C : ℝ} (hα1 : 0 < α1) (hα2 : 0 < α2)
    (hcoer : ∀ u ∈ orthant, α1 * u.1 + α2 * u.2 + C ≤ f u)
    {x : Vec} (hx : x ∈ orthant) :
    sInf ((fun y : Vec => μ1.expect (fun q1 => μ2.expect (fun q2 =>
        f (capAt y.1 x.1 q1, capAt y.2 x.2 q2)))) '' {y : Vec | x ≤ y}) =
      sInf (Fobj μ1 μ2 f '' Box μ1 μ2 x) := by
  have hx' := (mem_orthant_iff x).1 hx
  let Gfun : Vec → ℝ := fun y =>
    μ1.expect (fun q1 => μ2.expect (fun q2 => f (capAt y.1 x.1 q1, capAt y.2 x.2 q2)))
  have hG_ne : (Gfun '' {y : Vec | x ≤ y}).Nonempty := ⟨Gfun x, x, Set.mem_ofPred.2 le_rfl, rfl⟩
  have hB_ne : (Fobj μ1 μ2 f '' Box μ1 μ2 x).Nonempty :=
    (Box_nonempty h1nn h2nn x).image _
  have hB_bdd : BddBelow (Fobj μ1 μ2 f '' Box μ1 μ2 x) :=
    Fobj_bddBelow h1p h2p hα1 hα2 hcoer hx
  have hG_bdd : BddBelow (Gfun '' {y : Vec | x ≤ y}) := by
    obtain ⟨m, hm⟩ := hB_bdd
    refine ⟨m, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hm ⟨(fun q1 => capAt y.1 x.1 q1, fun q2 => capAt y.2 x.2 q2),
      ⟨fun q1 hq1 => capAt_inCap hy.1 (h1nn q1 hq1),
       fun q2 hq2 => capAt_inCap hy.2 (h2nn q2 hq2)⟩, rfl⟩
  apply le_antisymm
  · refine le_csInf hB_ne ?_
    rintro _ ⟨p, hp, rfl⟩
    -- Step 1: optimize coord 1 via 1D capping lemma
    let Φ : ℝ → ℝ := fun u1 => μ2.expect (fun q2 => f (u1, p.2 q2))
    have hΦ_conv : ConvexOn ℝ (Set.Ici 0) Φ := by
      refine ⟨convex_Ici 0, fun u hu v hv a b ha hb hab => ?_⟩
      simp only [Φ, FinLaw.expect, smul_eq_mul, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun q2 hq2 => ?_
      have h2 : 0 ≤ p.2 q2 := le_trans hx'.2 (inCap_le_left (hp.2 q2 hq2))
      have hc := hf.1.2 ((mem_orthant_iff (u, p.2 q2)).2 ⟨hu, h2⟩)
        ((mem_orthant_iff (v, p.2 q2)).2 ⟨hv, h2⟩) ha hb hab
      have hpt : a • ((u, p.2 q2) : Vec) + b • (v, p.2 q2) = (a * u + b * v, p.2 q2) := by
        ext <;> simp [smul_eq_mul]
        linear_combination hab * p.2 q2
      rw [hpt] at hc
      simp only [smul_eq_mul] at hc
      nlinarith [h2p.1 q2 hq2]
    have hΦ_cont : ContinuousOn Φ (Set.Ici 0) := by
      simp only [Φ, FinLaw.expect]
      refine continuousOn_finsetSum _ fun q2 hq2 => continuousOn_const.mul ?_
      have h2 : 0 ≤ p.2 q2 := le_trans hx'.2 (inCap_le_left (hp.2 q2 hq2))
      exact hf.2.1.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun u hu => (mem_orthant_iff _).2 ⟨hu, h2⟩)
    have hΦ_coer : ∀ u : ℝ, 0 ≤ u → α1 * u + C ≤ Φ u := by
      intro u hu
      calc α1 * u + C = μ2.expect (fun _ => α1 * u + C) := by
            simp [FinLaw.expect, ← Finset.sum_mul, h2p.2]
        _ ≤ Φ u := by
            refine Finset.sum_le_sum fun q2 hq2 => ?_
            have h2 : 0 ≤ p.2 q2 := le_trans hx'.2 (inCap_le_left (hp.2 q2 hq2))
            have hfu := hcoer (u, p.2 q2) ((mem_orthant_iff _).2 ⟨hu, h2⟩)
            have hle : α1 * u + C ≤ f (u, p.2 q2) := by nlinarith
            exact mul_le_mul_of_nonneg_left hle (h2p.1 q2 hq2)
    obtain ⟨y1, hy1, hy1_opt⟩ := oneD_cap_opt hΦ_conv hΦ_cont hα1 hΦ_coer hx'.1
    have hstep1 : Fobj μ1 μ2 f (fun q1 => capAt y1 x.1 q1, p.2) ≤ Fobj μ1 μ2 f p := by
      refine Finset.sum_le_sum fun q1 hq1 => ?_
      exact mul_le_mul_of_nonneg_left
        (hy1_opt q1 (h1nn q1 hq1) (p.1 q1) (hp.1 q1 hq1)) (h1p.1 q1 hq1)
    -- Step 2: optimize coord 2 holding capAt y1 x.1 fixed
    let Ψ : ℝ → ℝ := fun u2 => μ1.expect (fun q1 => f (capAt y1 x.1 q1, u2))
    have hΨ_conv : ConvexOn ℝ (Set.Ici 0) Ψ := by
      refine ⟨convex_Ici 0, fun u hu v hv a b ha hb hab => ?_⟩
      simp only [Ψ, FinLaw.expect, smul_eq_mul, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun q1 hq1 => ?_
      have h1 : 0 ≤ capAt y1 x.1 q1 := le_trans hx'.1 (inCap_le_left (capAt_inCap hy1 (h1nn q1 hq1)))
      have hc := hf.1.2 ((mem_orthant_iff (capAt y1 x.1 q1, u)).2 ⟨h1, hu⟩)
        ((mem_orthant_iff (capAt y1 x.1 q1, v)).2 ⟨h1, hv⟩) ha hb hab
      have hpt : a • ((capAt y1 x.1 q1, u) : Vec) + b • (capAt y1 x.1 q1, v) =
          (capAt y1 x.1 q1, a * u + b * v) := by
        ext <;> simp [smul_eq_mul]
        linear_combination hab * capAt y1 x.1 q1
      rw [hpt] at hc
      simp only [smul_eq_mul] at hc
      nlinarith [h1p.1 q1 hq1]
    have hΨ_cont : ContinuousOn Ψ (Set.Ici 0) := by
      simp only [Ψ, FinLaw.expect]
      refine continuousOn_finsetSum _ fun q1 hq1 => continuousOn_const.mul ?_
      have h1 : 0 ≤ capAt y1 x.1 q1 := le_trans hx'.1 (inCap_le_left (capAt_inCap hy1 (h1nn q1 hq1)))
      exact hf.2.1.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun u hu => (mem_orthant_iff _).2 ⟨h1, hu⟩)
    have hΨ_coer : ∀ u : ℝ, 0 ≤ u → α2 * u + C ≤ Ψ u := by
      intro u hu
      calc α2 * u + C = μ1.expect (fun _ => α2 * u + C) := by
            simp [FinLaw.expect, ← Finset.sum_mul, h1p.2]
        _ ≤ Ψ u := by
            refine Finset.sum_le_sum fun q1 hq1 => ?_
            have h1 : 0 ≤ capAt y1 x.1 q1 :=
              le_trans hx'.1 (inCap_le_left (capAt_inCap hy1 (h1nn q1 hq1)))
            have hfu := hcoer (capAt y1 x.1 q1, u) ((mem_orthant_iff _).2 ⟨h1, hu⟩)
            have hle : α2 * u + C ≤ f (capAt y1 x.1 q1, u) := by nlinarith
            exact mul_le_mul_of_nonneg_left hle (h1p.1 q1 hq1)
    obtain ⟨y2, hy2, hy2_opt⟩ := oneD_cap_opt hΨ_conv hΨ_cont hα2 hΨ_coer hx'.2
    have hswap : ∀ w2 : WithTop ℝ → ℝ,
        Fobj μ1 μ2 f (fun q1 => capAt y1 x.1 q1, w2) = μ2.expect (fun q2 => Ψ (w2 q2)) := by
      intro w2
      simp only [Fobj, Ψ, FinLaw.expect, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q2 _ => Finset.sum_congr rfl fun q1 _ => ?_
      ring
    have hstep2 : Gfun (y1, y2) ≤ Fobj μ1 μ2 f (fun q1 => capAt y1 x.1 q1, p.2) := by
      change Fobj μ1 μ2 f (fun q1 => capAt y1 x.1 q1, fun q2 => capAt y2 x.2 q2) ≤ _
      rw [hswap, hswap]
      refine Finset.sum_le_sum fun q2 hq2 => ?_
      exact mul_le_mul_of_nonneg_left
        (hy2_opt q2 (h2nn q2 hq2) (p.2 q2) (hp.2 q2 hq2)) (h2p.1 q2 hq2)
    have hle_G : sInf (Gfun '' {y : Vec | x ≤ y}) ≤ Gfun (y1, y2) :=
      csInf_le hG_bdd ⟨(y1, y2), ⟨hy1, hy2⟩, rfl⟩
    linarith
  · refine le_csInf hG_ne ?_
    rintro _ ⟨y, hy, rfl⟩
    exact csInf_le hB_bdd ⟨(fun q1 => capAt y.1 x.1 q1, fun q2 => capAt y.2 x.2 q2),
      ⟨fun q1 hq1 => capAt_inCap hy.1 (h1nn q1 hq1),
       fun q2 hq2 => capAt_inCap hy.2 (h2nn q2 hq2)⟩, rfl⟩

private lemma Vbox_convexOn {μ1 μ2 : FinLaw (WithTop ℝ)} {f : Vec → ℝ}
    (h1p : μ1.IsProb) (h2p : μ2.IsProb)
    (h1nn : ∀ q ∈ μ1.supp, (0 : WithTop ℝ) ≤ q)
    (h2nn : ∀ q ∈ μ2.supp, (0 : WithTop ℝ) ≤ q)
    (hf : Shape f) {α1 α2 C : ℝ} (hα1 : 0 < α1) (hα2 : 0 < α2)
    (hcoer : ∀ u ∈ orthant, α1 * u.1 + α2 * u.2 + C ≤ f u) :
    ConvexOn ℝ orthant (fun x => sInf (Fobj μ1 μ2 f '' Box μ1 μ2 x)) := by
  let Vb : Vec → ℝ := fun x => sInf (Fobj μ1 μ2 f '' Box μ1 μ2 x)
  refine ⟨orthant_convex, fun x hx y hy a b ha hb hab => ?_⟩
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · have hb1 : b = 1 := by linarith
    subst hb1; simp
  rcases eq_or_lt_of_le hb with rfl | hb_pos
  · have ha1 : a = 1 := by linarith
    subst ha1; simp
  have hxy_mem : a • x + b • y ∈ orthant := orthant_convex hx hy (le_of_lt ha_pos) (le_of_lt hb_pos) hab
  have hbdd := Fobj_bddBelow h1p h2p hα1 hα2 hcoer hxy_mem
  have hpair : ∀ px ∈ Box μ1 μ2 x, ∀ py ∈ Box μ1 μ2 y,
      Vb (a • x + b • y) ≤ a * Fobj μ1 μ2 f px + b * Fobj μ1 μ2 f py := by
    intro px hpx py hpy
    let pm := (fun q1 => a * px.1 q1 + b * py.1 q1, fun q2 => a * px.2 q2 + b * py.2 q2)
    have hpm_mem : pm ∈ Box μ1 μ2 (a • x + b • y) := by
      refine ⟨fun q1 hq1 => ?_, fun q2 hq2 => ?_⟩
      · have h1 := hpx.1 q1 hq1; have h2 := hpy.1 q1 hq1
        cases q1 with
        | top => simp only [inCap, pm, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at h1 h2 ⊢; nlinarith
        | coe r =>
          simp only [inCap, pm, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at h1 h2 ⊢
          exact ⟨by nlinarith, by nlinarith⟩
      · have h1 := hpx.2 q2 hq2; have h2 := hpy.2 q2 hq2
        cases q2 with
        | top => simp only [inCap, pm, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at h1 h2 ⊢; nlinarith
        | coe r =>
          simp only [inCap, pm, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at h1 h2 ⊢
          exact ⟨by nlinarith, by nlinarith⟩
    have hF_le : Fobj μ1 μ2 f pm ≤ a * Fobj μ1 μ2 f px + b * Fobj μ1 μ2 f py := by
      simp only [Fobj, FinLaw.expect, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun q1 hq1 => ?_
      rw [← Finset.sum_add_distrib]
      have hinner :
          ∑ q2 ∈ μ2.supp, μ2.weight q2 * f (pm.1 q1, pm.2 q2) ≤
            ∑ q2 ∈ μ2.supp, (a * (μ2.weight q2 * f (px.1 q1, px.2 q2)) +
              b * (μ2.weight q2 * f (py.1 q1, py.2 q2))) := by
        refine Finset.sum_le_sum fun q2 hq2 => ?_
        have hx' := (mem_orthant_iff x).1 hx
        have hy' := (mem_orthant_iff y).1 hy
        have hpx_mem : (px.1 q1, px.2 q2) ∈ orthant :=
          (mem_orthant_iff _).2 ⟨le_trans hx'.1 (inCap_le_left (hpx.1 q1 hq1)),
            le_trans hx'.2 (inCap_le_left (hpx.2 q2 hq2))⟩
        have hpy_mem : (py.1 q1, py.2 q2) ∈ orthant :=
          (mem_orthant_iff _).2 ⟨le_trans hy'.1 (inCap_le_left (hpy.1 q1 hq1)),
            le_trans hy'.2 (inCap_le_left (hpy.2 q2 hq2))⟩
        have hc := hf.1.2 hpx_mem hpy_mem (le_of_lt ha_pos) (le_of_lt hb_pos) hab
        have hpt : a • ((px.1 q1, px.2 q2) : Vec) + b • (py.1 q1, py.2 q2) = (pm.1 q1, pm.2 q2) := by
          ext <;> simp [pm, smul_eq_mul]
        rw [hpt] at hc
        simp only [smul_eq_mul] at hc
        nlinarith [h2p.1 q2 hq2]
      have hmul := mul_le_mul_of_nonneg_left hinner (h1p.1 q1 hq1)
      calc ∑ q2 ∈ μ2.supp, μ1.weight q1 * (μ2.weight q2 * f (pm.1 q1, pm.2 q2))
          = μ1.weight q1 * ∑ q2 ∈ μ2.supp, μ2.weight q2 * f (pm.1 q1, pm.2 q2) :=
              (Finset.mul_sum _ _ _).symm
        _ ≤ μ1.weight q1 * ∑ q2 ∈ μ2.supp, (a * (μ2.weight q2 * f (px.1 q1, px.2 q2)) +
              b * (μ2.weight q2 * f (py.1 q1, py.2 q2))) := hmul
        _ = ∑ q2 ∈ μ2.supp, (a * (μ1.weight q1 * (μ2.weight q2 * f (px.1 q1, px.2 q2))) +
              b * (μ1.weight q1 * (μ2.weight q2 * f (py.1 q1, py.2 q2)))) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q2 _ => by ring
    exact le_trans (csInf_le hbdd ⟨pm, hpm_mem, rfl⟩) hF_le
  have hstep1 : ∀ py ∈ Box μ1 μ2 y, Vb (a • x + b • y) ≤ a * Vb x + b * Fobj μ1 μ2 f py := by
    intro py hpy
    have hle : (Vb (a • x + b • y) - b * Fobj μ1 μ2 f py) / a ≤ Vb x := by
      refine le_csInf ((Box_nonempty h1nn h2nn x).image _) ?_
      rintro _ ⟨px, hpx, rfl⟩
      rw [div_le_iff₀ ha_pos]
      linarith [hpair px hpx py hpy]
    rw [div_le_iff₀ ha_pos] at hle
    linarith
  have hstep2 : (Vb (a • x + b • y) - a * Vb x) / b ≤ Vb y := by
    refine le_csInf ((Box_nonempty h1nn h2nn y).image _) ?_
    rintro _ ⟨py, hpy, rfl⟩
    rw [div_le_iff₀ hb_pos]
    linarith [hstep1 py hpy]
  rw [div_le_iff₀ hb_pos] at hstep2
  simp only [smul_eq_mul]
  linarith

private lemma Vbox_supermodularOn {μ1 μ2 : FinLaw (WithTop ℝ)} {f : Vec → ℝ}
    (h1p : μ1.IsProb) (h2p : μ2.IsProb)
    (h1nn : ∀ q ∈ μ1.supp, (0 : WithTop ℝ) ≤ q)
    (h2nn : ∀ q ∈ μ2.supp, (0 : WithTop ℝ) ≤ q)
    (hf : Shape f) {α1 α2 C : ℝ} (hα1 : 0 < α1) (hα2 : 0 < α2)
    (hcoer : ∀ u ∈ orthant, α1 * u.1 + α2 * u.2 + C ≤ f u) :
    SupermodularOn (fun x => sInf (Fobj μ1 μ2 f '' Box μ1 μ2 x)) orthant := by
  let Vb : Vec → ℝ := fun x => sInf (Fobj μ1 μ2 f '' Box μ1 μ2 x)
  have hrect : ∀ x1 x1' x2 x2' : ℝ, 0 ≤ x1 → x1 ≤ x1' → 0 ≤ x2 → x2 ≤ x2' →
      Vb (x1, x2') + Vb (x1', x2) ≤ Vb (x1, x2) + Vb (x1', x2') := by
    intro x1 x1' x2 x2' hx1 hx1' hx2 hx2'
    have hA_mem : ((x1, x2') : Vec) ∈ orthant := (mem_orthant_iff _).2 ⟨hx1, by linarith⟩
    have hB_mem : ((x1', x2) : Vec) ∈ orthant := (mem_orthant_iff _).2 ⟨by linarith, hx2⟩
    have hbddA := Fobj_bddBelow h1p h2p hα1 hα2 hcoer hA_mem
    have hbddB := Fobj_bddBelow h1p h2p hα1 hα2 hcoer hB_mem
    have hpair : ∀ pL ∈ Box μ1 μ2 (x1, x2), ∀ pH ∈ Box μ1 μ2 (x1', x2'),
        Vb (x1, x2') + Vb (x1', x2) ≤ Fobj μ1 μ2 f pL + Fobj μ1 μ2 f pH := by
      intro pL hpL pH hpH
      let pA := (fun q1 => min (pL.1 q1) (pH.1 q1), fun q2 => max (pL.2 q2) (pH.2 q2))
      let pB := (fun q1 => max (pL.1 q1) (pH.1 q1), fun q2 => min (pL.2 q2) (pH.2 q2))
      have hpA_mem : pA ∈ Box μ1 μ2 (x1, x2') := by
        refine ⟨fun q1 hq1 => ?_, fun q2 hq2 => ?_⟩
        · have hL := hpL.1 q1 hq1; have hH := hpH.1 q1 hq1
          cases q1 with
          | top => exact le_min hL (le_trans hx1' hH)
          | coe r => exact ⟨le_min hL.1 (le_trans hx1' hH.1), le_trans (min_le_left _ _) hL.2⟩
        · have hL := hpL.2 q2 hq2; have hH := hpH.2 q2 hq2
          cases q2 with
          | top => exact le_trans hH (le_max_right _ _)
          | coe r => exact ⟨le_trans hH.1 (le_max_right _ _), max_le (by linarith [hL.2]) hH.2⟩
      have hpB_mem : pB ∈ Box μ1 μ2 (x1', x2) := by
        refine ⟨fun q1 hq1 => ?_, fun q2 hq2 => ?_⟩
        · have hL := hpL.1 q1 hq1; have hH := hpH.1 q1 hq1
          cases q1 with
          | top => exact le_trans hH (le_max_right _ _)
          | coe r => exact ⟨le_trans hH.1 (le_max_right _ _), max_le (by linarith [hL.2]) hH.2⟩
        · have hL := hpL.2 q2 hq2; have hH := hpH.2 q2 hq2
          cases q2 with
          | top => exact le_min hL (le_trans hx2' hH)
          | coe r => exact ⟨le_min hL.1 (le_trans hx2' hH.1), le_trans (min_le_left _ _) hL.2⟩
      have hF_le : Fobj μ1 μ2 f pA + Fobj μ1 μ2 f pB ≤ Fobj μ1 μ2 f pL + Fobj μ1 μ2 f pH := by
        simp only [Fobj, FinLaw.expect]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun q1 hq1 => ?_
        rw [← mul_add, ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ (h1p.1 q1 hq1)
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun q2 hq2 => ?_
        rw [← mul_add, ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ (h2p.1 q2 hq2)
        exact supermodular_flip_pair hf.2.2
          (le_trans hx1 (inCap_le_left (hpL.1 q1 hq1)))
          (le_trans (by linarith) (inCap_le_left (hpH.1 q1 hq1)))
          (le_trans hx2 (inCap_le_left (hpL.2 q2 hq2)))
          (le_trans (by linarith) (inCap_le_left (hpH.2 q2 hq2)))
      have hleA : Vb (x1, x2') ≤ Fobj μ1 μ2 f pA := csInf_le hbddA ⟨pA, hpA_mem, rfl⟩
      have hleB : Vb (x1', x2) ≤ Fobj μ1 μ2 f pB := csInf_le hbddB ⟨pB, hpB_mem, rfl⟩
      linarith
    have hstep1 : ∀ pH ∈ Box μ1 μ2 (x1', x2'),
        Vb (x1, x2') + Vb (x1', x2) - Fobj μ1 μ2 f pH ≤ Vb (x1, x2) := by
      intro pH hpH
      refine le_csInf ((Box_nonempty h1nn h2nn (x1, x2)).image _) ?_
      rintro _ ⟨pL, hpL, rfl⟩
      linarith [hpair pL hpL pH hpH]
    have hstep2 : Vb (x1, x2') + Vb (x1', x2) - Vb (x1, x2) ≤ Vb (x1', x2') := by
      refine le_csInf ((Box_nonempty h1nn h2nn (x1', x2')).image _) ?_
      rintro _ ⟨pH, hpH, rfl⟩
      linarith [hstep1 pH hpH]
    linarith
  intro x hx y hy
  have hx' := (mem_orthant_iff x).1 hx
  have hy' := (mem_orthant_iff y).1 hy
  rcases le_total x.1 y.1 with h1 | h1 <;> rcases le_total x.2 y.2 with h2 | h2
  · have hsup : x ⊔ y = y := by ext <;> [simp [max_eq_right h1]; simp [max_eq_right h2]]
    have hinf : x ⊓ y = x := by ext <;> [simp [min_eq_left h1]; simp [min_eq_left h2]]
    rw [hsup, hinf, add_comm]
  · have hsup : x ⊔ y = (y.1, x.2) := by ext <;> [simp [max_eq_right h1]; simp [max_eq_left h2]]
    have hinf : x ⊓ y = (x.1, y.2) := by ext <;> [simp [min_eq_left h1]; simp [min_eq_right h2]]
    rw [hsup, hinf]
    have := hrect x.1 y.1 y.2 x.2 hx'.1 h1 hy'.2 h2
    dsimp only [Vb] at this
    simp only [Prod.eta] at this
    linarith
  · have hsup : x ⊔ y = (x.1, y.2) := by ext <;> [simp [max_eq_left h1]; simp [max_eq_right h2]]
    have hinf : x ⊓ y = (y.1, x.2) := by ext <;> [simp [min_eq_right h1]; simp [min_eq_left h2]]
    rw [hsup, hinf]
    have := hrect y.1 x.1 x.2 y.2 hy'.1 h1 hx'.2 h2
    dsimp only [Vb] at this
    simp only [Prod.eta] at this
    linarith
  · have hsup : x ⊔ y = x := by ext <;> [simp [max_eq_left h1]; simp [max_eq_left h2]]
    have hinf : x ⊓ y = y := by ext <;> [simp [min_eq_right h1]; simp [min_eq_right h2]]
    rw [hsup, hinf]

private lemma Vbox_continuousOn {μ1 μ2 : FinLaw (WithTop ℝ)} {f : Vec → ℝ}
    (h1p : μ1.IsProb) (h2p : μ2.IsProb)
    (h1nn : ∀ q ∈ μ1.supp, (0 : WithTop ℝ) ≤ q)
    (h2nn : ∀ q ∈ μ2.supp, (0 : WithTop ℝ) ≤ q)
    (hf : Shape f) {α1 α2 C : ℝ} (hα1 : 0 < α1) (hα2 : 0 < α2)
    (hcoer : ∀ u ∈ orthant, α1 * u.1 + α2 * u.2 + C ≤ f u) :
    ContinuousOn (fun x => sInf (Fobj μ1 μ2 f '' Box μ1 μ2 x)) orthant := by
  let Vb : Vec → ℝ := fun x => sInf (Fobj μ1 μ2 f '' Box μ1 μ2 x)
  intro x0 hx0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hx0' := (mem_orthant_iff x0).1 hx0
  let B0 : Set Vec := Set.Icc (0 : ℝ) (x0.1 + 1) ×ˢ Set.Icc (0 : ℝ) (x0.2 + 1)
  have hB0_compact : IsCompact B0 := isCompact_Icc.prod isCompact_Icc
  have hB0_sub : B0 ⊆ orthant := fun u hu => (mem_orthant_iff u).2 ⟨hu.1.1, hu.2.1⟩
  have hB0_ne : B0.Nonempty := ⟨x0, ⟨hx0'.1, by linarith⟩, ⟨hx0'.2, by linarith⟩⟩
  obtain ⟨zmax, _, hzmax⟩ := hB0_compact.exists_isMaxOn hB0_ne (hf.2.1.mono hB0_sub)
  let M0 := f zmax
  let R1 : ℝ := ∑ q1 ∈ μ1.supp, if 0 < μ1.weight q1 then max 0 ((M0 + 1 - C) / (α1 * μ1.weight q1)) else 0
  let R2 : ℝ := ∑ q2 ∈ μ2.supp, if 0 < μ2.weight q2 then max 0 ((M0 + 1 - C) / (α2 * μ2.weight q2)) else 0
  let R : ℝ := max (max R1 (x0.1 + 1)) (max R2 (x0.2 + 1))
  let K : Set Vec := Set.Icc (0 : ℝ) (R + 1) ×ˢ Set.Icc (0 : ℝ) (R + 1)
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hK_sub : K ⊆ orthant := fun u hu => (mem_orthant_iff u).2 ⟨hu.1.1, hu.2.1⟩
  have huc : UniformContinuousOn f K :=
    hK_compact.uniformContinuousOn_of_continuous (hf.2.1.mono hK_sub)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ0, hδ0, hδ0_prop⟩ := huc (ε / 2) (by linarith)
  have hshift : ∀ a b : Vec, a ∈ B0 → b ∈ B0 → dist b a < min 1 δ0 → Vb b < Vb a + ε := by
    intro a b haB hbB hdist
    have ha_orth : a ∈ orthant := hB0_sub haB
    have hb_orth : b ∈ orthant := hB0_sub hbB
    have ha' := (mem_orthant_iff a).1 ha_orth
    have hb' := (mem_orthant_iff b).1 hb_orth
    have hVa_le_M0 : Vb a ≤ M0 := by
      have hself : (fun _ => a.1, fun _ => a.2) ∈ Box μ1 μ2 a :=
        ⟨fun q1 hq1 => inCap_self (h1nn q1 hq1), fun q2 hq2 => inCap_self (h2nn q2 hq2)⟩
      have hFself : Fobj μ1 μ2 f (fun _ => a.1, fun _ => a.2) = f a := by
        simp [Fobj, FinLaw.expect, ← Finset.sum_mul, h1p.2, h2p.2]
      calc Vb a ≤ Fobj μ1 μ2 f (fun _ => a.1, fun _ => a.2) :=
            csInf_le (Fobj_bddBelow h1p h2p hα1 hα2 hcoer ha_orth) ⟨_, hself, rfl⟩
        _ = f a := hFself
        _ ≤ M0 := hzmax haB
    let η := min (ε / 2) 1
    have hη : 0 < η := lt_min (by linarith) zero_lt_one
    obtain ⟨_, ⟨p, hp, rfl⟩, hp_lt⟩ :=
      exists_lt_of_csInf_lt ((Box_nonempty h1nn h2nn a).image _) (lt_add_of_pos_right (Vb a) hη)
    have hFp_M : Fobj μ1 μ2 f p ≤ M0 + 1 := by
      have : η ≤ 1 := min_le_right _ _; linarith
    -- Clean zero-weight coordinates
    let pc : (WithTop ℝ → ℝ) × (WithTop ℝ → ℝ) :=
      (fun q1 => if 0 < μ1.weight q1 then p.1 q1 else a.1,
       fun q2 => if 0 < μ2.weight q2 then p.2 q2 else a.2)
    have hpc_Box : pc ∈ Box μ1 μ2 a := by
      refine ⟨fun q1 hq1 => ?_, fun q2 hq2 => ?_⟩
      · dsimp only [pc]; split_ifs
        · exact hp.1 q1 hq1
        · exact inCap_self (h1nn q1 hq1)
      · dsimp only [pc]; split_ifs
        · exact hp.2 q2 hq2
        · exact inCap_self (h2nn q2 hq2)
    have hFpc_eq : Fobj μ1 μ2 f pc = Fobj μ1 μ2 f p := by
      simp only [Fobj, FinLaw.expect]
      refine Finset.sum_congr rfl fun q1 hq1 => ?_
      by_cases hw1 : 0 < μ1.weight q1
      · congr 1
        refine Finset.sum_congr rfl fun q2 hq2 => ?_
        by_cases hw2 : 0 < μ2.weight q2
        · simp [pc, hw1, hw2]
        · have hw20 : μ2.weight q2 = 0 := le_antisymm (not_lt.1 hw2) (h2p.1 q2 hq2)
          simp [hw20]
      · have hw10 : μ1.weight q1 = 0 := le_antisymm (not_lt.1 hw1) (h1p.1 q1 hq1)
        simp [hw10]
    -- Bound pc coordinates by R
    have hpc1_le : ∀ q1 ∈ μ1.supp, pc.1 q1 ≤ R := by
      intro q1 hq1
      dsimp only [pc]; split_ifs with hw1
      · have hlb_all : ∀ q ∈ μ1.supp, α1 * p.1 q + C ≤ μ2.expect (fun q2 => f (p.1 q, p.2 q2)) := by
          intro q hq
          have h1 : 0 ≤ p.1 q := le_trans ha'.1 (inCap_le_left (hp.1 q hq))
          calc α1 * p.1 q + C = μ2.expect (fun _ => α1 * p.1 q + C) := by
                simp [FinLaw.expect, ← Finset.sum_mul, h2p.2]
            _ ≤ μ2.expect (fun q2 => f (p.1 q, p.2 q2)) := by
                refine Finset.sum_le_sum fun q2 hq2 => ?_
                have h2 : 0 ≤ p.2 q2 := le_trans ha'.2 (inCap_le_left (hp.2 q2 hq2))
                have hf0 := hcoer (p.1 q, p.2 q2) ((mem_orthant_iff _).2 ⟨h1, h2⟩)
                exact mul_le_mul_of_nonneg_left (by nlinarith) (h2p.1 q2 hq2)
        have hsum_lb : C + α1 * ∑ q ∈ μ1.supp, μ1.weight q * p.1 q ≤ Fobj μ1 μ2 f p := by
          calc C + α1 * ∑ q ∈ μ1.supp, μ1.weight q * p.1 q
              = ∑ q ∈ μ1.supp, μ1.weight q * (α1 * p.1 q + C) := by
                simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, h1p.2, one_mul,
                  Finset.mul_sum]
                rw [add_comm]; congr 1
                refine Finset.sum_congr rfl fun q _ => by ring
            _ ≤ Fobj μ1 μ2 f p := Finset.sum_le_sum fun q hq =>
                mul_le_mul_of_nonneg_left (hlb_all q hq) (h1p.1 q hq)
        have hterm_le : μ1.weight q1 * p.1 q1 ≤ ∑ q ∈ μ1.supp, μ1.weight q * p.1 q :=
          Finset.single_le_sum (fun q hq => mul_nonneg (h1p.1 q hq)
            (le_trans ha'.1 (inCap_le_left (hp.1 q hq)))) hq1
        have hp1_bd : p.1 q1 ≤ (M0 + 1 - C) / (α1 * μ1.weight q1) := by
          rw [le_div_iff₀ (mul_pos hα1 hw1)]
          nlinarith
        have hterm_R1 : (if 0 < μ1.weight q1 then max 0 ((M0 + 1 - C) / (α1 * μ1.weight q1)) else 0) ≤ R1 :=
          Finset.single_le_sum (f := fun q => if 0 < μ1.weight q then max 0 ((M0 + 1 - C) / (α1 * μ1.weight q)) else 0)
            (fun q _ => by split_ifs <;> [exact le_max_left _ _; exact le_rfl]) hq1
        rw [if_pos hw1] at hterm_R1
        exact le_trans hp1_bd (le_trans (le_max_right _ _)
          (le_trans hterm_R1 (le_trans (le_max_left _ _) (le_max_left _ _))))
      · exact le_trans haB.1.2 (le_trans (le_max_right _ _) (le_max_left _ _))
    have hpc2_le : ∀ q2 ∈ μ2.supp, pc.2 q2 ≤ R := by
      intro q2 hq2
      dsimp only [pc]; split_ifs with hw2
      · have hswap : Fobj μ1 μ2 f p = μ2.expect (fun q => μ1.expect (fun q1 => f (p.1 q1, p.2 q))) := by
          simp only [Fobj, FinLaw.expect, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q1 _ => by ring
        have hlb_all : ∀ q ∈ μ2.supp, α2 * p.2 q + C ≤ μ1.expect (fun q1 => f (p.1 q1, p.2 q)) := by
          intro q hq
          have h2 : 0 ≤ p.2 q := le_trans ha'.2 (inCap_le_left (hp.2 q hq))
          calc α2 * p.2 q + C = μ1.expect (fun _ => α2 * p.2 q + C) := by
                simp [FinLaw.expect, ← Finset.sum_mul, h1p.2]
            _ ≤ μ1.expect (fun q1 => f (p.1 q1, p.2 q)) := by
                refine Finset.sum_le_sum fun q1 hq1 => ?_
                have h1 : 0 ≤ p.1 q1 := le_trans ha'.1 (inCap_le_left (hp.1 q1 hq1))
                have hf0 := hcoer (p.1 q1, p.2 q) ((mem_orthant_iff _).2 ⟨h1, h2⟩)
                exact mul_le_mul_of_nonneg_left (by nlinarith) (h1p.1 q1 hq1)
        have hsum_lb : C + α2 * ∑ q ∈ μ2.supp, μ2.weight q * p.2 q ≤ Fobj μ1 μ2 f p := by
          rw [hswap]
          calc C + α2 * ∑ q ∈ μ2.supp, μ2.weight q * p.2 q
              = ∑ q ∈ μ2.supp, μ2.weight q * (α2 * p.2 q + C) := by
                simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, h2p.2, one_mul,
                  Finset.mul_sum]
                rw [add_comm]; congr 1
                refine Finset.sum_congr rfl fun q _ => by ring
            _ ≤ _ := Finset.sum_le_sum fun q hq =>
                mul_le_mul_of_nonneg_left (hlb_all q hq) (h2p.1 q hq)
        have hterm_le : μ2.weight q2 * p.2 q2 ≤ ∑ q ∈ μ2.supp, μ2.weight q * p.2 q :=
          Finset.single_le_sum (fun q hq => mul_nonneg (h2p.1 q hq)
            (le_trans ha'.2 (inCap_le_left (hp.2 q hq)))) hq2
        have hp2_bd : p.2 q2 ≤ (M0 + 1 - C) / (α2 * μ2.weight q2) := by
          rw [le_div_iff₀ (mul_pos hα2 hw2)]
          nlinarith
        have hterm_R2 : (if 0 < μ2.weight q2 then max 0 ((M0 + 1 - C) / (α2 * μ2.weight q2)) else 0) ≤ R2 :=
          Finset.single_le_sum (f := fun q => if 0 < μ2.weight q then max 0 ((M0 + 1 - C) / (α2 * μ2.weight q)) else 0)
            (fun q _ => by split_ifs <;> [exact le_max_left _ _; exact le_rfl]) hq2
        rw [if_pos hw2] at hterm_R2
        exact le_trans hp2_bd (le_trans (le_max_right _ _)
          (le_trans hterm_R2 (le_trans (le_max_left _ _) (le_max_right _ _))))
      · exact le_trans haB.2.2 (le_trans (le_max_right _ _) (le_max_right _ _))
    -- Shift pc by (b - a)
    let pb : (WithTop ℝ → ℝ) × (WithTop ℝ → ℝ) :=
      (fun q1 => pc.1 q1 + (b.1 - a.1), fun q2 => pc.2 q2 + (b.2 - a.2))
    have hpb_Box : pb ∈ Box μ1 μ2 b := by
      refine ⟨fun q1 hq1 => ?_, fun q2 hq2 => ?_⟩
      · have h := hpc_Box.1 q1 hq1
        cases q1 with
        | top => dsimp only [inCap, pb] at h ⊢; linarith
        | coe r => dsimp only [inCap, pb] at h ⊢; exact ⟨by linarith, by linarith⟩
      · have h := hpc_Box.2 q2 hq2
        cases q2 with
        | top => dsimp only [inCap, pb] at h ⊢; linarith
        | coe r => dsimp only [inCap, pb] at h ⊢; exact ⟨by linarith, by linarith⟩
    have hd1 : dist b a < 1 := lt_of_lt_of_le hdist (min_le_left _ _)
    have hd0 : dist b a < δ0 := lt_of_lt_of_le hdist (min_le_right _ _)
    have hba_le : b.1 - a.1 ≤ 1 ∧ b.2 - a.2 ≤ 1 := by
      rw [Prod.dist_eq] at hd1
      have h1 : |b.1 - a.1| < 1 := by simpa [Real.dist_eq] using lt_of_le_of_lt (le_max_left _ _) hd1
      have h2 : |b.2 - a.2| < 1 := by simpa [Real.dist_eq] using lt_of_le_of_lt (le_max_right _ _) hd1
      exact ⟨by linarith [(abs_lt.1 h1).2], by linarith [(abs_lt.1 h2).2]⟩
    have hF_diff : Fobj μ1 μ2 f pb ≤ Fobj μ1 μ2 f pc + ε / 2 := by
      have hsum_eps : Fobj μ1 μ2 f pc + ε / 2 =
          μ1.expect (fun q1 => μ2.expect (fun q2 => f (pc.1 q1, pc.2 q2) + ε / 2)) := by
        simp only [Fobj, FinLaw.expect, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, h1p.2, h2p.2, one_mul]
      rw [hsum_eps]
      refine Finset.sum_le_sum fun q1 hq1 => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun q2 hq2 => mul_le_mul_of_nonneg_left ?_ (h2p.1 q2 hq2)) (h1p.1 q1 hq1)
      have hpc_K : (pc.1 q1, pc.2 q2) ∈ K :=
        ⟨⟨le_trans ha'.1 (inCap_le_left (hpc_Box.1 q1 hq1)), by linarith [hpc1_le q1 hq1]⟩,
         ⟨le_trans ha'.2 (inCap_le_left (hpc_Box.2 q2 hq2)), by linarith [hpc2_le q2 hq2]⟩⟩
      have hpb_K : (pb.1 q1, pb.2 q2) ∈ K :=
        ⟨⟨le_trans hb'.1 (inCap_le_left (hpb_Box.1 q1 hq1)), by linarith [hpc1_le q1 hq1]⟩,
         ⟨le_trans hb'.2 (inCap_le_left (hpb_Box.2 q2 hq2)), by linarith [hpc2_le q2 hq2]⟩⟩
      have hdist_pt : dist (pb.1 q1, pb.2 q2) (pc.1 q1, pc.2 q2) < δ0 := by
        have heq : dist (pb.1 q1, pb.2 q2) (pc.1 q1, pc.2 q2) = dist b a := by
          simp [pb, Prod.dist_eq, Real.dist_eq]
        rw [heq]; exact hd0
      have hlt := hδ0_prop _ hpb_K _ hpc_K hdist_pt
      rw [Real.dist_eq, abs_lt] at hlt
      linarith
    have hVb_le : Vb b ≤ Fobj μ1 μ2 f pb :=
      csInf_le (Fobj_bddBelow h1p h2p hα1 hα2 hcoer hb_orth) ⟨pb, hpb_Box, rfl⟩
    have hη_le : η ≤ ε / 2 := min_le_left _ _
    linarith
  refine ⟨min 1 δ0, lt_min zero_lt_one hδ0, fun x hx hdist => ?_⟩
  have hd1 : dist x x0 < 1 := lt_of_lt_of_le hdist (min_le_left _ _)
  have hx' := (mem_orthant_iff x).1 hx
  have hx0_B0 : x0 ∈ B0 := ⟨⟨hx0'.1, by linarith⟩, ⟨hx0'.2, by linarith⟩⟩
  have hx_B0 : x ∈ B0 := by
    rw [Prod.dist_eq] at hd1
    have h1 : |x.1 - x0.1| < 1 := by simpa [Real.dist_eq] using lt_of_le_of_lt (le_max_left _ _) hd1
    have h2 : |x.2 - x0.2| < 1 := by simpa [Real.dist_eq] using lt_of_le_of_lt (le_max_right _ _) hd1
    exact ⟨⟨hx'.1, by linarith [(abs_lt.1 h1).2]⟩, ⟨hx'.2, by linarith [(abs_lt.1 h2).2]⟩⟩
  have h1 := hshift x0 x hx0_B0 hx_B0 hdist
  have h2 := hshift x x0 hx_B0 hx0_B0 (by rwa [dist_comm])
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

private lemma V_eq_Vstep (d : Data) (t : ℕ) (htT : t ≤ d.T) :
    V d t = Vstep d t (V d (t + 1)) := by
  have hk : d.T + 1 - t = (d.T - t) + 1 := by omega
  have htk : d.T - (d.T - t) = t := by omega
  have hk' : d.T - t = d.T + 1 - (t + 1) := by omega
  rw [V, hk, Vtg, htk, hk']; rfl

private lemma V_shape (d : Data) (hd : d.Standing) (t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ d.T) (hH : H d t) : Shape (V d t) := by
  have ⟨_, _, _, hper, _⟩ := hd
  obtain ⟨_, _, _, _, _, _, _, _, h1p, h2p, h1nn, h2nn⟩ := hper t ht htT
  have hGshape := Gbar_shape d hd t ht htT hH
  obtain ⟨α1, α2, C, hα1, hα2, hcoer⟩ := Gbar_coercive d hd t ht htT hH
  let Vb : Vec → ℝ := fun x => sInf (Fobj (d.qq1 t) (d.qq2 t) (Gbar d t) '' Box (d.qq1 t) (d.qq2 t) x)
  have hEq : ∀ x ∈ orthant, V d t x = Vb x := by
    intro x hx
    rw [V_eq_Vstep d t htT]
    exact V_eq_sInf_Box h1p h2p h1nn h2nn hGshape hα1 hα2 hcoer hx
  have hVb_conv := Vbox_convexOn h1p h2p h1nn h2nn hGshape hα1 hα2 hcoer
  have hVb_cont := Vbox_continuousOn h1p h2p h1nn h2nn hGshape hα1 hα2 hcoer
  have hVb_sm := Vbox_supermodularOn h1p h2p h1nn h2nn hGshape hα1 hα2 hcoer
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨orthant_convex, fun x hx y hy a b ha hb hab => ?_⟩
    rw [hEq _ (orthant_convex hx hy ha hb hab), hEq x hx, hEq y hy]
    exact hVb_conv.2 hx hy ha hb hab
  · exact hVb_cont.congr hEq
  · intro x hx y hy
    have hsup_mem : x ⊔ y ∈ orthant :=
      (mem_orthant_iff _).2 ⟨le_trans ((mem_orthant_iff x).1 hx).1 (le_max_left _ _),
        le_trans ((mem_orthant_iff x).1 hx).2 (le_max_left _ _)⟩
    have hinf_mem : x ⊓ y ∈ orthant :=
      (mem_orthant_iff _).2 ⟨le_min ((mem_orthant_iff x).1 hx).1 ((mem_orthant_iff y).1 hy).1,
        le_min ((mem_orthant_iff x).1 hx).2 ((mem_orthant_iff y).1 hy).2⟩
    rw [hEq x hx, hEq y hy, hEq _ hsup_mem, hEq _ hinf_mem]
    exact hVb_sm hx hy

private lemma V_lowerGrowth (d : Data) (hd : d.Standing) (t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ d.T) (hH : H d t) :
    LowerGrowth (V d t) (d.c1 t) (d.c2 t) := by
  have ⟨_, ha1, _, hper, _⟩ := hd
  obtain ⟨hσ, he, hh1, hh2, hch1, hch2, _, _, h1p, h2p, h1nn, h2nn⟩ := hper t ht htT
  have hp : 0 < p d t := by unfold p; linarith
  have hV_lb : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x ∈ orthant,
      (d.c1 t - ε / 2) * x.1 + C ≤ V d t x ∧ (d.c2 t - ε / 2) * x.2 + C ≤ V d t x := by
    intro ε hε
    let ε' := min (ε / 2) (min (d.a1 * p d t) (min (d.c1 t + d.h1 t) (d.c2 t + d.h2 t)))
    have hε' : 0 < ε' := by positivity
    have hε'_a1 : ε' ≤ d.a1 * p d t := le_trans (min_le_right _ _) (min_le_left _ _)
    have hε'_e : ε' ≤ ε / 2 := min_le_left _ _
    have hε'_1 : ε' ≤ d.c1 t + d.h1 t :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hε'_2 : ε' ≤ d.c2 t + d.h2 t :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    obtain ⟨C, hC⟩ := Gbar_linear_lower d hd t ht htT hH hε' hε'_a1
    let b1 := d.c1 t + d.h1 t - ε'
    let b2 := d.c2 t + d.h2 t - ε'
    have hb1 : 0 ≤ b1 := by dsimp only [b1]; linarith
    have hb2 : 0 ≤ b2 := by dsimp only [b2]; linarith
    refine ⟨C, fun x hx => ?_⟩
    have hx' := (mem_orthant_iff x).1 hx
    have hmain : b1 * x.1 + b2 * x.2 + C ≤ V d t x := by
      rw [V_eq_Vstep d t htT]
      refine le_csInf ⟨G d t x x, x, Set.mem_ofPred.2 le_rfl, rfl⟩ ?_
      rintro _ ⟨y, hy, rfl⟩
      have hinner : ∀ q1 ∈ (d.qq1 t).supp,
          b1 * x.1 + b2 * x.2 + C ≤
            (d.qq2 t).expect (fun q2 => Gbar d t (capAt y.1 x.1 q1, capAt y.2 x.2 q2)) := by
        intro q1 hq1
        have h1 : x.1 ≤ capAt y.1 x.1 q1 := inCap_le_left (capAt_inCap hy.1 (h1nn q1 hq1))
        calc b1 * x.1 + b2 * x.2 + C = (d.qq2 t).expect (fun _ => b1 * x.1 + b2 * x.2 + C) := by
              simp [FinLaw.expect, ← Finset.sum_mul, h2p.2]
          _ ≤ _ := Finset.sum_le_sum fun q2 hq2 => by
              have h2 : x.2 ≤ capAt y.2 x.2 q2 := inCap_le_left (capAt_inCap hy.2 (h2nn q2 hq2))
              have hGb := hC (capAt y.1 x.1 q1, capAt y.2 x.2 q2)
                ((mem_orthant_iff _).2 ⟨le_trans hx'.1 h1, le_trans hx'.2 h2⟩)
              exact mul_le_mul_of_nonneg_left (by nlinarith) (h2p.1 q2 hq2)
      calc b1 * x.1 + b2 * x.2 + C = (d.qq1 t).expect (fun _ => b1 * x.1 + b2 * x.2 + C) := by
            simp [FinLaw.expect, ← Finset.sum_mul, h1p.2]
        _ ≤ G d t y x := Finset.sum_le_sum fun q1 hq1 =>
            mul_le_mul_of_nonneg_left (hinner q1 hq1) (h1p.1 q1 hq1)
    exact ⟨by nlinarith, by nlinarith⟩
  constructor
  · intro ε hε v hv
    obtain ⟨C, hC⟩ := hV_lb ε hε
    filter_upwards [eventually_gt_atTop (max 0 (2 * (-C) / ε))] with s hs
    have hs0 : 0 < s := lt_of_le_of_lt (le_max_left _ _) hs
    have hsC : 2 * (-C) / ε < s := lt_of_le_of_lt (le_max_right _ _) hs
    have h1 := (hC (s, v) ((mem_orthant_iff _).2 ⟨le_of_lt hs0, hv⟩)).1
    rw [le_div_iff₀ hs0]
    have : 2 * (-C) < s * ε := (div_lt_iff₀ hε).1 hsC
    nlinarith
  · intro ε hε v hv
    obtain ⟨C, hC⟩ := hV_lb ε hε
    filter_upwards [eventually_gt_atTop (max 0 (2 * (-C) / ε))] with s hs
    have hs0 : 0 < s := lt_of_le_of_lt (le_max_left _ _) hs
    have hsC : 2 * (-C) / ε < s := lt_of_le_of_lt (le_max_right _ _) hs
    have h2 := (hC (v, s) ((mem_orthant_iff _).2 ⟨hv, le_of_lt hs0⟩)).2
    rw [le_div_iff₀ hs0]
    have : 2 * (-C) < s * ε := (div_lt_iff₀ hε).1 hsC
    nlinarith

end RawBlending.UB.Lemma3d

open RawBlending.UB in
theorem solution (d : Data) (hd : d.Standing) (t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ d.T) (hH : H d t) : H d (t-1) := by
  have ht1 : t - 1 + 1 = t := Nat.sub_add_cancel ht
  unfold H
  rw [ht1]
  exact ⟨Lemma3d.V_shape d hd t ht htT hH, Lemma3d.V_lowerGrowth d hd t ht htT hH⟩
