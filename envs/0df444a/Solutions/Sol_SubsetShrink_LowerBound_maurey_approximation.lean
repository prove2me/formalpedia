-- Prove2me | solution 1 for SubsetShrink.LowerBound.maurey_approximation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T01:13:33.816895+00:00
-- url     : https://prove2.me/submissions/f7559492-0bd5-4408-b0bf-77973dc2ad96

import Mathlib
import Definitions.Def_SubsetShrink_LowerBound_Model

namespace SSLBmaurey

open SubsetShrink.LowerBound

/-- One averaging step of Maurey's empirical method. -/
theorem avg_step {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : ι → E) (π : ι → ℝ) (hπ : ∀ j, 0 ≤ π j) (hsum : ∑ j, π j = 1) (B : ℝ)
    (hB : ∀ j, ‖h j‖ ^ 2 ≤ B) (f : E) (hf : f = ∑ j, π j • h j) (w : E) :
    ∃ j, ‖w + (f - h j)‖ ^ 2 ≤ ‖w‖ ^ 2 + (B - ‖f‖ ^ 2) := by
  have hzero : ∑ j, π j • (f - h j) = 0 := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul, ← hf,
      sub_self]
  have e1 : ∀ j, π j * ‖w + (f - h j)‖ ^ 2 =
      π j * ‖w‖ ^ 2 + 2 * inner ℝ w (π j • (f - h j)) +
        (π j * ‖f‖ ^ 2 - 2 * inner ℝ f (π j • h j) + π j * ‖h j‖ ^ 2) := by
    intro j
    rw [norm_add_sq_real, norm_sub_sq_real, real_inner_smul_right, real_inner_smul_right,
      inner_sub_right]
    ring
  have hB' : ∑ j, π j * ‖h j‖ ^ 2 ≤ B := by
    calc ∑ j, π j * ‖h j‖ ^ 2 ≤ ∑ j, π j * B :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hB j) (hπ j))
      _ = B := by rw [← Finset.sum_mul, hsum, one_mul]
  have key : ∑ j, π j * ‖w + (f - h j)‖ ^ 2 ≤ ‖w‖ ^ 2 + (B - ‖f‖ ^ 2) := by
    simp_rw [e1]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← inner_sum, ← inner_sum,
      hzero, ← hf, ← Finset.sum_mul, ← Finset.sum_mul, hsum, inner_zero_right,
      real_inner_self_eq_norm_sq]
    linarith
  by_contra hc
  push_neg at hc
  obtain ⟨j0, hj0⟩ : ∃ j, 0 < π j := by
    by_contra hn
    push_neg at hn
    have : ∑ j, π j ≤ 0 := Finset.sum_nonpos (fun j _ => hn j)
    linarith
  have hpos : 0 < ∑ j, π j * (‖w + (f - h j)‖ ^ 2 - (‖w‖ ^ 2 + (B - ‖f‖ ^ 2))) := by
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (hπ j) (by linarith [hc j])
    · exact ⟨j0, Finset.mem_univ _, mul_pos hj0 (by linarith [hc j0])⟩
  have : ∑ j, π j * (‖w + (f - h j)‖ ^ 2 - (‖w‖ ^ 2 + (B - ‖f‖ ^ 2))) =
      ∑ j, π j * ‖w + (f - h j)‖ ^ 2 - (‖w‖ ^ 2 + (B - ‖f‖ ^ 2)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  linarith

/-- Maurey's empirical method: `m` atoms approximate `f` with `m²`-scaled error `≤ m (B − ‖f‖²)`. -/
theorem maurey_iter {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : ι → E) (π : ι → ℝ) (hπ : ∀ j, 0 ≤ π j) (hsum : ∑ j, π j = 1) (B : ℝ)
    (hB : ∀ j, ‖h j‖ ^ 2 ≤ B) (f : E) (hf : f = ∑ j, π j • h j) :
    ∀ m : ℕ, ∃ J : Fin m → ι, ‖(m : ℝ) • f - ∑ t, h (J t)‖ ^ 2 ≤ m * (B - ‖f‖ ^ 2) := by
  intro m
  induction m with
  | zero => exact ⟨Fin.elim0, by simp⟩
  | succ m ih =>
    obtain ⟨J, hJ⟩ := ih
    obtain ⟨j, hj⟩ := avg_step h π hπ hsum B hB f hf ((m : ℝ) • f - ∑ t, h (J t))
    refine ⟨Fin.snoc J j, ?_⟩
    have : ((m + 1 : ℕ) : ℝ) • f - ∑ t, h ((Fin.snoc J j : Fin (m + 1) → ι) t) =
        ((m : ℝ) • f - ∑ t, h (J t)) + (f - h j) := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [this]
    push_cast
    linarith

/-- The prediction map `β ↦ Xβ`, landing in Euclidean space. -/
noncomputable def Lmap {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) :
    (Fin p → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap ∘ₗ Matrix.mulVecLin X

theorem Lmap_normsq {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (x : Fin p → ℝ) :
    ‖Lmap X x‖ ^ 2 = ∑ i, (X.mulVec x i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem l0_le_of_supp {p : ℕ} (b : Fin p → ℝ) (A : Finset (Fin p))
    (h : ∀ j, b j ≠ 0 → j ∈ A) : l0 b ≤ A.card := by
  unfold l0 supp
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact h j hj

end SSLBmaurey

open SubsetShrink.LowerBound in
theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (βstar : Fin p → ℝ) (hX : SubsetShrink.Events.UnitCols X) (hk : 1 ≤ k) :
    ∃ βt : Fin p → ℝ, (l0 βt : ℝ) ≤ (k : ℝ) / 2 ∧
      ∑ i, (X.mulVec βstar i - X.mulVec βt i) ^ 2 ≤ 2 * SubsetShrink.Events.l1 βstar ^ 2 / k := by
  set R := SubsetShrink.Events.l1 βstar with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set L := SSLBmaurey.Lmap X
  have hsq : ∀ x y : Fin p → ℝ, ∑ i, (X.mulVec x i - X.mulVec y i) ^ 2 = ‖L x - L y‖ ^ 2 := by
    intro x y
    rw [← map_sub, SSLBmaurey.Lmap_normsq, Matrix.mulVec_sub]
    rfl
  have hl0zero : l0 (0 : Fin p → ℝ) = 0 := by simp [l0, supp]
  rcases eq_or_lt_of_le hR0 with hR0' | hRpos
  · -- `βstar = 0`
    have hβ : βstar = 0 := by
      funext j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (βstar j))).mp hR0'.symm j
        (Finset.mem_univ _)
      simpa using this
    refine ⟨0, by simp [hl0zero]; positivity, ?_⟩
    rw [hβ]; simp; positivity
  -- the atoms
  set s : Fin p → ℝ := fun j => if 0 ≤ βstar j then 1 else -1 with hs
  have hs2 : ∀ j, s j ^ 2 = 1 := by intro j; simp only [hs]; split_ifs <;> norm_num
  have habs : ∀ j, |βstar j| * s j = βstar j := by
    intro j; simp only [hs]; split_ifs with h
    · rw [abs_of_nonneg h, mul_one]
    · rw [abs_of_neg (lt_of_not_ge h)]; ring
  set π : Fin p → ℝ := fun j => |βstar j| / R with hπdef
  have hπ : ∀ j, 0 ≤ π j := fun j => div_nonneg (abs_nonneg _) hR0
  have hsum : ∑ j, π j = 1 := by
    simp only [hπdef, ← Finset.sum_div]
    rw [show ∑ j, |βstar j| = R from rfl, div_self hRpos.ne']
  set h : Fin p → EuclideanSpace ℝ (Fin n) := fun j => L (Pi.single j (R * s j)) with hhdef
  have hcol : ∀ j (c : ℝ), ‖L (Pi.single j c)‖ ^ 2 = c ^ 2 := by
    intro j c
    rw [SSLBmaurey.Lmap_normsq]
    have : ∀ i, X.mulVec (Pi.single j c) i = X i j * c := by
      intro i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    simp_rw [this, mul_pow, ← Finset.sum_mul, hX j, one_mul]
  have hB : ∀ j, ‖h j‖ ^ 2 ≤ R ^ 2 := by
    intro j; simp only [hhdef]; rw [hcol, mul_pow, hs2, mul_one]
  have hf : L βstar = ∑ j, π j • h j := by
    conv_lhs => rw [← Finset.univ_sum_single βstar]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp only [hhdef, ← map_smul]
    congr 1
    funext i
    by_cases hi : i = j
    · subst hi
      simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, hπdef]
      rw [show |βstar i| / R * (R * s i) = |βstar i| * s i by field_simp, habs]
    · simp [Pi.single_apply, hi]
  -- Maurey iterations
  have hit := SSLBmaurey.maurey_iter h π hπ hsum (R ^ 2) hB (L βstar) hf
  have hfB : ‖L βstar‖ ^ 2 ≤ R ^ 2 := by
    obtain ⟨J, hJ⟩ := hit 1
    have := norm_nonneg ((1 : ℕ) • L βstar - ∑ t, h (J t))
    have h0 : 0 ≤ ‖((1 : ℕ) : ℝ) • L βstar - ∑ t, h (J t)‖ ^ 2 := sq_nonneg _
    push_cast at hJ h0
    linarith
  set m := k / 2 with hm
  have hmk : (k : ℝ) ≤ 2 * m + 1 := by
    have : k ≤ 2 * m + 1 := by omega
    exact_mod_cast this
  have hm2 : (m : ℝ) ≤ (k : ℝ) / 2 := by
    have : 2 * m ≤ k := by omega
    have : (2 * m : ℝ) ≤ k := by exact_mod_cast this
    linarith
  set a := ‖L βstar‖ ^ 2 with ha
  by_cases hcase : ((m : ℝ) + 1) * a ≤ R ^ 2
  · refine ⟨0, by rw [hl0zero]; simp; positivity, ?_⟩
    rw [hsq, map_zero, sub_zero]
    rw [le_div_iff₀ hkpos]
    have : a * (k : ℝ) ≤ a * (2 * m + 1) := mul_le_mul_of_nonneg_left hmk (sq_nonneg _)
    nlinarith [sq_nonneg (‖L βstar‖)]
  push_neg at hcase
  have hmpos : 1 ≤ m := by
    by_contra hm0
    have : m = 0 := by omega
    rw [this] at hcase
    simp at hcase
    linarith
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  obtain ⟨J, hJ⟩ := hit m
  set b : Fin p → ℝ := ∑ t, Pi.single (J t) (R * s (J t)) with hb
  have hLb : L b = ∑ t, h (J t) := by rw [hb, map_sum]
  refine ⟨((m : ℝ)⁻¹) • b, ?_, ?_⟩
  · have hsupp : l0 (((m : ℝ)⁻¹) • b) ≤ (Finset.univ.image J).card := by
      apply SSLBmaurey.l0_le_of_supp
      intro j hj
      by_contra hjn
      apply hj
      simp only [hb, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [Finset.sum_eq_zero, mul_zero]
      intro t _
      have : J t ≠ j := fun he => hjn (by rw [← he]; exact Finset.mem_image_of_mem J (Finset.mem_univ t))
      simp [Pi.single_apply, Ne.symm this]
    have h2 : (Finset.univ.image J).card ≤ m := by
      calc (Finset.univ.image J).card ≤ Finset.univ.card := Finset.card_image_le
        _ = m := by simp
    have : (l0 (((m : ℝ)⁻¹) • b) : ℝ) ≤ m := by exact_mod_cast hsupp.trans h2
    linarith
  · rw [hsq, map_smul, hLb]
    have hmne : (m : ℝ) ≠ 0 := by positivity
    have e : L βstar - (m : ℝ)⁻¹ • ∑ t, h (J t) = (m : ℝ)⁻¹ • ((m : ℝ) • L βstar - ∑ t, h (J t)) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hmne, one_smul]
    rw [e, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    set E := ‖(m : ℝ) • L βstar - ∑ t, h (J t)‖ ^ 2
    have hmpos' : (0 : ℝ) < m := by linarith
    rw [le_div_iff₀ hkpos]
    -- E ≤ m (R² − a) and (m+1) a > R²
    have h1 : ((m : ℝ)⁻¹) ^ 2 * E ≤ (R ^ 2 - a) / m := by
      rw [inv_pow, ← div_eq_inv_mul, div_le_div_iff₀ (by positivity) hmpos']
      nlinarith
    have h2 : (R ^ 2 - a) / m ≤ R ^ 2 / (m + 1) := by
      rw [div_le_div_iff₀ hmpos' (by positivity)]
      nlinarith
    have h3 : R ^ 2 / (m + 1) * k ≤ 2 * R ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg R]
    calc ((m : ℝ)⁻¹) ^ 2 * E * k ≤ R ^ 2 / (m + 1) * k :=
          mul_le_mul_of_nonneg_right (h1.trans h2) hkpos.le
      _ ≤ 2 * R ^ 2 := h3
