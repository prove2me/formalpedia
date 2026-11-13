-- Prove2me | solution 1 for RestrictedAP.Counting.proposition_5_28
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:27:03.972345+00:00
-- url     : https://prove2.me/submissions/f6bf42d5-bcb5-4ced-8759-8832996fc57b

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions

section
open ComplexOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RestrictedAP.Counting.Dev.P528
open RestrictedAP.Counting Matrix

/-- A nonzero complex number is detected by a `ℚ`-linear functional. -/
lemma exists_rat_dual {x : ℂ} (hx : x ≠ 0) : ∃ ℓ : ℂ →ₗ[ℚ] ℚ, ℓ x ≠ 0 := by
  by_contra h
  push Not at h
  exact hx ((Module.forall_dual_apply_eq_zero_iff ℚ x).1 h)

lemma hasEmb_rat_of_complex {T : Type*} (S : Set (T × T × T)) :
    HasEmbedding ℂ S → HasEmbedding ℚ S := by
  rintro ⟨σ, γ, φ, hnc, hrel⟩
  have hrel' : ∀ ℓ : ℂ →ₗ[ℚ] ℚ, ∀ t ∈ S, ℓ (σ t.1) + ℓ (γ t.2.1) + ℓ (φ t.2.2) = 0 := by
    intro ℓ t ht
    rw [← map_add, ← map_add, hrel t ht, map_zero]
  by_cases h1 : ∀ a a', σ a = σ a'
  · by_cases h2 : ∀ b b', γ b = γ b'
    · have h3 : ¬ ∀ c c', φ c = φ c' := fun h3 => hnc ⟨h1, h2, h3⟩
      push Not at h3
      obtain ⟨c, c', hc⟩ := h3
      obtain ⟨ℓ, hℓ⟩ := exists_rat_dual (sub_ne_zero.2 hc)
      refine ⟨ℓ ∘ σ, ℓ ∘ γ, ℓ ∘ φ, ?_, hrel' ℓ⟩
      rintro ⟨-, -, h⟩
      exact hℓ (by rw [map_sub, sub_eq_zero]; exact h c c')
    · push Not at h2
      obtain ⟨c, c', hc⟩ := h2
      obtain ⟨ℓ, hℓ⟩ := exists_rat_dual (sub_ne_zero.2 hc)
      refine ⟨ℓ ∘ σ, ℓ ∘ γ, ℓ ∘ φ, ?_, hrel' ℓ⟩
      rintro ⟨-, h, -⟩
      exact hℓ (by rw [map_sub, sub_eq_zero]; exact h c c')
  · push Not at h1
    obtain ⟨c, c', hc⟩ := h1
    obtain ⟨ℓ, hℓ⟩ := exists_rat_dual (sub_ne_zero.2 hc)
    refine ⟨ℓ ∘ σ, ℓ ∘ γ, ℓ ∘ φ, ?_, hrel' ℓ⟩
    rintro ⟨h, -, -⟩
    exact hℓ (by rw [map_sub, sub_eq_zero]; exact h c c')

/-- A common denominator for a finite set of rationals. -/
lemma common_den (s : Finset ℚ) : ∃ N : ℕ, N ≠ 0 ∧ ∀ q ∈ s, ∃ z : ℤ, (z : ℚ) = N * q := by
  refine ⟨∏ q ∈ s, q.den, Finset.prod_ne_zero_iff.2 fun q _ => q.den_nz, fun q hq => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun q : ℚ => q.den) hq
  refine ⟨k * q.num, ?_⟩
  rw [hk]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

lemma hasEmb_int_of_rat {T : Type*} [Fintype T] (S : Set (T × T × T)) :
    HasEmbedding ℚ S → HasEmbedding ℤ S := by
  classical
  rintro ⟨σ, γ, φ, hnc, hrel⟩
  obtain ⟨N, hN, hz⟩ := common_den
    (Finset.univ.image σ ∪ Finset.univ.image γ ∪ Finset.univ.image φ)
  have hfl : ∀ q, (q ∈ Finset.univ.image σ ∪ Finset.univ.image γ ∪ Finset.univ.image φ) →
      ((⌊(N : ℚ) * q⌋ : ℤ) : ℚ) = N * q := by
    intro q hq
    obtain ⟨z, hz⟩ := hz q hq
    rw [← hz, Int.floor_intCast]
  have hσ : ∀ a, ((⌊(N : ℚ) * σ a⌋ : ℤ) : ℚ) = N * σ a := fun a => hfl _ (by simp)
  have hγ : ∀ a, ((⌊(N : ℚ) * γ a⌋ : ℤ) : ℚ) = N * γ a := fun a => hfl _ (by simp)
  have hφ : ∀ a, ((⌊(N : ℚ) * φ a⌋ : ℤ) : ℚ) = N * φ a := fun a => hfl _ (by simp)
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  refine ⟨fun a => ⌊(N : ℚ) * σ a⌋, fun a => ⌊(N : ℚ) * γ a⌋, fun a => ⌊(N : ℚ) * φ a⌋, ?_, ?_⟩
  · rintro ⟨h1, h2, h3⟩
    apply hnc
    refine ⟨fun a a' => ?_, fun a a' => ?_, fun a a' => ?_⟩
    · have := congrArg (fun z : ℤ => (z : ℚ)) (h1 a a')
      simp only [hσ] at this
      exact mul_left_cancel₀ hN' this
    · have := congrArg (fun z : ℤ => (z : ℚ)) (h2 a a')
      simp only [hγ] at this
      exact mul_left_cancel₀ hN' this
    · have := congrArg (fun z : ℤ => (z : ℚ)) (h3 a a')
      simp only [hφ] at this
      exact mul_left_cancel₀ hN' this
  · intro t ht
    have : (((⌊(N : ℚ) * σ t.1⌋ + ⌊(N : ℚ) * γ t.2.1⌋ + ⌊(N : ℚ) * φ t.2.2⌋ : ℤ)) : ℚ) = 0 := by
      push_cast
      rw [hσ, hγ, hφ, ← mul_add, ← mul_add, hrel t ht, mul_zero]
    exact_mod_cast this

lemma hasEmb_int_of_complex {T : Type*} [Fintype T] (S : Set (T × T × T)) :
    HasEmbedding ℂ S → HasEmbedding ℤ S :=
  fun h => hasEmb_int_of_rat S (hasEmb_rat_of_complex S h)


section Key
variable {T : Type*} [Fintype T]

/-- The quadratic form `Q_S(g) = Σ_{t ∈ S} ‖g₀ x + g₁ y + g₂ z‖²`. -/
noncomputable def Qf (S : Finset (T × T × T)) (g : Fin 3 → T → ℂ) : ℝ :=
  ∑ t ∈ S, ‖g 0 t.1 + g 1 t.2.1 + g 2 t.2.2‖ ^ 2

/-- The squared norm `Σ_i Σ_a ‖g i a‖²`. -/
noncomputable def Nf (g : Fin 3 → T → ℂ) : ℝ :=
  ∑ i, ∑ a, ‖g i a‖ ^ 2

/-- The three coordinate sums of `g` are equal. -/
def EqSums (g : Fin 3 → T → ℂ) : Prop :=
  ∑ a, g 0 a = ∑ a, g 1 a ∧ ∑ a, g 1 a = ∑ a, g 2 a

lemma Qf_nonneg (S : Finset (T × T × T)) (g : Fin 3 → T → ℂ) : 0 ≤ Qf S g :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma Nf_nonneg (g : Fin 3 → T → ℂ) : 0 ≤ Nf g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

lemma Qf_smul (S : Finset (T × T × T)) (g : Fin 3 → T → ℂ) (r : ℝ) :
    Qf S (fun i a => (r : ℂ) * g i a) = r ^ 2 * Qf S g := by
  unfold Qf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← mul_add, ← mul_add, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma Nf_smul (g : Fin 3 → T → ℂ) (r : ℝ) :
    Nf (fun i a => (r : ℂ) * g i a) = r ^ 2 * Nf g := by
  unfold Nf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma EqSums_smul (g : Fin 3 → T → ℂ) (r : ℝ) (h : EqSums g) :
    EqSums (fun i a => (r : ℂ) * g i a) := by
  unfold EqSums at *
  simp only [← Finset.mul_sum]
  exact ⟨by rw [h.1], by rw [h.2]⟩

lemma eq_zero_of_Qf_eq_zero (S : Finset (T × T × T)) (hS : S.Nonempty)
    (hemb : ¬ HasEmbedding ℤ (S : Set (T × T × T))) (g : Fin 3 → T → ℂ) (hg : EqSums g)
    (hQ : Qf S g = 0) : Nf g = 0 := by
  have hz : ∀ t ∈ S, g 0 t.1 + g 1 t.2.1 + g 2 t.2.2 = 0 := by
    intro t ht
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => by positivity)).1 hQ t ht
    simpa using this
  have hconst : (∀ a a', g 0 a = g 0 a') ∧ (∀ b b', g 1 b = g 1 b') ∧ (∀ c c', g 2 c = g 2 c') := by
    by_contra hnc
    exact hemb (hasEmb_int_of_complex _ ⟨g 0, g 1, g 2, hnc, fun t ht => hz t ht⟩)
  obtain ⟨t, ht⟩ := hS
  have hcard : (Fintype.card T : ℂ) ≠ 0 := by
    have : 0 < Fintype.card T := Fintype.card_pos_iff.2 ⟨t.1⟩
    exact_mod_cast this.ne'
  have hsum : ∀ i : Fin 3, ∀ a0 : T, (∀ a a', g i a = g i a') →
      ∑ a, g i a = (Fintype.card T : ℂ) * g i a0 := by
    intro i a0 h
    rw [Finset.sum_congr rfl (fun a _ => h a a0)]
    simp
  have e01 : g 0 t.1 = g 1 t.2.1 := by
    have := hg.1
    rw [hsum 0 t.1 hconst.1, hsum 1 t.2.1 hconst.2.1] at this
    exact mul_left_cancel₀ hcard this
  have e12 : g 1 t.2.1 = g 2 t.2.2 := by
    have := hg.2
    rw [hsum 1 t.2.1 hconst.2.1, hsum 2 t.2.2 hconst.2.2] at this
    exact mul_left_cancel₀ hcard this
  have h0 : g 0 t.1 = 0 := by
    have := hz t ht
    rw [← e12, ← e01] at this
    have h3 : (3 : ℂ) * g 0 t.1 = 0 := by rw [← this]; ring
    simpa using h3
  have hall : ∀ i a, g i a = 0 := by
    intro i a
    fin_cases i
    · simp only [Fin.zero_eta]; rw [hconst.1 a t.1, h0]
    · simp only [Fin.mk_one]; rw [hconst.2.1 a t.2.1, ← e01, h0]
    · show g 2 a = 0
      rw [hconst.2.2 a t.2.2, ← e12, ← e01, h0]
  unfold Nf
  simp [hall]

lemma continuous_Qf (S : Finset (T × T × T)) : Continuous (Qf S) := by
  unfold Qf; fun_prop

lemma continuous_Nf : Continuous (Nf : (Fin 3 → T → ℂ) → ℝ) := by
  unfold Nf; fun_prop

/-- The per-support lemma: `Q_S` dominates `Nf` on the equal-sums subspace. -/
lemma key (S : Finset (T × T × T)) (hS : S.Nonempty)
    (hemb : ¬ HasEmbedding ℤ (S : Set (T × T × T))) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : Fin 3 → T → ℂ, EqSums g → c * Nf g ≤ Qf S g := by
  set X : Set (Fin 3 → T → ℂ) := {g | Nf g = 1 ∧ EqSums g} with hXdef
  have hXc : IsCompact X := by
    apply Metric.isCompact_of_isClosed_isBounded
    · refine IsClosed.inter (isClosed_eq continuous_Nf continuous_const) ?_
      refine IsClosed.inter (isClosed_eq (by fun_prop) (by fun_prop))
        (isClosed_eq (by fun_prop) (by fun_prop))
    · refine (Metric.isBounded_closedBall (x := 0) (r := 1)).subset ?_
      intro g hg
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
      have h1 : ‖g i a‖ ^ 2 ≤ Nf g := by
        unfold Nf
        refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ a, ‖g i a‖ ^ 2)
          (fun i _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i))
        exact Finset.single_le_sum (f := fun a => ‖g i a‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ a)
      rw [hg.1] at h1
      nlinarith [norm_nonneg (g i a)]
  -- normalization
  have hnorm : ∀ g, EqSums g → Nf g ≠ 0 →
      (fun i a => ((Real.sqrt (Nf g))⁻¹ : ℝ) * g i a) ∈ X ∧
      Qf S (fun i a => ((Real.sqrt (Nf g))⁻¹ : ℝ) * g i a) = (Nf g)⁻¹ * Qf S g := by
    intro g hg hN
    have hpos : 0 < Nf g := lt_of_le_of_ne (Nf_nonneg g) (Ne.symm hN)
    have hsq : ((Real.sqrt (Nf g))⁻¹) ^ 2 = (Nf g)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hpos.le]
    refine ⟨⟨?_, EqSums_smul g _ hg⟩, ?_⟩
    · rw [Nf_smul, hsq, inv_mul_cancel₀ hN]
    · rw [Qf_smul, hsq]
  by_cases hX : X.Nonempty
  · obtain ⟨g0, hg0, hmin⟩ := hXc.exists_isMinOn hX (continuous_Qf S).continuousOn
    refine ⟨Qf S g0, ?_, ?_⟩
    · refine lt_of_le_of_ne (Qf_nonneg S g0) fun h => ?_
      have := eq_zero_of_Qf_eq_zero S hS hemb g0 hg0.2 h.symm
      rw [hg0.1] at this
      exact one_ne_zero this
    · intro g hg
      by_cases hN : Nf g = 0
      · rw [hN, mul_zero]; exact Qf_nonneg S g
      · obtain ⟨hmem, hQ⟩ := hnorm g hg hN
        have h1 := hmin hmem
        simp only [Set.mem_ofPred_eq] at h1
        rw [hQ] at h1
        have hpos : 0 < Nf g := lt_of_le_of_ne (Nf_nonneg g) (Ne.symm hN)
        rw [le_inv_mul_iff₀ hpos] at h1
        linarith
  · refine ⟨1, one_pos, fun g hg => ?_⟩
    by_cases hN : Nf g = 0
    · rw [hN, mul_zero]; exact Qf_nonneg S g
    · exact absurd ⟨_, (hnorm g hg hN).1⟩ hX

/-- Uniformity over all alphabets with `q' + 1` letters. -/
lemma unif (q' : ℕ) : ∃ c : ℝ, 0 < c ∧
    ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig], Fintype.card Sig = q' + 1 →
    ∀ S : Finset (Sig × Sig × Sig), S.Nonempty → ¬ HasEmbedding ℤ (S : Set (Sig × Sig × Sig)) →
    ∀ g : Fin 3 → Sig → ℂ, EqSums g → c * Nf g ≤ Qf S g := by
  classical
  have hk : ∀ S : Finset (Fin (q' + 1) × Fin (q' + 1) × Fin (q' + 1)), ∃ c : ℝ, 0 < c ∧
      (S.Nonempty → ¬ HasEmbedding ℤ (S : Set (Fin (q' + 1) × Fin (q' + 1) × Fin (q' + 1))) →
        ∀ g : Fin 3 → Fin (q' + 1) → ℂ, EqSums g → c * Nf g ≤ Qf S g) := by
    intro S
    by_cases h : S.Nonempty ∧ ¬ HasEmbedding ℤ (S : Set (Fin (q' + 1) × Fin (q' + 1) × Fin (q' + 1)))
    · obtain ⟨c, hc, hc'⟩ := key S h.1 h.2
      exact ⟨c, hc, fun _ _ => hc'⟩
    · exact ⟨1, one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose cf hcf hcf' using hk
  refine ⟨Finset.univ.inf' Finset.univ_nonempty cf,
    (Finset.lt_inf'_iff _).2 (fun S _ => hcf S), ?_⟩
  intro Sig _ _ hcard S hS hemb g hg
  let e : Sig ≃ Fin (q' + 1) := Fintype.equivFinOfCardEq hcard
  let E : Sig × Sig × Sig ≃ Fin (q' + 1) × Fin (q' + 1) × Fin (q' + 1) :=
    e.prodCongr (e.prodCongr e)
  let S' := S.map E.toEmbedding
  let g' : Fin 3 → Fin (q' + 1) → ℂ := fun i a => g i (e.symm a)
  have hS' : S'.Nonempty := hS.map
  have hemb' : ¬ HasEmbedding ℤ (S' : Set (Fin (q' + 1) × Fin (q' + 1) × Fin (q' + 1))) := by
    rintro ⟨σ, γ, φ, hnc, hrel⟩
    apply hemb
    refine ⟨σ ∘ e, γ ∘ e, φ ∘ e, ?_, ?_⟩
    · rintro ⟨h1, h2, h3⟩
      apply hnc
      refine ⟨fun a a' => ?_, fun a a' => ?_, fun a a' => ?_⟩
      · simpa using h1 (e.symm a) (e.symm a')
      · simpa using h2 (e.symm a) (e.symm a')
      · simpa using h3 (e.symm a) (e.symm a')
    · intro t ht
      have hmem : E t ∈ S' := Finset.mem_map_of_mem _ ht
      simpa [E] using hrel (E t) hmem
  have hs : ∀ i, ∑ a, g' i a = ∑ a, g i a := fun i => Equiv.sum_comp e.symm (g i)
  have hg' : EqSums g' := by
    unfold EqSums; rw [hs, hs, hs]; exact hg
  have hN : Nf g' = Nf g := by
    unfold Nf
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Equiv.sum_comp e.symm (fun a => ‖g i a‖ ^ 2)
  have hQ : Qf S' g' = Qf S g := by
    unfold Qf
    rw [Finset.sum_map]
    simp [E, g']
  calc Finset.univ.inf' Finset.univ_nonempty cf * Nf g ≤ cf S' * Nf g :=
        mul_le_mul_of_nonneg_right (Finset.inf'_le _ (Finset.mem_univ _)) (Nf_nonneg g)
    _ = cf S' * Nf g' := by rw [hN]
    _ ≤ Qf S' g' := hcf' S' hS' hemb' g' hg'
    _ = Qf S g := hQ

lemma reorder3 {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] (F : X → Y → Z → ℂ) :
    ∑ x, ∑ y, ∑ z, F x y z = ∑ z, ∑ y, ∑ x, F x y z := by
  calc ∑ x, ∑ y, ∑ z, F x y z = ∑ x, ∑ z, ∑ y, F x y z :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, F x y z := Finset.sum_comm
    _ = ∑ z, ∑ y, ∑ x, F x y z := Finset.sum_congr rfl fun z _ => Finset.sum_comm

/-- The quadratic form of a covariance matrix. -/
lemma quad {ι Ω : Type*} [Fintype ι] [Fintype Ω] (μ : Ω → ℝ) (W : ι → Ω → ℂ) (v : ι → ℂ) :
    star v ⬝ᵥ ((Matrix.of fun ij kl => ∑ t, (μ t : ℂ) * W ij t * star (W kl t)) *ᵥ v) =
      ((∑ t, μ t * ‖∑ k, v k * star (W k t)‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  simp_rw [← Complex.conj_mul']
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, map_sum, map_mul, Finset.mul_sum,
    Finset.sum_mul, Pi.star_apply, Complex.star_def, Complex.conj_conj]
  refine Eq.trans ?_ (reorder3 (fun t b a => (μ t : ℂ) * ((starRingEnd ℂ) (v a) * W a t *
    (v b * (starRingEnd ℂ) (W b t))))).symm
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun t _ => ?_
  ring

/-- Shifting a `ν`-mean-zero function by a constant does not decrease its `L²(ν)` mass. -/
lemma shift_ge {Ω : Type*} [Fintype Ω] (ν : Ω → ℝ) (hν : ∀ a, 0 ≤ ν a) (g : Ω → ℂ)
    (hmean : ∑ a, (ν a : ℂ) * g a = 0) (c : ℂ) :
    ∑ a, ν a * ‖g a‖ ^ 2 ≤ ∑ a, ν a * ‖g a + c‖ ^ 2 := by
  have key : ∑ a, ν a * ‖g a + c‖ ^ 2 = ∑ a, ν a * ‖g a‖ ^ 2 + (∑ a, ν a) * ‖c‖ ^ 2 +
      2 * ((∑ a, (ν a : ℂ) * g a) * (starRingEnd ℂ) c).re := by
    rw [Finset.sum_mul, Finset.sum_mul, Complex.re_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, mul_assoc,
      Complex.re_ofReal_mul]
    ring
  rw [key, hmean, zero_mul, Complex.zero_re, mul_zero, add_zero]
  have : 0 ≤ (∑ a, ν a) * ‖c‖ ^ 2 :=
    mul_nonneg (Finset.sum_nonneg fun a _ => hν a) (by positivity)
  linarith

/-- Orthonormality: the `L²(ν)` mass of `Σ_j v j · conj(f j)` is `Σ_j ‖v j‖²`. -/
lemma ortho_mass {Ω : Type*} [Fintype Ω] {n : ℕ} (ν : Ω → ℝ) (f : Fin n → Ω → ℂ)
    (horth : ∀ j k, ∑ a, (ν a : ℂ) * star (f j a) * f k a = if j = k then 1 else 0)
    (v : Fin n → ℂ) :
    ∑ a, ν a * ‖∑ j, v j * star (f j a)‖ ^ 2 = ∑ j, ‖v j‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.conj_mul']
  simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, Complex.star_def, Complex.conj_conj]
  refine (reorder3 (fun a k j => (ν a : ℂ) * ((starRingEnd ℂ) (v j) * f j a *
    (v k * (starRingEnd ℂ) (f k a))))).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∀ k, ∑ a, (ν a : ℂ) * ((starRingEnd ℂ) (v j) * f j a *
      (v k * (starRingEnd ℂ) (f k a))) = (starRingEnd ℂ) (v j) * v k * (if k = j then 1 else 0) := by
    intro k
    rw [← horth k j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.star_def]
    ring
  simp only [h1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Key

/-- The main estimate: `α c Σ‖v‖² ≤ Σ_t μ t |G(t)|²`. -/
lemma bound (q' : ℕ) (c : ℝ)
    (hunif : ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig], Fintype.card Sig = q' + 1 →
      ∀ S : Finset (Sig × Sig × Sig), S.Nonempty → ¬ HasEmbedding ℤ (S : Set (Sig × Sig × Sig)) →
      ∀ g : Fin 3 → Sig → ℂ, EqSums g → c * Nf g ≤ Qf S g)
    (hc : 0 < c) (α : ℝ) (hα : 0 < α) (Sig : Type) [Fintype Sig] [DecidableEq Sig]
    (hcard : Fintype.card Sig = q' + 1) (μ : Sig × Sig × Sig → ℝ) (hμ : IsDist μ)
    (hemb : ¬ DistHasEmbedding ℤ μ) (hat : AtomsAtLeast μ α)
    (fb : Fin 3 → Fin (q' + 1) → Sig → ℂ) (hfb0 : ∀ i a, fb i 0 a = 1)
    (horth : ∀ (i : Fin 3) (j k : Fin (q' + 1)),
      ∑ a, (marginal μ i a : ℂ) * star (fb i j a) * fb i k a = if j = k then 1 else 0)
    (v : Fin 3 × Fin q' → ℂ) :
    α * c * ∑ k, ‖v k‖ ^ 2 ≤
      ∑ t, μ t * ‖∑ k, v k * star (fb k.1 k.2.succ (coord3 k.1 t))‖ ^ 2 := by
  set ν := marginal μ with hνdef
  set g : Fin 3 → Sig → ℂ := fun i a => ∑ j, v (i, j) * star (fb i j.succ a) with hgdef
  have hG : ∀ t : Sig × Sig × Sig, ∑ k, v k * star (fb k.1 k.2.succ (coord3 k.1 t)) =
      g 0 t.1 + g 1 t.2.1 + g 2 t.2.2 := by
    intro t
    rw [Fintype.sum_prod_type, Fin.sum_univ_three]
    simp [coord3, g]
  have hν0 : ∀ i a, 0 ≤ ν i a := by
    intro i a
    refine Finset.sum_nonneg fun t _ => ?_
    split_ifs
    · exact hμ.1 t
    · exact le_rfl
  have hν1 : ∀ i a, ν i a ≤ 1 := by
    intro i a
    calc ν i a ≤ ∑ t, μ t := Finset.sum_le_sum fun t _ => by
            split_ifs
            · exact le_rfl
            · exact hμ.1 t
      _ = 1 := hμ.2
  have hmean : ∀ i, ∑ a, (ν i a : ℂ) * g i a = 0 := by
    intro i
    simp only [g, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h0 := horth i j.succ 0
    rw [if_neg (Fin.succ_ne_zero j)] at h0
    calc ∑ a, (ν i a : ℂ) * (v (i, j) * star (fb i j.succ a))
        = v (i, j) * ∑ a, (marginal μ i a : ℂ) * star (fb i j.succ a) * fb i 0 a := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hfb0]
          ring
      _ = 0 := by rw [h0, mul_zero]
  have hmass : ∀ i, ∑ a, ν i a * ‖g i a‖ ^ 2 = ∑ j, ‖v (i, j)‖ ^ 2 := by
    intro i
    exact ortho_mass (ν i) (fun j => fb i j.succ)
      (fun j k => by rw [horth]; simp [Fin.succ_inj]) (fun j => v (i, j))
  have hcardne : (Fintype.card Sig : ℂ) ≠ 0 := by rw [hcard]; exact_mod_cast Nat.succ_ne_zero q'
  set m : Fin 3 → ℂ := fun i => (∑ a, g i a) / Fintype.card Sig with hmdef
  set mb : ℂ := (m 0 + m 1 + m 2) / 3 with hmbdef
  set h : Fin 3 → Sig → ℂ := fun i a => g i a + (mb - m i) with hhdef
  have hsumh : ∀ i, ∑ a, h i a = Fintype.card Sig * mb := by
    intro i
    simp only [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : ∑ a, g i a = Fintype.card Sig * m i := by
      simp only [m]; rw [mul_div_cancel₀ _ hcardne]
    rw [this]; ring
  have hEq : EqSums h := ⟨by rw [hsumh, hsumh], by rw [hsumh, hsumh]⟩
  have hpt : ∀ t : Sig × Sig × Sig,
      h 0 t.1 + h 1 t.2.1 + h 2 t.2.2 = g 0 t.1 + g 1 t.2.1 + g 2 t.2.2 := by
    intro t; simp only [h, mb]; ring
  set suppF := Finset.univ.filter (fun t => μ t ≠ 0) with hsuppF
  have hSne : suppF.Nonempty := by
    obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := μ)
      (by rw [hμ.2]; exact one_ne_zero)
    exact ⟨t, by simp [suppF, ht]⟩
  have hembS : ¬ HasEmbedding ℤ (suppF : Set (Sig × Sig × Sig)) := by
    have : (suppF : Set (Sig × Sig × Sig)) = supp μ := by
      ext t; simp [suppF, supp]
    rw [this]; exact hemb
  have hQ := hunif Sig hcard suppF hSne hembS h hEq
  have hNf : ∑ k, ‖v k‖ ^ 2 ≤ Nf h := by
    rw [Fintype.sum_prod_type]
    unfold Nf
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← hmass i]
    calc ∑ a, ν i a * ‖g i a‖ ^ 2 ≤ ∑ a, ν i a * ‖g i a + (mb - m i)‖ ^ 2 :=
          shift_ge (ν i) (hν0 i) (g i) (hmean i) _
      _ ≤ ∑ a, ‖h i a‖ ^ 2 :=
          Finset.sum_le_sum fun a _ => mul_le_of_le_one_left (by positivity) (hν1 i a)
  have hR : α * Qf suppF h ≤
      ∑ t, μ t * ‖∑ k, v k * star (fb k.1 k.2.succ (coord3 k.1 t))‖ ^ 2 := by
    unfold Qf
    rw [Finset.mul_sum]
    calc ∑ t ∈ suppF, α * ‖h 0 t.1 + h 1 t.2.1 + h 2 t.2.2‖ ^ 2
        ≤ ∑ t ∈ suppF, μ t * ‖∑ k, v k * star (fb k.1 k.2.succ (coord3 k.1 t))‖ ^ 2 := by
          refine Finset.sum_le_sum fun t ht => ?_
          rw [hG, ← hpt]
          exact mul_le_mul_of_nonneg_right (hat t (Finset.mem_filter.1 ht).2) (by positivity)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun t _ _ => mul_nonneg (hμ.1 t) (by positivity))
  calc α * c * ∑ k, ‖v k‖ ^ 2 ≤ α * (c * Nf h) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hNf hc.le) hα.le
    _ ≤ α * Qf suppF h := mul_le_mul_of_nonneg_left hQ hα.le
    _ ≤ _ := hR

end RestrictedAP.Counting.Dev.P528

namespace RestrictedAP.Counting
open RestrictedAP.Counting.Dev.P528 Matrix in
theorem chk_proposition_5_28 (q' : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig], Fintype.card Sig = q' + 1 →
      ∀ μ : Sig × Sig × Sig → ℝ, IsDist μ → ¬ DistHasEmbedding ℤ μ → IsMinAtom μ α →
        (∀ (i : Fin 3) (a : Sig), marginal μ i a ≠ 0) →
      ∀ fb : Fin 3 → Fin (q' + 1) → Sig → ℂ,
        (∀ i a, fb i 0 a = 1) →
        (∀ (i : Fin 3) (j k : Fin (q' + 1)),
          ∑ a, (marginal μ i a : ℂ) * star (fb i j a) * fb i k a = if j = k then 1 else 0) →
        let W : Fin 3 × Fin q' → Sig × Sig × Sig → ℂ :=
          fun ij t => fb ij.1 ij.2.succ (coord3 ij.1 t)
        let Mcov : Matrix (Fin 3 × Fin q') (Fin 3 × Fin q') ℂ :=
          Matrix.of fun ij kl => ∑ t, (μ t : ℂ) * W ij t * star (W kl t)
        Mcov.PosDef ∧
          (Mcov - (η : ℂ) • (1 : Matrix (Fin 3 × Fin q') (Fin 3 × Fin q') ℂ)).PosSemidef := by
  obtain ⟨c, hc, hunif⟩ := unif q'
  refine ⟨α * c, mul_pos hα hc, ?_⟩
  intro Sig _ _ hcard μ hμ hemb hmin _ fb hfb0 horth W Mcov
  have hq : ∀ v, star v ⬝ᵥ (Mcov *ᵥ v) =
      ((∑ t, μ t * ‖∑ k, v k * star (W k t)‖ ^ 2 : ℝ) : ℂ) := fun v => quad μ W v
  have hb : ∀ v : Fin 3 × Fin q' → ℂ, α * c * ∑ k, ‖v k‖ ^ 2 ≤
      ∑ t, μ t * ‖∑ k, v k * star (W k t)‖ ^ 2 :=
    fun v => bound q' c hunif hc α hα Sig hcard μ hμ hemb hmin.2.1 fb hfb0 horth v
  have herm : Mcov.IsHermitian := by
    ext i j
    simp only [Mcov, Matrix.conjTranspose_apply, Matrix.of_apply, star_sum, star_mul',
      Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  have hvv : ∀ v : Fin 3 × Fin q' → ℂ, star v ⬝ᵥ v = ((∑ k, ‖v k‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    push_cast
    simp only [dotProduct, ← Complex.conj_mul', Pi.star_apply, Complex.star_def]
  constructor
  · refine Matrix.PosDef.of_dotProduct_mulVec_pos herm fun v hv => ?_
    rw [hq]
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
    have hpos : 0 < ∑ k, ‖v k‖ ^ 2 :=
      Finset.sum_pos' (fun _ _ => by positivity) ⟨k, Finset.mem_univ _, by
        have : 0 < ‖v k‖ := norm_pos_iff.2 hk
        positivity⟩
    exact_mod_cast lt_of_lt_of_le (mul_pos (mul_pos hα hc) hpos) (hb v)
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (herm.sub (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint]))) fun v => ?_
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, hq, hvv, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    exact Complex.zero_le_real.2 (by linarith [hb v])

end RestrictedAP.Counting
end

theorem solution : type_of% @RestrictedAP.Counting.chk_proposition_5_28 := @RestrictedAP.Counting.chk_proposition_5_28
