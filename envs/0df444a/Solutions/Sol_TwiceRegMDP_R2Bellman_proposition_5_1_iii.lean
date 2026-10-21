-- Prove2me | solution 1 for TwiceRegMDP.R2Bellman.proposition_5_1_iii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:29:02.205447+00:00
-- url     : https://prove2.me/submissions/a4de2f14-3fc0-427d-afe1-5ee4018e695e

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_TwiceRegMDP_R2Bellman_MDP
import Definitions.Def_TwiceRegMDP_R2Bellman_R2Ops

set_option autoImplicit false
open TwiceRegMDP.R2Bellman

section l2
variable {Z : Type} [Fintype Z]

lemma trm_l2norm_eq (a : Z → ℝ) : l2norm a = ‖(WithLp.toLp 2 a : EuclideanSpace ℝ Z)‖ := by
  simp [l2norm, EuclideanSpace.norm_eq]

lemma trm_l2norm_nonneg (a : Z → ℝ) : 0 ≤ l2norm a := Real.sqrt_nonneg _

lemma trm_l2norm_sub (a b : Z → ℝ) : |l2norm a - l2norm b| ≤ l2norm (a - b) := by
  rw [trm_l2norm_eq, trm_l2norm_eq, trm_l2norm_eq]
  have := abs_norm_sub_norm_le (WithLp.toLp 2 a : EuclideanSpace ℝ Z) (WithLp.toLp 2 b)
  simpa using this

lemma trm_l2norm_smul (c : ℝ) (hc : 0 ≤ c) (a : Z → ℝ) : l2norm (c • a) = c * l2norm a := by
  rw [trm_l2norm_eq, trm_l2norm_eq]
  have : (WithLp.toLp 2 (c • a) : EuclideanSpace ℝ Z) = c • (WithLp.toLp 2 a) := by simp
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]

lemma trm_l2norm_le_sup (a : Z → ℝ) : l2norm a ≤ Real.sqrt (Fintype.card Z) * ‖a‖ := by
  unfold l2norm
  have h : ∑ z, a z ^ 2 ≤ (Fintype.card Z : ℝ) * ‖a‖ ^ 2 := by
    calc ∑ z, a z ^ 2 ≤ ∑ z : Z, ‖a‖ ^ 2 := Finset.sum_le_sum fun z _ => by
            have := norm_le_pi_norm a z
            rw [Real.norm_eq_abs] at this
            nlinarith [abs_nonneg (a z), sq_abs (a z)]
      _ = _ := by simp
  calc Real.sqrt (∑ z, a z ^ 2) ≤ Real.sqrt ((Fintype.card Z : ℝ) * ‖a‖ ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = Real.sqrt (Fintype.card Z) * ‖a‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

lemma trm_l2norm_simplex_le (p : Z → ℝ) (hp : p ∈ stdSimplex ℝ Z) : l2norm p ≤ 1 := by
  unfold l2norm
  apply Real.sqrt_le_one.2
  calc ∑ z, p z ^ 2 ≤ ∑ z, p z := Finset.sum_le_sum fun z _ => by
        have h0 := hp.1 z
        have h1 : p z ≤ 1 := by
          have := Finset.single_le_sum (f := p) (fun i _ => hp.1 i) (Finset.mem_univ z)
          rw [hp.2] at this; exact this
        nlinarith
    _ = 1 := hp.2

lemma trm_l2norm_simplex_pos (p : Z → ℝ) (hp : p ∈ stdSimplex ℝ Z) : 0 < l2norm p := by
  by_contra h
  have h0 : l2norm p = 0 := le_antisymm (not_lt.1 h) (Real.sqrt_nonneg _)
  unfold l2norm at h0
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun z _ => sq_nonneg _)] at h0
  have hz : ∀ z, p z = 0 := fun z => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => sq_nonneg (p z))).1 h0 z
      (Finset.mem_univ z)
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  have h1 := hp.2
  simp [hz] at h1

lemma trm_l2norm_continuous : Continuous (fun p : Z → ℝ => l2norm p) :=
  Real.continuous_sqrt.comp (continuous_finset_sum _ fun a _ => (continuous_apply a).pow 2)
end l2

section mdp
variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

noncomputable def trmObj (γ : ℝ) (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ) (αr αP : S → ℝ)
    (v : S → ℝ) (s : S) (p : A → ℝ) : ℝ :=
  ∑ a, p a * qfun γ P₀ r₀ v s a - r2Reg γ αr αP v s p

lemma trm_obj_cont (γ : ℝ) (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ) (αr αP : S → ℝ)
    (v : S → ℝ) (s : S) : Continuous (trmObj γ P₀ r₀ αr αP v s) := by
  unfold trmObj r2Reg
  exact (continuous_finset_sum _ fun a _ => (continuous_apply a).mul continuous_const).sub
    (trm_l2norm_continuous.mul continuous_const)

lemma trm_bdd (γ : ℝ) (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ) (αr αP : S → ℝ)
    (v : S → ℝ) (s : S) :
    BddAbove ((trmObj γ P₀ r₀ αr αP v s) '' stdSimplex ℝ A) :=
  IsCompact.bddAbove_image (isCompact_stdSimplex ℝ A) (trm_obj_cont γ P₀ r₀ αr αP v s).continuousOn

lemma trm_innerMin_le (P₀ : S → A → S → ℝ)
    (hP : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀) (s : S)
    (u : A → ℝ) (w : S → ℝ) (hu : ∀ a, 0 ≤ u a) (hun : l2norm u = 1) (hw : ∀ s', 0 ≤ w s')
    (hwn : l2norm w = 1) :
    innerMin P₀ s ≤ ∑ a, ∑ s', u a * P₀ s a s' * w s' := by
  unfold innerMin
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨uw, ⟨hu', -, hw', -⟩, rfl⟩
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun s' _ =>
      mul_nonneg (mul_nonneg (hu' a) ((hP s a).1 s')) (hw' s')
  · exact ⟨(u, w), ⟨hu, hun, hw, hwn⟩, rfl⟩

lemma trm_T_nonneg (P₀ : S → A → S → ℝ)
    (hP : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀) (s : S)
    (p : A → ℝ) (hp : p ∈ stdSimplex ℝ A) (δ : S → ℝ) (hδ : ∀ s', 0 ≤ δ s') :
    0 ≤ ∑ a, p a * ∑ s', P₀ s a s' * δ s' :=
  Finset.sum_nonneg fun a _ => mul_nonneg (hp.1 a)
    (Finset.sum_nonneg fun s' _ => mul_nonneg ((hP s a).1 s') (hδ s'))

lemma trm_claimA (P₀ : S → A → S → ℝ)
    (hP : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀) (s : S) (αs : ℝ)
    (hα : αs ≤ innerMin P₀ s)
    (p : A → ℝ) (hp : p ∈ stdSimplex ℝ A) (δ : S → ℝ) (hδ : ∀ s', 0 ≤ δ s') :
    αs * (l2norm p * l2norm δ) ≤ ∑ a, p a * ∑ s', P₀ s a s' * δ s' := by
  have hT := trm_T_nonneg P₀ hP s p hp δ hδ
  by_cases h0 : l2norm δ = 0
  · rw [h0]; simpa using hT
  have hnδ : 0 < l2norm δ := lt_of_le_of_ne (trm_l2norm_nonneg δ) (Ne.symm h0)
  have hnp : 0 < l2norm p := trm_l2norm_simplex_pos p hp
  have hu : ∀ a, 0 ≤ ((l2norm p)⁻¹ • p) a := fun a => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hnp.le) (hp.1 a)
  have hw : ∀ s', 0 ≤ ((l2norm δ)⁻¹ • δ) s' := fun s' => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hnδ.le) (hδ s')
  have hun : l2norm ((l2norm p)⁻¹ • p) = 1 := by
    rw [trm_l2norm_smul _ (inv_nonneg.2 hnp.le)]; field_simp
  have hwn : l2norm ((l2norm δ)⁻¹ • δ) = 1 := by
    rw [trm_l2norm_smul _ (inv_nonneg.2 hnδ.le)]; field_simp
  have h1 := trm_innerMin_le P₀ hP s _ _ hu hun hw hwn
  have h2 : ∑ a, ∑ s', ((l2norm p)⁻¹ • p) a * P₀ s a s' * ((l2norm δ)⁻¹ • δ) s' =
      (l2norm p)⁻¹ * (l2norm δ)⁻¹ * ∑ a, p a * ∑ s', P₀ s a s' * δ s' := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s' _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h2] at h1
  have h3 := hα.trans h1
  have h4 : 0 < l2norm p * l2norm δ := mul_pos hnp hnδ
  have h5 : αs * (l2norm p * l2norm δ) ≤ (l2norm p)⁻¹ * (l2norm δ)⁻¹ *
      (∑ a, p a * ∑ s', P₀ s a s' * δ s') * (l2norm p * l2norm δ) :=
    mul_le_mul_of_nonneg_right h3 h4.le
  calc αs * (l2norm p * l2norm δ) ≤ _ := h5
    _ = _ := by field_simp

lemma trm_obj_mono (γ : ℝ) (hγ : 0 < γ) (P₀ : S → A → S → ℝ)
    (hP : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀) (r₀ : S → A → ℝ)
    (αr αP : S → ℝ) (hαP : ∀ s, 0 ≤ αP s) (s : S) (hα : αP s ≤ innerMin P₀ s)
    (p : A → ℝ) (hp : p ∈ stdSimplex ℝ A) (v₁ v₂ : S → ℝ) (hv : v₁ ≤ v₂) :
    trmObj γ P₀ r₀ αr αP v₁ s p ≤ trmObj γ P₀ r₀ αr αP v₂ s p := by
  have hδ : ∀ s', 0 ≤ (v₂ - v₁) s' := fun s' => sub_nonneg.2 (hv s')
  have hA := trm_claimA P₀ hP s (αP s) hα p hp (v₂ - v₁) hδ
  have hq : ∑ a, p a * qfun γ P₀ r₀ v₂ s a - ∑ a, p a * qfun γ P₀ r₀ v₁ s a =
      γ * ∑ a, p a * ∑ s', P₀ s a s' * (v₂ - v₁) s' := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    unfold qfun
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hr : r2Reg γ αr αP v₂ s p - r2Reg γ αr αP v₁ s p =
      l2norm p * αP s * γ * (l2norm v₂ - l2norm v₁) := by
    unfold r2Reg; ring
  have hn : l2norm v₂ - l2norm v₁ ≤ l2norm (v₂ - v₁) :=
    (le_abs_self _).trans (trm_l2norm_sub v₂ v₁)
  have hc : 0 ≤ l2norm p * αP s * γ :=
    mul_nonneg (mul_nonneg (trm_l2norm_nonneg p) (hαP s)) hγ.le
  have h1 : l2norm p * αP s * γ * (l2norm v₂ - l2norm v₁) ≤
      l2norm p * αP s * γ * l2norm (v₂ - v₁) := mul_le_mul_of_nonneg_left hn hc
  have h2 : γ * (αP s * (l2norm p * l2norm (v₂ - v₁))) ≤
      γ * ∑ a, p a * ∑ s', P₀ s a s' * (v₂ - v₁) s' := mul_le_mul_of_nonneg_left hA hγ.le
  unfold trmObj
  nlinarith [hq, hr, h1, h2]
end mdp

section contr
variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

lemma trm_T_le (P₀ : S → A → S → ℝ)
    (hP : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀) (s : S)
    (p : A → ℝ) (hp : p ∈ stdSimplex ℝ A) (δ : S → ℝ) (c : ℝ) (h : ∀ s', δ s' ≤ c) :
    ∑ a, p a * ∑ s', P₀ s a s' * δ s' ≤ c := by
  calc ∑ a, p a * ∑ s', P₀ s a s' * δ s' ≤ ∑ a, p a * c := by
        apply Finset.sum_le_sum; intro a _
        apply mul_le_mul_of_nonneg_left _ (hp.1 a)
        calc ∑ s', P₀ s a s' * δ s' ≤ ∑ s', P₀ s a s' * c :=
              Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (h s') ((hP s a).1 s')
          _ = c := by rw [← Finset.sum_mul, (hP s a).2, one_mul]
    _ = c := by rw [← Finset.sum_mul, hp.2, one_mul]

lemma trm_T_abs (P₀ : S → A → S → ℝ)
    (hP : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀) (s : S)
    (p : A → ℝ) (hp : p ∈ stdSimplex ℝ A) (δ : S → ℝ) :
    |∑ a, p a * ∑ s', P₀ s a s' * δ s'| ≤ ‖δ‖ := by
  rw [abs_le]
  have hδ : ∀ s', δ s' ≤ ‖δ‖ := fun s' => by
    have := norm_le_pi_norm δ s'
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have hδ' : ∀ s', (-δ) s' ≤ ‖δ‖ := fun s' => by
    have := norm_le_pi_norm δ s'
    rw [Real.norm_eq_abs] at this
    simp only [Pi.neg_apply]
    linarith [neg_le_abs (δ s')]
  constructor
  · have := trm_T_le P₀ hP s p hp (-δ) ‖δ‖ hδ'
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] at this
    linarith
  · exact trm_T_le P₀ hP s p hp δ ‖δ‖ hδ

lemma trm_obj_diff [Nonempty S] (γ : ℝ) (hγ : 0 < γ) (P₀ : S → A → S → ℝ)
    (hP : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀) (r₀ : S → A → ℝ)
    (αr αP : S → ℝ) (hαP : ∀ s, 0 ≤ αP s) (ϵ : S → ℝ) (s : S)
    (hα : αP s ≤ (1 - γ - ϵ s) / (γ * Real.sqrt (Fintype.card S)))
    (p : A → ℝ) (hp : p ∈ stdSimplex ℝ A) (v₁ v₂ : S → ℝ) :
    |trmObj γ P₀ r₀ αr αP v₁ s p - trmObj γ P₀ r₀ αr αP v₂ s p| ≤ (1 - ϵ s) * ‖v₁ - v₂‖ := by
  have hq : ∑ a, p a * qfun γ P₀ r₀ v₁ s a - ∑ a, p a * qfun γ P₀ r₀ v₂ s a =
      γ * ∑ a, p a * ∑ s', P₀ s a s' * (v₁ - v₂) s' := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    unfold qfun
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hr : r2Reg γ αr αP v₁ s p - r2Reg γ αr αP v₂ s p =
      l2norm p * αP s * γ * (l2norm v₁ - l2norm v₂) := by
    unfold r2Reg; ring
  have hT := trm_T_abs P₀ hP s p hp (v₁ - v₂)
  have hcard : 0 < (Fintype.card S : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsq : 0 < Real.sqrt (Fintype.card S) := Real.sqrt_pos.2 hcard
  have hα' : αP s * (γ * Real.sqrt (Fintype.card S)) ≤ 1 - γ - ϵ s :=
    (le_div_iff₀ (mul_pos hγ hsq)).1 hα
  have hn : |l2norm v₁ - l2norm v₂| ≤ Real.sqrt (Fintype.card S) * ‖v₁ - v₂‖ :=
    (trm_l2norm_sub v₁ v₂).trans (trm_l2norm_le_sup _)
  have hnp := trm_l2norm_simplex_le p hp
  have hnp0 := trm_l2norm_nonneg p
  have hc0 : 0 ≤ l2norm p * αP s * γ := mul_nonneg (mul_nonneg hnp0 (hαP s)) hγ.le
  have hR : |l2norm p * αP s * γ * (l2norm v₁ - l2norm v₂)| ≤ (1 - γ - ϵ s) * ‖v₁ - v₂‖ := by
    rw [abs_mul, abs_of_nonneg hc0]
    have h1 : l2norm p * αP s * γ ≤ 1 * αP s * γ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnp (hαP s)) hγ.le
    calc l2norm p * αP s * γ * |l2norm v₁ - l2norm v₂|
        ≤ (1 * αP s * γ) * (Real.sqrt (Fintype.card S) * ‖v₁ - v₂‖) :=
          mul_le_mul h1 hn (abs_nonneg _) (by have := hαP s; positivity)
      _ = (αP s * (γ * Real.sqrt (Fintype.card S))) * ‖v₁ - v₂‖ := by ring
      _ ≤ (1 - γ - ϵ s) * ‖v₁ - v₂‖ := mul_le_mul_of_nonneg_right hα' (norm_nonneg _)
  have hid : trmObj γ P₀ r₀ αr αP v₁ s p - trmObj γ P₀ r₀ αr αP v₂ s p =
      γ * ∑ a, p a * ∑ s', P₀ s a s' * (v₁ - v₂) s' -
        l2norm p * αP s * γ * (l2norm v₁ - l2norm v₂) := by
    unfold trmObj; linarith [hq, hr]
  rw [hid]
  calc _ ≤ |γ * ∑ a, p a * ∑ s', P₀ s a s' * (v₁ - v₂) s'| +
        |l2norm p * αP s * γ * (l2norm v₁ - l2norm v₂)| := abs_sub _ _
    _ ≤ γ * ‖v₁ - v₂‖ + (1 - γ - ϵ s) * ‖v₁ - v₂‖ := by
        gcongr
        rw [abs_mul, abs_of_pos hγ]
        exact mul_le_mul_of_nonneg_left hT hγ.le
    _ = (1 - ϵ s) * ‖v₁ - v₂‖ := by ring
end contr

lemma trm_sSup_le {B : Type} (T : Set B) (f g : B → ℝ) (hne : T.Nonempty)
    (bg : BddAbove (g '' T)) (C : ℝ) (hd : ∀ p ∈ T, f p ≤ g p + C) :
    sSup (f '' T) ≤ sSup (g '' T) + C := by
  apply csSup_le (hne.image f)
  rintro _ ⟨p, hp, rfl⟩
  have := le_csSup bg ⟨p, hp, rfl⟩
  linarith [hd p hp]

lemma trm_sSup_abs {B : Type} (T : Set B) (f g : B → ℝ) (hne : T.Nonempty)
    (bf : BddAbove (f '' T)) (bg : BddAbove (g '' T)) (C : ℝ) (hd : ∀ p ∈ T, |f p - g p| ≤ C) :
    |sSup (f '' T) - sSup (g '' T)| ≤ C := by
  rw [abs_le]
  have h1 := trm_sSup_le T f g hne bg C (fun p hp => by linarith [(abs_le.1 (hd p hp)).2])
  have h2 := trm_sSup_le T g f hne bf C (fun p hp => by linarith [(abs_le.1 (hd p hp)).1])
  constructor <;> linarith

theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (P₀ : S → A → S → ℝ) (hP₀ : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀)
    (r₀ : S → A → ℝ)
    (αr αP : S → ℝ) (hαr : ∀ s, 0 ≤ αr s) (hαP : ∀ s, 0 ≤ αP s)
    (ϵ : S → ℝ) (hasm : BoundedRadius γ P₀ αP ϵ) :
    0 < epsStar ϵ ∧
    ∀ v₁ v₂ : S → ℝ,
      (∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π →
        ‖evalOpR2 γ P₀ r₀ αr αP π v₁ - evalOpR2 γ P₀ r₀ αr αP π v₂‖ ≤
          (1 - epsStar ϵ) * ‖v₁ - v₂‖) ∧
      ‖optOpR2 γ P₀ r₀ αr αP v₁ - optOpR2 γ P₀ r₀ αr αP v₂‖ ≤
        (1 - epsStar ϵ) * ‖v₁ - v₂‖ := by
  have hpos : 0 < epsStar ϵ := by
    unfold epsStar
    rw [Finset.lt_inf'_iff]
    intro s _
    exact (hasm s).1
  refine ⟨hpos, fun v₁ v₂ => ?_⟩
  have hle : ∀ s, epsStar ϵ ≤ ϵ s := fun s => Finset.inf'_le _ (Finset.mem_univ s)
  have hC : ∀ s, (1 - ϵ s) * ‖v₁ - v₂‖ ≤ (1 - epsStar ϵ) * ‖v₁ - v₂‖ := fun s =>
    mul_le_mul_of_nonneg_right (by linarith [hle s]) (norm_nonneg _)
  refine ⟨fun π hπ => ?_, ?_⟩
  · rw [pi_norm_le_iff_of_nonempty]
    intro s
    rw [Real.norm_eq_abs]
    exact (trm_obj_diff γ hγ0 P₀ hP₀ r₀ αr αP hαP ϵ s (hasm s).2.1 (π s) (hπ s) v₁ v₂).trans
      (hC s)
  · rw [pi_norm_le_iff_of_nonempty]
    intro s
    rw [Real.norm_eq_abs]
    obtain ⟨a0⟩ := ‹Nonempty A›
    have hne : (stdSimplex ℝ A).Nonempty := ⟨Pi.single a0 1, single_mem_stdSimplex ℝ a0⟩
    exact trm_sSup_abs (stdSimplex ℝ A) (trmObj γ P₀ r₀ αr αP v₁ s) (trmObj γ P₀ r₀ αr αP v₂ s)
      hne (trm_bdd γ P₀ r₀ αr αP v₁ s) (trm_bdd γ P₀ r₀ αr αP v₂ s) _
      (fun p hp => (trm_obj_diff γ hγ0 P₀ hP₀ r₀ αr αP hαP ϵ s (hasm s).2.1 p hp v₁ v₂).trans
        (hC s))
