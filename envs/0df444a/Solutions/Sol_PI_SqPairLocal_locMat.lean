-- Prove2me | solution 1 for PI.SqPairLocal.locMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:28:37.306319+00:00
-- url     : https://prove2.me/submissions/673ebe3e-f773-4ce0-9b38-975028f0c8e1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IntAtOfDivAtZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_Imports
import Theorems.Thm_P2M_PI_SqPairLocal_StModel___ne_57ec0e9aa56c
import Theorems.Thm_PI_SqPairLocal_divAt_conj
import Theorems.Thm_PI_SqPairLocal_divAt_of_map
import Theorems.Thm_PI_SqPairLocal_intAt_of_divAt_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField Matrix
namespace PI.SqPairLocal
open PI.SqPair
attribute [local instance] StModel.cr StModel.dom StModel.dvr StModel.hens StModel.fin
private theorem exists_common_denominator' {E : Type} [Field E] [NumberField E] (s : Finset E) :
    ∃ b : 𝓞 E, b ≠ 0 ∧ ∀ x ∈ s, ∃ w : 𝓞 E,
      algebraMap (𝓞 E) E b * x = algebraMap (𝓞 E) E w := by
  classical
  refine Finset.induction_on s ⟨1, one_ne_zero, fun x hx => by simp at hx⟩ ?_
  intro x s _ ih
  obtain ⟨b, hb, hw⟩ := ih
  obtain ⟨⟨a, c⟩, hac⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) x
  simp only at hac
  have hc : (c : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero c.2
  refine ⟨b * c, mul_ne_zero hb hc, fun y hy => ?_⟩
  rcases Finset.mem_insert.mp hy with rfl | hy
  · refine ⟨b * a, ?_⟩
    rw [map_mul, map_mul, mul_assoc, mul_comm (algebraMap (𝓞 E) E (c : 𝓞 E)), hac]
  · obtain ⟨w, hw'⟩ := hw y hy
    refine ⟨c * w, ?_⟩
    rw [map_mul, map_mul, mul_comm (algebraMap (𝓞 E) E b), mul_assoc, hw']
private theorem exists_one_sub_pow_mul_pow_eq_mul {E : Type} [Field E] [NumberField E] (ϖ : 𝓞 E) (b : 𝓞 E) (hb : b ≠ 0) :
    ∃ m k : ℕ, ∃ v : 𝓞 E, (1 - ϖ ^ (m + 1)) * ϖ ^ k = b * v := by
  have hne : Ideal.span {b} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  haveI : Finite (𝓞 E ⧸ Ideal.span {b}) := by
    first
    | exact (Ideal.absNorm_ne_zero_iff _).mp (fun h0 => hne (Ideal.absNorm_eq_zero_iff.mp h0))
    | exact Ideal.finiteQuotientOfFreeOfNeBot _ hne
    | infer_instance
  obtain ⟨x, y, hxy, h⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => Ideal.Quotient.mk (Ideal.span {b}) (ϖ ^ n))
  have key : ∀ x y : ℕ, x < y →
      Ideal.Quotient.mk (Ideal.span {b}) (ϖ ^ x) = Ideal.Quotient.mk (Ideal.span {b}) (ϖ ^ y) →
      ∃ m k : ℕ, ∃ v : 𝓞 E, (1 - ϖ ^ (m + 1)) * ϖ ^ k = b * v := by
    intro x y hlt he
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at he
    obtain ⟨v, hv⟩ := he
    exact ⟨m, x, v, by rw [← hv]; ring⟩
  rcases Nat.lt_or_gt_of_ne hxy with hlt | hlt
  · exact key x y hlt h
  · exact key y x hlt h.symm
private theorem one_sub_pow_succ_not_mem_of_mem_maximal {E : Type} [Field E] [NumberField E] (Q : Ideal (𝓞 E)) [hQ : Q.IsMaximal]
    (ϖ : 𝓞 E) (hϖ : ϖ ∈ Q) (m : ℕ) : (1 - ϖ ^ (m + 1)) ∉ Q := by
  intro h
  have h2 : ϖ ^ (m + 1) ∈ Q := Q.pow_mem_of_mem hϖ (m + 1) (Nat.succ_pos m)
  have h3 : (1 : 𝓞 E) ∈ Q := by simpa using Q.add_mem h h2
  exact hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h3)
private theorem algebraMap_cj_eq_star {E : Type} [Field E] [NumberField E] [StarRing E] (x : 𝓞 E) :
    algebraMap (𝓞 E) E (cj E x) = star (algebraMap (𝓞 E) E x) := by
  first
  | rfl
  | (simp [cj]; rfl)
  | simp [cj]
end PI.SqPairLocal
end
end

set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair
attribute [local instance] StModel.cr StModel.dom StModel.dvr StModel.hens StModel.fin
namespace PI.SqPairLocal
theorem _root_.solution : LocMat := by
  classical
  unfold LocMat
  intro E _ _ _ Q hQ M hC N hN u hu1 hu2 K
  haveI hQp : Q.IsPrime := hQ.isPrime
  have hone : (1 : 𝓞 E) ∉ Q := fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h1)
  have hϖ0 : M.ϖ ≠ 0 := by
    first
    | exact M.ϖ_ne
    | exact StModel.ϖ_ne (M := M)
    | exact StModel.ϖ_ne M
  obtain ⟨b, hb0, hb⟩ := exists_common_denominator' (Finset.univ.image (fun p : Fin N × Fin N => u p.1 p.2))
  obtain ⟨m, k, v, hv⟩ := exists_one_sub_pow_mul_pow_eq_mul M.ϖ b hb0
  set d : 𝓞 E := 1 - M.ϖ ^ (m + 1) with hd_def
  have hd : d ∉ Q := one_sub_pow_succ_not_mem_of_mem_maximal Q M.ϖ M.ϖ_Q m
  have hdd : d * d ∉ Q := fun hx => hd ((hQp.mem_or_mem hx).elim id id)
  have hdc : cj E d = d := by rw [hd_def, map_sub, map_one, map_pow, M.ϖ_cj]
  have hc0 : cj E (d * M.ϖ ^ k) = d * M.ϖ ^ k := by rw [map_mul, map_pow, hdc, M.ϖ_cj]
  have hU0 : ∀ a c, ∃ w : 𝓞 E,
      algebraMap (𝓞 E) E w = algebraMap (𝓞 E) E (d * M.ϖ ^ k) * u a c := by
    intro a c
    obtain ⟨w, hw⟩ := hb (u a c) (Finset.mem_image.mpr ⟨(a, c), Finset.mem_univ _, rfl⟩)
    refine ⟨v * w, ?_⟩
    rw [hv, map_mul, map_mul, ← hw]
    ring
  choose U hU using hU0
  obtain ⟨Um, hUm⟩ : ∃ Um : Matrix (Fin N) (Fin N) (𝓞 E), ∀ a c, Um a c = U a c :=
    ⟨Matrix.of U, fun _ _ => rfl⟩
  have hUι : (algebraMap (𝓞 E) E).mapMatrix Um = algebraMap (𝓞 E) E (d * M.ϖ ^ k) • u := by
    ext a c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hUm]
    exact hU a c
  have hUc : (algebraMap (𝓞 E) E).mapMatrix ((Um.map (cj E))ᵀ) =
      algebraMap (𝓞 E) E (d * M.ϖ ^ k) • uᴴ := by
    ext a c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.conjTranspose_apply]
    rw [algebraMap_cj_eq_star, hUm, hU, star_mul', ← algebraMap_cj_eq_star (d * M.ϖ ^ k), hc0]
  have hE1 : ∀ W : Matrix (Fin N) (Fin N) (𝓞 E),
      (algebraMap (𝓞 E) E).mapMatrix ((Um.map (cj E))ᵀ * W * Um) =
        (algebraMap (𝓞 E) E (d * M.ϖ ^ k) * algebraMap (𝓞 E) E (d * M.ϖ ^ k)) •
          (uᴴ * (algebraMap (𝓞 E) E).mapMatrix W * u) := by
    intro W
    rw [map_mul, map_mul, hUc, hUι]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hUU : (Um.map (cj E))ᵀ * Um =
      (d * M.ϖ ^ k * (d * M.ϖ ^ k)) • (1 : Matrix (Fin N) (Fin N) (𝓞 E)) := by
    have key : (algebraMap (𝓞 E) E).mapMatrix ((Um.map (cj E))ᵀ * Um) =
        (algebraMap (𝓞 E) E).mapMatrix
          ((d * M.ϖ ^ k * (d * M.ϖ ^ k)) • (1 : Matrix (Fin N) (Fin N) (𝓞 E))) := by
      have h1 := hE1 1
      rw [mul_one, map_one, mul_one, hu1] at h1
      rw [h1]
      ext a c
      by_cases hac : a = c
      · subst hac
        simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply_eq,
          smul_eq_mul, mul_one, map_mul]
      · simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
          Matrix.one_apply_ne hac, smul_eq_mul, mul_zero, map_zero]
    ext a c
    first
    | exact congrArg (fun X => X a c) key
    | exact IsFractionRing.injective (𝓞 E) E (congrArg (fun X => X a c) key)
  obtain ⟨τ, hτ⟩ := (M.unit_of d hd).exists_left_inv
  have hσd : M.σ (M.j d) = M.j d := by rw [← M.j_cj, hdc]
  have hστ : M.σ τ * M.j d = 1 := by
    have h1 := congrArg M.σ hτ
    rwa [map_mul, map_one, hσd] at h1
  have hσϖ : M.σ (M.j M.ϖ) = M.j M.ϖ := (M.mem₀ _).mp M.ϖ_mem
  obtain ⟨h, hdef⟩ : ∃ h : Matrix (Fin N) (Fin N) M.R, h = τ • M.j.mapMatrix Um := ⟨_, rfl⟩
  have hUj : M.j.mapMatrix Um = M.j d • h := by
    rw [hdef, smul_smul, show M.j d * τ = 1 by rw [mul_comm]; exact hτ, one_smul]
  have hUc' : M.j.mapMatrix ((Um.map (cj E))ᵀ) = M.j d • (h.map M.σ)ᵀ := by
    ext a c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply,
      smul_eq_mul, hdef, map_mul, M.j_cj]
    linear_combination (-(M.σ (M.j (Um c a)))) * hστ
  have hR1 : ∀ W : Matrix (Fin N) (Fin N) (𝓞 E),
      M.j.mapMatrix ((Um.map (cj E))ᵀ * W * Um) =
        (M.j d * M.j d) • ((h.map M.σ)ᵀ * M.j.mapMatrix W * h) := by
    intro W
    rw [map_mul, map_mul, hUc', hUj]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h2 : (M.j d * M.j d) • ((h.map M.σ)ᵀ * h) =
      M.j.mapMatrix ((d * M.ϖ ^ k * (d * M.ϖ ^ k)) • (1 : Matrix (Fin N) (Fin N) (𝓞 E))) := by
    have h1 := hR1 1
    rw [map_one, mul_one, mul_one, hUU] at h1
    exact h1.symm
  have hh : (h.map M.σ)ᵀ * h = (M.j M.ϖ ^ (2 * k)) • (1 : Matrix (Fin N) (Fin N) M.R) := by
    have h3 : (h.map M.σ)ᵀ * h = (τ * τ) •
        M.j.mapMatrix ((d * M.ϖ ^ k * (d * M.ϖ ^ k)) • (1 : Matrix (Fin N) (Fin N) (𝓞 E))) := by
      rw [← h2, smul_smul,
        show τ * τ * (M.j d * M.j d) = 1 by linear_combination (τ * M.j d + 1) * hτ, one_smul]
    rw [h3]
    ext a c
    by_cases hac : a = c
    · subst hac
      simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one, map_mul, map_pow]
      linear_combination (τ * M.j d + 1) * M.j M.ϖ ^ (2 * k) * hτ
    · simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.one_apply_ne hac, smul_eq_mul, mul_zero, map_zero]
  obtain ⟨e, f, he, heS, hef⟩ :=
    hC M.R M.σ M.σσ M.R₀ M.mem₀ M.unram ⟨M.j M.ϖ, M.ϖ_mem⟩ M.ϖ_irr N hN k h hh
  choose Y Z hYZ using fun a c => M.dense (e a c) (2 * k + K)
  obtain ⟨Ym, hYm⟩ : ∃ Ym : Matrix (Fin N) (Fin N) (𝓞 E), ∀ a c, Ym a c = Y a c :=
    ⟨Matrix.of Y, fun _ _ => rfl⟩
  obtain ⟨Zm, hZm⟩ : ∃ Zm : Matrix (Fin N) (Fin N) M.R, ∀ a c, Zm a c = Z a c :=
    ⟨Matrix.of Z, fun _ _ => rfl⟩
  have hYj : M.j.mapMatrix Ym = e - (M.j M.ϖ ^ (2 * k + K)) • Zm := by
    ext a c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, hYm, hZm]
    linear_combination -(hYZ a c)
  have hYY : M.j.mapMatrix (Ym * Ym - Ym) = (M.j M.ϖ ^ (2 * k + K)) •
      (Zm - e * Zm - Zm * e + (M.j M.ϖ ^ (2 * k + K)) • (Zm * Zm)) := by
    rw [map_sub, map_mul, hYj]
    simp only [mul_sub, sub_mul, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_add, smul_smul, he]
    abel
  have hYcj : M.j.mapMatrix ((Ym.map (cj E))ᵀ) = ((M.j.mapMatrix Ym).map M.σ)ᵀ := by
    ext a c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply, M.j_cj]
  have hs : ((e - (M.j M.ϖ ^ (2 * k + K)) • Zm).map M.σ)ᵀ =
      (e.map M.σ)ᵀ - (M.j M.ϖ ^ (2 * k + K)) • (Zm.map M.σ)ᵀ := by
    ext a c
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, map_sub, map_mul, map_pow, hσϖ]
  have hA : M.j.mapMatrix (Ym + (Ym.map (cj E))ᵀ - 1) =
      (M.j M.ϖ ^ (2 * k + K)) • (-(Zm + (Zm.map M.σ)ᵀ)) := by
    rw [map_sub, map_add, map_one, hYcj, hYj, hs, heS]
    simp only [smul_neg, smul_add]
    abel
  have hcT : ((algebraMap (𝓞 E) E).mapMatrix Ym)ᴴ =
      (algebraMap (𝓞 E) E).mapMatrix ((Ym.map (cj E))ᵀ) := by
    ext a c
    simp only [Matrix.conjTranspose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.transpose_apply]
    exact (algebraMap_cj_eq_star _).symm
  have hsq : (algebraMap (𝓞 E) E).mapMatrix Ym * (algebraMap (𝓞 E) E).mapMatrix Ym -
      (algebraMap (𝓞 E) E).mapMatrix Ym = (algebraMap (𝓞 E) E).mapMatrix (Ym * Ym - Ym) := by
    rw [map_sub, map_mul]
  have hpl : (algebraMap (𝓞 E) E).mapMatrix Ym + ((algebraMap (𝓞 E) E).mapMatrix Ym)ᴴ - 1 =
      (algebraMap (𝓞 E) E).mapMatrix (Ym + (Ym.map (cj E))ᵀ - 1) := by
    rw [hcT, map_sub, map_add, map_one]
  have hdetA : ∀ (A : Matrix (Fin N) (Fin N) (𝓞 E)) (V : Matrix (Fin N) (Fin N) M.R),
      M.j.mapMatrix A = (M.j M.ϖ ^ (2 * k + K)) • V →
      ∀ a c, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * A a c = M.ϖ ^ K * w := by
    intro A V hAV a c
    apply M.detect
    refine ⟨M.j M.ϖ ^ (2 * k) * V a c, ?_⟩
    have h1 : M.j (A a c) = M.j M.ϖ ^ (2 * k + K) * V a c := congrArg (fun X => X a c) hAV
    rw [h1, pow_add]
    ring
  have hGen : ∀ (W : Matrix (Fin N) (Fin N) (𝓞 E)) (mm : ℕ) (V : Matrix (Fin N) (Fin N) M.R),
      (h.map M.σ)ᵀ * M.j.mapMatrix W * h = (M.j M.ϖ ^ (2 * k + mm)) • V →
      ∀ a c, DivAt Q (M.ϖ ^ mm) ((uᴴ * (algebraMap (𝓞 E) E).mapMatrix W * u) a c) := by
    intro W mm V hV a c
    refine divAt_conj M.ϖ (d * d) hϖ0 hdd k mm ((Um.map (cj E))ᵀ * W * Um) _ ?_ ?_ a c
    · intro a' c'
      have h1 : algebraMap (𝓞 E) E (((Um.map (cj E))ᵀ * W * Um) a' c') =
          (algebraMap (𝓞 E) E (d * M.ϖ ^ k) * algebraMap (𝓞 E) E (d * M.ϖ ^ k)) *
            (uᴴ * (algebraMap (𝓞 E) E).mapMatrix W * u) a' c' :=
        congrArg (fun X => X a' c') (hE1 W)
      rw [h1]
      simp only [map_mul, map_pow]
      ring
    · intro a' c'
      apply M.detect
      refine ⟨M.j d * M.j d * V a' c', ?_⟩
      have h1 := hR1 W
      rw [hV] at h1
      have h2 : M.j (((Um.map (cj E))ᵀ * W * Um) a' c') =
          M.j d * M.j d * (M.j M.ϖ ^ (2 * k + mm) * V a' c') := congrArg (fun X => X a' c') h1
      rw [h2]
      ring
  have hV2 : (h.map M.σ)ᵀ * M.j.mapMatrix Ym * h = (M.j M.ϖ ^ (2 * k + 0)) •
      (f - (M.j M.ϖ ^ K) • ((h.map M.σ)ᵀ * Zm * h)) := by
    rw [hYj, mul_sub, sub_mul, mul_assoc _ e h, hef, ← mul_assoc, hh, add_zero, pow_add]
    simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_sub, smul_smul]
  have hV4 : (h.map M.σ)ᵀ * M.j.mapMatrix (Ym * Ym - Ym) * h = (M.j M.ϖ ^ (2 * k + K)) •
      ((h.map M.σ)ᵀ * (Zm - e * Zm - Zm * e + (M.j M.ϖ ^ (2 * k + K)) • (Zm * Zm)) * h) := by
    rw [hYY]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  have hV6 : (h.map M.σ)ᵀ * M.j.mapMatrix (Ym + (Ym.map (cj E))ᵀ - 1) * h =
      (M.j M.ϖ ^ (2 * k + K)) • ((h.map M.σ)ᵀ * (-(Zm + (Zm.map M.σ)ᵀ)) * h) := by
    rw [hA]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  refine ⟨(algebraMap (𝓞 E) E).mapMatrix Ym, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a c
    exact intAt_of_divAt_zero M.ϖ (divAt_of_map Ym (M.ϖ ^ 0)
      (fun a' c' => ⟨1, hone, Ym a' c', by simp⟩) a c)
  · intro a c
    exact intAt_of_divAt_zero M.ϖ (hGen Ym 0 _ hV2 a c)
  · intro a c
    rw [hsq]
    exact divAt_of_map _ _ (hdetA _ _ hYY) a c
  · intro a c
    rw [hsq]
    exact hGen _ K _ hV4 a c
  · intro a c
    rw [hpl]
    exact divAt_of_map _ _ (hdetA _ _ hA) a c
  · intro a c
    rw [hpl]
    exact hGen _ K _ hV6 a c
end PI.SqPairLocal
