-- Prove2me | solution 1 for QAlgorithms.GottesmanIntro.knillLaflamme
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T00:00:25.528305+00:00
-- url     : https://prove2.me/submissions/4fa931a2-0423-48e6-8217-e35d4d6ba1bf

import Definitions.Def_QAlgorithms_Defs_FTCircuit
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Center
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open QAlgorithms QAlgorithms.Stabilizer
open scoped ComplexConjugate Matrix

namespace KnillLaflammeProof
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma act_lin (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act A v = Matrix.toEuclideanLin A v := rfl

omit [DecidableEq ι] in
private lemma act_pure (x v : EuclideanSpace ℂ ι) :
    act (pureDensity x) v = inner ℂ x v • x := by
  ext i
  simp only [act, pureDensity, Matrix.mulVec, dotProduct, Matrix.of_apply,
    WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply]
  simp_rw [mul_assoc, mul_comm (x i), ← Finset.sum_mul]
  simp only [Complex.star_def, mul_comm]

omit [DecidableEq ι] in
private lemma pure_conj (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    A * pureDensity v * Aᴴ = pureDensity (act A v) := by
  ext i j
  simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply, Matrix.conjTranspose_apply,
    act, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp]
  simp only [map_sum, map_mul, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

omit [Fintype ι] [DecidableEq ι] in
private lemma pure_smul (c : ℂ) (v : EuclideanSpace ℂ ι) :
    pureDensity (c • v) = (c * conj c) • pureDensity v := by
  ext i j
  simp only [pureDensity, Matrix.of_apply, PiLp.smul_apply, smul_eq_mul,
    map_mul, Matrix.smul_apply]
  ring

omit [DecidableEq ι] in
private lemma trace_pure (v : EuclideanSpace ℂ ι) :
    (pureDensity v).trace = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  change (∑ i, v i * conj (v i)) = ((‖v‖ ^ 2 : ℝ) : ℂ)
  rw [EuclideanSpace.norm_sq_eq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma trace_kraus {m : ℕ} (R : Fin m → Matrix ι ι ℂ)
    (hR : IsKrausFamily R) (ρ : Matrix ι ι ℂ) :
    (krausApply R ρ).trace = ρ.trace := by
  simp only [krausApply, Matrix.trace_sum]
  conv_lhs => arg 2; ext j; rw [Matrix.trace_mul_cycle]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hR, Matrix.one_mul]

private lemma kraus_collinear {m : ℕ} (R : Fin m → Matrix ι ι ℂ)
    (v ψ : EuclideanSpace ℂ ι) (c : ℂ)
    (h : krausApply R (pureDensity v) = c • pureDensity ψ) :
    ∀ j, act (R j) v ∈ Submodule.span ℂ {ψ} := by
  intro j
  rw [← (Submodule.span ℂ {ψ}).orthogonal_orthogonal]
  apply (Submodule.mem_orthogonal _ _).2
  intro w hw
  have hwψ : inner ℂ w ψ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp hw
  have heq := congrArg (fun M => (inner ℂ w (act M w)).re) h
  have form : ∀ x : EuclideanSpace ℂ ι,
      inner ℂ w (act (pureDensity x) w) = (‖inner ℂ x w‖ : ℂ) ^ 2 := by
    intro x
    rw [act_pure, inner_smul_right, ← inner_conj_symm w x]
    simpa only [mul_comm] using Complex.conj_mul' (inner ℂ x w)
  have hs : act (krausApply R (pureDensity v)) w =
      ∑ a, act (pureDensity (act (R a) v)) w := by
    simp only [krausApply, pure_conj, act_lin, map_sum, LinearMap.sum_apply]
  rw [hs] at heq
  have hs' : act (c • pureDensity ψ) w = c • act (pureDensity ψ) w := by
    simp [act_lin]
  rw [hs', act_pure, inner_smul_right, inner_smul_right, hwψ, mul_zero, mul_zero] at heq
  have hz : ∑ a, ‖inner ℂ (act (R a) v) w‖ ^ 2 = 0 := by
    simpa only [inner_sum, form, Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.zero_re] using heq
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg
    ‖inner ℂ (act (R a) v) w‖)).mp hz j (Finset.mem_univ j)
  have hz' : inner ℂ (act (R j) v) w = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hj)
  exact (inner_eq_zero_symm).mp hz'

omit [DecidableEq ι] in
private lemma act_mul (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A * B) v = act A (act B v) := by
  simp only [act, Matrix.mulVec_mulVec, WithLp.ofLp_toLp]

private lemma inner_act (A : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ x (act Aᴴ y) = inner ℂ (act A x) y := by
  rw [act_lin, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact LinearMap.adjoint_inner_right _ _ _

omit [DecidableEq ι] in
private lemma unit_normalize (x : EuclideanSpace ℂ ι) (hx : x ≠ 0) :
    ‖((‖x‖ : ℂ)⁻¹) • x‖ = 1 := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

omit [DecidableEq ι] in
private lemma scalar_on_subspace (C : Submodule ℂ (EuclideanSpace ℂ ι))
    (T : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (hT : ∀ x ∈ C, ‖x‖ = 1 → T x ∈ Submodule.span ℂ {x}) :
    ∃ c : ℂ, ∀ x ∈ C, T x = c • x := by
  classical
  have hall : ∀ x ∈ C, T x ∈ Submodule.span ℂ {x} := by
    intro x hx
    by_cases hz : x = 0
    · simp [hz]
    have hn := hT (((‖x‖ : ℂ)⁻¹) • x) (C.smul_mem _ hx) (unit_normalize x hz)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hn
    refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
    rw [map_smul, smul_comm] at hc
    exact (smul_right_injective _ (inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr hz)))) hc
  let f : C →ₗ[ℂ] C := (T.comp C.subtype).codRestrict C (fun x =>
    ((Submodule.span_singleton_le_iff_mem _ _).mpr x.property) (hall x x.property))
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent (f := f)
    (fun x => by
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hall x x.property)
      have hax : a • x = f x := Subtype.ext ha
      intro hi
      exact (linearIndependent_fin2.mp (LinearIndependent.pair_symm_iff.mp hi)).2 a hax)
  refine ⟨c, fun x hx => ?_⟩
  exact congrArg Subtype.val (LinearMap.congr_fun hc ⟨x, hx⟩)

private theorem necessary (C : Submodule ℂ (EuclideanSpace ℂ ι))
    (S : Set (Matrix ι ι ℂ)) (h : Corrects C S) :
    ∃ c : Matrix ι ι ℂ → ℂ, ∀ E ∈ S, ∀ ψ ∈ C, ‖ψ‖ = 1 →
      inner ℂ ψ (act (Eᴴ * E) ψ) = c E := by
  classical
  obtain ⟨Φ, ⟨m, R, hR, hΦ⟩, h⟩ := h
  have scalars : ∀ E ∈ S, ∀ j, ∃ c : ℂ, ∀ ψ ∈ C,
      act (R j) (act E ψ) = c • ψ := by
    intro E hE j
    apply scalar_on_subspace C ((R j).toEuclideanLin.comp E.toEuclideanLin)
    intro ψ hψ hu
    apply kraus_collinear R (act E ψ) ψ ((‖act E ψ‖ ^ 2 : ℝ) : ℂ) _ j
    rw [← hΦ]
    exact h E hE ψ hψ hu
  let a : Matrix ι ι ℂ → Fin m → ℂ := fun E j =>
    if hE : E ∈ S then (scalars E hE j).choose else 0
  refine ⟨fun E => ∑ j, conj (a E j) * a E j, ?_⟩
  intro E hE ψ hψ hu
  have ha : ∀ j, act (R j) (act E ψ) = a E j • ψ := by
    intro j
    simpa only [a, dif_pos hE] using ((scalars E hE j).choose_spec ψ hψ)
  have hm : act (∑ j, (R j)ᴴ * R j) (act E ψ) = act E ψ := by
    rw [hR]
    simp [act]
  have hsum : inner ℂ (act E ψ) (act E ψ) =
      ∑ j, inner ℂ (act (R j) (act E ψ)) (act (R j) (act E ψ)) := by
    nth_rw 2 [← hm]
    simp only [act_lin, map_sum, LinearMap.sum_apply, inner_sum]
    apply Finset.sum_congr rfl
    intro j _
    change inner ℂ (act E ψ) (act ((R j)ᴴ * R j) (act E ψ)) = _
    rw [act_mul, inner_act]
    rfl
  rw [act_mul, inner_act, hsum]
  have hip : inner ℂ ψ ψ = 1 := by simp [inner_self_eq_norm_sq_to_K, hu]
  simp only [ha, inner_smul_left, inner_smul_right, hip, mul_one]
  simp only [mul_comm]


private theorem self_gram (𝓔 : Submodule ℂ (Matrix ι ι ℂ))
    (C : Submodule ℂ (EuclideanSpace ℂ ι))
    (c : Matrix ι ι ℂ → ℂ)
    (h : ∀ E ∈ 𝓔, ∀ ψ ∈ C, ‖ψ‖ = 1 → inner ℂ ψ (act (Eᴴ * E) ψ) = c E) :
    ∀ E ∈ 𝓔, ∀ x ∈ C, ∀ y ∈ C,
      inner ℂ (act E x) (act E y) = c E * inner ℂ x y := by
  intro E hE
  have diag : ∀ x ∈ C, inner ℂ (act E x) (act E x) = c E * inner ℂ x x := by
    intro x hx
    by_cases hz : x = 0
    · simp [hz, act_lin]
    have hu := h E hE (((‖x‖ : ℂ)⁻¹) • x)
      (C.smul_mem ((‖x‖ : ℂ)⁻¹) hx) (unit_normalize x hz)
    rw [act_mul, inner_act] at hu
    simp only [act_lin, map_smul, inner_smul_left, inner_smul_right,
      map_inv₀, Complex.conj_ofReal] at hu
    rw [inner_self_eq_norm_sq_to_K x]
    have hn : (↑‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    field_simp [hn] at hu
    change inner ℂ (act E x) (act E x) = c E * (↑‖x‖ : ℂ)^2
    change inner ℂ (act E x) (act E x) = _ at hu
    rw [hu]
    ring
  intro x hx y hy
  have hp := diag (x+y) (C.add_mem hx hy)
  have hm := diag (x-y) (C.sub_mem hx hy)
  have hpi := diag (x+Complex.I • y) (C.add_mem hx (C.smul_mem _ hy))
  have hmi := diag (x-Complex.I • y) (C.sub_mem hx (C.smul_mem _ hy))
  simp only [act_lin, map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_I] at hp hm hpi hmi
  simp only [act_lin]
  linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
    (hp - hm - Complex.I*hpi + Complex.I*hmi) / 4


private theorem cross_gram (𝓔 : Submodule ℂ (Matrix ι ι ℂ))
    (C : Submodule ℂ (EuclideanSpace ℂ ι))
    (c : Matrix ι ι ℂ → ℂ)
    (h : ∀ E ∈ 𝓔, ∀ ψ ∈ C, ‖ψ‖ = 1 → inner ℂ ψ (act (Eᴴ * E) ψ) = c E) :
    ∃ g : Matrix ι ι ℂ → Matrix ι ι ℂ → ℂ,
      ∀ E ∈ 𝓔, ∀ F ∈ 𝓔, ∀ x ∈ C, ∀ y ∈ C,
        inner ℂ (act E x) (act F y) = g E F * inner ℂ x y := by
  refine ⟨fun E F => (c (E + F) - c (E - F) - Complex.I * c (E + Complex.I • F) +
    Complex.I * c (E - Complex.I • F)) / 4, ?_⟩
  intro E hE F hF x hx y hy
  have hp := self_gram 𝓔 C c h (E+F) (𝓔.add_mem hE hF) x hx y hy
  have hm := self_gram 𝓔 C c h (E-F) (𝓔.sub_mem hE hF) x hx y hy
  have hpi := self_gram 𝓔 C c h (E+Complex.I • F)
    (𝓔.add_mem hE (𝓔.smul_mem _ hF)) x hx y hy
  have hmi := self_gram 𝓔 C c h (E-Complex.I • F)
    (𝓔.sub_mem hE (𝓔.smul_mem _ hF)) x hx y hy
  simp only [act_lin, map_add, map_sub, map_smul, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_I] at hp hm hpi hmi
  simp only [act_lin]
  linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
    (hp - hm - Complex.I*hpi + Complex.I*hmi) / 4


private lemma kraus_of_collinear {m : ℕ} (R : Fin m → Matrix ι ι ℂ)
    (hR : IsKrausFamily R) (v ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (h : ∀ j, act (R j) v ∈ Submodule.span ℂ {ψ}) :
    krausApply R (pureDensity v) = ((‖v‖ ^ 2 : ℝ) : ℂ) • pureDensity ψ := by
  choose c hc using fun j => Submodule.mem_span_singleton.mp (h j)
  have heq : krausApply R (pureDensity v) =
      (∑ j, c j * conj (c j)) • pureDensity ψ := by
    simp only [krausApply, pure_conj, ← hc, pure_smul, Finset.sum_smul]
  have htrace := congrArg Matrix.trace heq
  rw [trace_kraus R hR, Matrix.trace_smul, trace_pure, trace_pure, hψ] at htrace
  norm_num only [one_pow, Complex.ofReal_one, smul_eq_mul, mul_one] at htrace
  rw [heq, ← htrace]

private lemma rect_mul {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ]
    (A : Matrix α β ℂ) (B : Matrix β γ ℂ) (x : EuclideanSpace ℂ γ) :
    (A * B).toEuclideanLin x = A.toEuclideanLin (B.toEuclideanLin x) := by
  simp only [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

private theorem orthogonal_recovery (d s : ℕ)
    (U : Matrix ι (Fin d) ℂ) (V : Fin s → Matrix ι (Fin d) ℂ)
    (hU : Uᴴ * U = 1) (hV : ∀ k l, (V k)ᴴ * V l = if k = l then 1 else 0) :
    ∃ Φ : Superop ι ι, IsChannel Φ ∧
      ∀ (a : Fin s → ℂ) (x : EuclideanSpace ℂ (Fin d)), ‖U.toEuclideanLin x‖ = 1 →
      Φ (pureDensity (∑ k, a k • (V k).toEuclideanLin x)) =
        ((‖∑ k, a k • (V k).toEuclideanLin x‖ ^ 2 : ℝ) : ℂ) • pureDensity (U.toEuclideanLin x) := by
  classical
  let P : Matrix ι ι ℂ := ∑ k, V k * (V k)ᴴ
  let A : Fin s → Matrix ι ι ℂ := fun k => U * (V k)ᴴ
  let B : Matrix ι ι ℂ := 1 - P
  have hPV : ∀ k, P * V k = V k := by
    intro k
    simp only [P, Matrix.sum_mul, Matrix.mul_assoc, hV]
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hl
      rw [if_neg hl, Matrix.mul_zero]
    · simp
  have hPP : P * P = P := by
    conv_lhs => arg 2; unfold P
    rw [Finset.mul_sum]
    simp only [← Matrix.mul_assoc, hPV]
    rfl
  have hPadj : Pᴴ = P := by
    simp only [P, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hA : ∀ k, (A k)ᴴ * A k = V k * (V k)ᴴ := by
    intro k
    simp only [A, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
  have hB : Bᴴ * B = 1 - P := by
    have hb : Bᴴ = B := by simp only [B, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPadj]
    rw [hb]
    dsimp [B]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hPP]
    abel
  let R : Fin (s+1) → Matrix ι ι ℂ := Fin.cases B A
  have hR : IsKrausFamily R := by
    unfold IsKrausFamily
    rw [Fin.sum_univ_succ]
    change Bᴴ * B + ∑ k, (A k)ᴴ * A k = 1
    simp only [hB,hA]
    change 1-P+P=1
    abel
  have hAV : ∀ k l, A k * V l = if k=l then U else 0 := by
    intro k l
    simp only [A,Matrix.mul_assoc,hV]
    split_ifs <;> simp
  have hBV : ∀ k, B * V k = 0 := by
    intro k
    simp only [B, Matrix.sub_mul,Matrix.one_mul,hPV,sub_self]
  refine ⟨krausApply R, ⟨s+1,R,hR,fun _ => rfl⟩, ?_⟩
  intro a x hx
  apply kraus_of_collinear R hR _ _ hx
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · change act B _ ∈ _
    have hz : act B (∑ k, a k • (V k).toEuclideanLin x) = 0 := by
      simp only [act_lin, map_sum, map_smul, ← rect_mul, hBV, map_zero,
        LinearMap.zero_apply, smul_zero, Finset.sum_const_zero]
    rw [hz]
    exact Submodule.zero_mem _
  · change act (A k) _ ∈ _
    have ha : act (A k) (∑ l, a l • (V l).toEuclideanLin x) = a k • U.toEuclideanLin x := by
      simp only [act_lin,map_sum,map_smul,← rect_mul,hAV]
      rw [Finset.sum_eq_single k]
      · simp
      · intro l _ hl
        rw [if_neg (Ne.symm hl)]
        simp
      · simp
    rw [ha]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

omit [DecidableEq ι] in
private lemma columns_inner {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v w : κ → EuclideanSpace ℂ ι) (i j : κ) :
    ((Matrix.of fun p k => (v k) p : Matrix ι κ ℂ)ᴴ * (Matrix.of fun p k => (w k) p : Matrix ι κ ℂ)) i j =
      inner ℂ (v i) (w j) := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct,Pi.star_apply,Complex.star_def,Matrix.of_apply,mul_comm]

omit [Fintype ι] [DecidableEq ι] in
private lemma columns_action {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v : κ → EuclideanSpace ℂ ι) (x : EuclideanSpace ℂ κ) :
    (Matrix.of fun p k => (v k) p : Matrix ι κ ℂ).toEuclideanLin x = ∑ k, x k • v k := by
  ext p
  simp only [Matrix.toLpLin_apply,WithLp.ofLp_toLp,Matrix.mulVec,dotProduct,
    WithLp.ofLp_sum, Finset.sum_apply,Matrix.of_apply,PiLp.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

private theorem recover_gram (𝓔 : Submodule ℂ (Matrix ι ι ℂ))
    (C : Submodule ℂ (EuclideanSpace ℂ ι))
    (g : Matrix ι ι ℂ → Matrix ι ι ℂ → ℂ)
    (hg : ∀ E ∈ 𝓔, ∀ F ∈ 𝓔, ∀ x ∈ C, ∀ y ∈ C,
      inner ℂ (act E x) (act F y) = g E F * inner ℂ x y) :
    Corrects C (𝓔 : Set (Matrix ι ι ℂ)) := by
  classical
  by_cases hunit : ∃ ψ ∈ C, ‖ψ‖ = 1
  swap
  · refine ⟨fun ρ => ρ, ⟨1, fun _ => 1, ?_, ?_⟩, ?_⟩
    · simp [IsKrausFamily]
    · intro ρ
      simp [krausApply]
    · intro E _ ψ hψ hu
      exact False.elim (hunit ⟨ψ,hψ,hu⟩)
  obtain ⟨ψ₀,hψ₀,hu₀⟩ := hunit
  have hi₀ : inner ℂ ψ₀ ψ₀ = 1 := by simp [inner_self_eq_norm_sq_to_K,hu₀]
  let ev : 𝓔 →ₗ[ℂ] EuclideanSpace ℂ ι :=
    { toFun := fun E => act E ψ₀
      map_add' := by intro E F; simp [act_lin]
      map_smul' := by intro a E; simp [act_lin] }
  let S := ev.range
  let s := Module.finrank ℂ S
  let b := stdOrthonormalBasis ℂ S
  obtain ⟨F,hF⟩ : ∃ F : Fin s → 𝓔, ∀ k, ev (F k) = (b k : EuclideanSpace ℂ ι) := by
    choose F hF using fun k => (b k).property
    exact ⟨F,hF⟩
  let d := Module.finrank ℂ C
  let bC := stdOrthonormalBasis ℂ C
  let U : Matrix ι (Fin d) ℂ := Matrix.of fun i j => (bC j : EuclideanSpace ℂ ι) i
  let V : Fin s → Matrix ι (Fin d) ℂ := fun k => Matrix.of fun i j => act (F k) (bC j) i
  have hcoeff : ∀ E F : 𝓔, g E F = inner ℂ (ev E) (ev F) := by
    intro E F
    have hh := hg E E.property F F.property ψ₀ hψ₀ ψ₀ hψ₀
    rw [hi₀,mul_one] at hh
    exact hh.symm
  have hU : Uᴴ * U = 1 := by
    ext i j
    change ((Matrix.of fun p k => (bC k : EuclideanSpace ℂ ι) p : Matrix ι (Fin d) ℂ)ᴴ *
      (Matrix.of fun p k => (bC k : EuclideanSpace ℂ ι) p : Matrix ι (Fin d) ℂ)) i j = _
    rw [columns_inner]
    exact bC.inner_eq_ite i j
  have hV : ∀ k l, (V k)ᴴ * V l = if k=l then 1 else 0 := by
    intro k l
    have hscalar : g (F k) (F l) = if k=l then 1 else 0 := by
      rw [hcoeff,hF,hF]
      exact b.inner_eq_ite k l
    ext i j
    change ((Matrix.of fun p t => act (F k) (bC t : EuclideanSpace ℂ ι) p : Matrix ι (Fin d) ℂ)ᴴ *
      (Matrix.of fun p t => act (F l) (bC t : EuclideanSpace ℂ ι) p : Matrix ι (Fin d) ℂ)) i j = _
    rw [columns_inner,hg _ (F k).property _ (F l).property _ (bC i).property _ (bC j).property,hscalar]
    by_cases hkl : k=l
    · simp only [hkl,if_true,one_mul]
      exact bC.inner_eq_ite i j
    · simp only [hkl,if_false,zero_mul,Matrix.zero_apply]
  obtain ⟨Φ,hΦ,hrec⟩ := orthogonal_recovery d s U V hU hV
  refine ⟨Φ,hΦ,?_⟩
  intro E hE ψ hψ hu
  let e : 𝓔 := ⟨E,hE⟩
  let z : S := ⟨ev e, LinearMap.mem_range_self ev e⟩
  let a : Fin s → ℂ := fun k => b.repr z k
  let e' : 𝓔 := ∑ k, a k • F k
  have heval : ev e' = ev e := by
    change ev (∑ k, a k • F k) = ev e
    simp only [map_sum,map_smul,hF]
    simpa only [Submodule.coe_sum,Submodule.coe_smul] using
      congrArg (fun z : S => (z : EuclideanSpace ℂ ι)) (b.sum_repr z)
  have hzero : ∀ x : C, act ((e-e' : 𝓔) : Matrix ι ι ℂ) x = 0 := by
    intro x
    have hz : ev (e-e') = 0 := by rw [map_sub, heval, sub_self]
    have hc : g ((e-e' : 𝓔) : Matrix ι ι ℂ) ((e-e' : 𝓔) : Matrix ι ι ℂ) = 0 := by
      rw [hcoeff (e-e') (e-e'),hz]
      simp
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [hg _ (e-e').property _ (e-e').property x x.property x x.property, hc, zero_mul]
  have hexp : act E ψ = ∑ k, a k • act (F k) ψ := by
    have hz := hzero ⟨ψ,hψ⟩
    have he : act E ψ = act (e' : Matrix ι ι ℂ) ψ := by
      apply sub_eq_zero.mp
      simpa only [Submodule.coe_sub, act_lin, map_sub, LinearMap.sub_apply] using hz
    rw [he]
    change act ((∑ k, a k • F k : 𝓔) : Matrix ι ι ℂ) ψ = _
    simp only [Submodule.coe_sum,Submodule.coe_smul,act_lin,map_sum,map_smul,
      LinearMap.sum_apply,LinearMap.smul_apply]
  let v := bC.repr ⟨ψ,hψ⟩
  have huv : U.toEuclideanLin v = ψ := by
    change (Matrix.of fun p k => (bC k : EuclideanSpace ℂ ι) p : Matrix ι (Fin d) ℂ).toEuclideanLin v = ψ
    rw [columns_action]
    simpa only [Submodule.coe_sum,Submodule.coe_smul] using
      congrArg (fun z : C => (z : EuclideanSpace ℂ ι)) (bC.sum_repr ⟨ψ,hψ⟩)
  have hv : ∀ k, (V k).toEuclideanLin v = act (F k) ψ := by
    intro k
    change (Matrix.of fun p t => act (F k) (bC t : EuclideanSpace ℂ ι) p : Matrix ι (Fin d) ℂ).toEuclideanLin v = _
    rw [columns_action,← huv]
    change _ = (F k).val.toEuclideanLin (U.toEuclideanLin v)
    change _ = (F k).val.toEuclideanLin
      ((Matrix.of fun p t => (bC t : EuclideanSpace ℂ ι) p : Matrix ι (Fin d) ℂ).toEuclideanLin v)
    rw [columns_action,map_sum]
    simp only [map_smul]
    rfl
  have hr := hrec a v (huv.symm ▸ hu)
  simp only [hv,huv] at hr
  rw [hexp]
  exact hr

end KnillLaflammeProof

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝓔 : Submodule ℂ (Matrix ι ι ℂ)) (C : Submodule ℂ (EuclideanSpace ℂ ι)) :
    Corrects C (𝓔 : Set (Matrix ι ι ℂ)) ↔
      ∃ c : Matrix ι ι ℂ → ℂ, ∀ E ∈ 𝓔, ∀ ψ ∈ C, ‖ψ‖ = 1 → inner ℂ ψ (act (Eᴴ * E) ψ) = c E := by
  constructor
  · exact KnillLaflammeProof.necessary C (𝓔 : Set (Matrix ι ι ℂ))
  · rintro ⟨c,hc⟩
    obtain ⟨g,hg⟩ := KnillLaflammeProof.cross_gram 𝓔 C c hc
    exact KnillLaflammeProof.recover_gram 𝓔 C g hg
