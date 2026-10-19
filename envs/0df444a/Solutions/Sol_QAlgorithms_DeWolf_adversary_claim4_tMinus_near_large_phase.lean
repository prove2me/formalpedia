-- Prove2me | solution 1 for QAlgorithms.DeWolf.adversary_claim4_tMinus_near_large_phase
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:27:39.241638+00:00
-- url     : https://prove2.me/submissions/1e0f1c23-8ae4-426b-9d62-0ec9762e7040

import Definitions.Def_QAlgorithms_Defs_Adversary
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
open QAlgorithms
open scoped ComplexConjugate NNReal

private lemma eigen_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E →ₗᵢ[ℂ] E) {μ : ℂ} {v : E} (hv : v ≠ 0) (he : U v = μ • v) : ‖μ‖ = 1 := by
  have h := U.norm_map v
  rw [he, norm_smul] at h
  exact (mul_right_cancel₀ (norm_ne_zero_iff.mpr hv) (h.trans (one_mul _).symm))

private lemma eigen_orth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E →ₗᵢ[ℂ] E) {μ ν : ℂ} (hne : μ ≠ ν) {v w : E}
    (hv : U v = μ • v) (hw : U w = ν • w) : inner ℂ v w = 0 := by
  by_cases hz : v = 0
  · simp [hz]
  have hm : μ * conj μ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, eigen_norm U hz hv]; norm_num
  have hi := U.inner_map_map v w
  rw [hv, hw, inner_smul_left, inner_smul_right] at hi
  have he : ν * inner ℂ v w = μ * inner ℂ v w := by
    have := congrArg (fun z : ℂ => μ * z) hi
    calc
      ν * inner ℂ v w = (μ * conj μ) * (ν * inner ℂ v w) := by rw [hm, one_mul]
      _ = μ * inner ℂ v w := by linear_combination this
  by_contra hn
  exact hne (mul_right_cancel₀ hn he).symm

private lemma eigen_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U : E →ₗᵢ[ℂ] E) :
    (⨆ μ : ℂ, Module.End.eigenspace U.toLinearMap μ) = ⊤ := by
  classical
  let V : Submodule ℂ E := ⨆ μ : ℂ, Module.End.eigenspace U.toLinearMap μ
  suffices Vᗮ = ⊥ from Submodule.orthogonal_eq_bot_iff.mp this
  by_contra hn
  have : Nontrivial Vᗮ := (Submodule.nontrivial_iff_ne_bot).mpr hn
  have hInv : ∀ w ∈ Vᗮ, U w ∈ Vᗮ := by
    intro w hw
    rw [Submodule.mem_orthogonal]
    intro v hv
    obtain ⟨f, hf, hs⟩ := (Submodule.mem_iSup_iff_exists_finsupp
      (fun μ : ℂ => Module.End.eigenspace U.toLinearMap μ) v).mp hv
    rw [← hs]
    change inner ℂ (∑ μ ∈ f.support, f μ) (U w) = 0
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro μ hμ
    by_cases hz : f μ = 0
    · simp [hz]
    have he : U (f μ) = μ • f μ := Module.End.mem_eigenspace_iff.mp (hf μ)
    have hμne : conj μ ≠ 0 := by
      apply (map_ne_zero (starRingEnd ℂ)).mpr
      intro h
      have := eigen_norm U hz he
      simp [h] at this
    have hi := U.inner_map_map (f μ) w
    rw [he, inner_smul_left,
      (V.mem_orthogonal w).mp hw (f μ) (le_iSup (fun μ => Module.End.eigenspace U.toLinearMap μ) μ (hf μ))] at hi
    exact (mul_eq_zero.mp hi).resolve_left hμne
  let T : Vᗮ →ₗ[ℂ] Vᗮ := U.toLinearMap.restrict hInv
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv, hvne⟩ := hμ.exists_hasEigenvector
  have he : U (v : E) = μ • (v : E) := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hv)
  have hvV : (v : E) ∈ V := le_iSup (fun μ => Module.End.eigenspace U.toLinearMap μ) μ
    (Module.End.mem_eigenspace_iff.mpr he)
  have hz := (V.mem_orthogonal (v : E)).mp v.property (v : E) hvV
  exact hvne (Subtype.ext (inner_self_eq_zero.mp hz))

private lemma phase_distance (θ : ℝ) : ‖1 - Complex.exp (θ * Complex.I)‖ ≤ |θ| := by
  rw [norm_sub_rev, mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul,
    Real.norm_eq_abs, Real.norm_eq_abs]
  norm_num
  have h := Real.abs_sin_le_abs (x := θ / 2)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  linarith

private lemma restricted_displacement {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (U : E →ₗᵢ[ℂ] E) (S : Set ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hunit : ∀ μ ∈ S, ‖μ‖ = 1) (hclose : ∀ μ ∈ S, ‖1 - μ‖ ≤ c)
    (x : E) (hx : x ∈ ⨆ μ : S, Module.End.eigenspace U.toLinearMap μ) :
    ‖x - U x‖ ≤ c * ‖x‖ := by
  classical
  let V : S → Submodule ℂ E := fun μ => Module.End.eigenspace U.toLinearMap μ
  have orth : OrthogonalFamily ℂ (fun μ => V μ) (fun μ => (V μ).subtypeₗᵢ) := by
    intro μ ν hne v w
    have hv : U (v : E) = (μ : ℂ) • (v : E) := Module.End.mem_eigenspace_iff.mp v.property
    have hw : U (w : E) = (ν : ℂ) • (w : E) := Module.End.mem_eigenspace_iff.mp w.property
    have hi := U.inner_map_map (v : E) (w : E)
    rw [hv, hw, inner_smul_left, inner_smul_right] at hi
    have hm : (μ : ℂ) * conj (μ : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hunit μ μ.property]
      norm_num
    have he : (ν : ℂ) * inner ℂ (v : E) (w : E) =
        (μ : ℂ) * inner ℂ (v : E) (w : E) := by
      have := congrArg (fun z : ℂ => (μ : ℂ) * z) hi
      calc
        (ν : ℂ) * inner ℂ (v : E) (w : E) =
            ((μ : ℂ) * conj (μ : ℂ)) * ((ν : ℂ) * inner ℂ (v : E) (w : E)) := by rw [hm, one_mul]
        _ = (μ : ℂ) * inner ℂ (v : E) (w : E) := by linear_combination this
    by_contra hn
    exact hne (Subtype.ext ((mul_right_cancel₀ hn he).symm))
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp V x).mp hx
  let l : ∀ μ, V μ := fun μ => ⟨f μ, hf μ⟩
  let d : ∀ μ, V μ := fun μ => (1 - (μ : ℂ)) • l μ
  have hs : (∑ μ ∈ f.support, ((l μ : V μ) : E)) = x := hsum
  have hd : (∑ μ ∈ f.support, ((d μ : V μ) : E)) = x - U x := by
    rw [← hs, map_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro μ hμ
    have he : U (l μ : E) = (μ : ℂ) • (l μ : E) :=
      Module.End.mem_eigenspace_iff.mp (l μ).property
    simp [d, he, sub_smul]
  have hb : ‖x - U x‖ ^ 2 ≤ c ^ 2 * ‖x‖ ^ 2 := by
    have hl := orth.norm_sum l f.support
    have hd' := orth.norm_sum d f.support
    change ‖∑ μ ∈ f.support, ((l μ : V μ) : E)‖ ^ 2 = _ at hl
    change ‖∑ μ ∈ f.support, ((d μ : V μ) : E)‖ ^ 2 = _ at hd'
    rw [hs] at hl
    rw [hd] at hd'
    rw [hd', hl, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro μ hμ
    dsimp [d]
    rw [norm_smul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (by nlinarith [hclose μ μ.property, norm_nonneg (1 - (μ : ℂ))]) (sq_nonneg _)
  nlinarith [norm_nonneg (x - U x), mul_nonneg hc (norm_nonneg x)]

private lemma gap_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (K L : Submodule ℂ E) (c : ℝ) (hc : 0 ≤ c)
    (w : E) (hw : L.starProjection w = 0) :
    ‖eigenProjection (reflProduct K L) {μ : ℂ | ‖μ‖ = 1 ∧ |μ.arg| ≤ c}
      (K.starProjection w)‖ ≤ c / 2 * ‖w‖ := by
  classical
  let U : E →ₗᵢ[ℂ] E := (L.reflection.trans K.reflection).toLinearIsometry
  let S : Set ℂ := {μ | ‖μ‖ = 1 ∧ |μ.arg| ≤ c}
  let W : Submodule ℂ E := ⨆ μ ∈ S, Module.End.eigenspace U.toLinearMap μ
  let p := K.starProjection w
  let y := W.starProjection p
  change ‖y‖ ≤ c / 2 * ‖w‖
  have hy : y ∈ W := W.starProjection_apply_mem p
  have hbound : ‖y - U y‖ ≤ c * ‖y‖ := by
    apply restricted_displacement U S c hc
    · intro μ hμ; exact hμ.1
    · intro μ hμ
      have he : μ = Complex.exp (μ.arg * Complex.I) := by
        calc
          μ = (‖μ‖ : ℂ) * Complex.exp (μ.arg * Complex.I) := (Complex.norm_mul_exp_arg_mul_I μ).symm
          _ = _ := by rw [hμ.1]; simp
      exact (congrArg (fun z : ℂ => ‖1 - z‖) he).le.trans ((phase_distance μ.arg).trans hμ.2)
    · simpa only [iSup_subtype] using hy
  have huphi : U w = w - 2 • p := by
    change K.reflection (L.reflection w) = w - 2 • K.starProjection w
    have hL : L.reflection w = -w := by
      rw [Submodule.reflection_apply, hw, smul_zero, zero_sub]
    rw [hL, map_neg, Submodule.reflection_apply]
    abel
  have hip : inner ℂ y p = inner ℂ y y := by
    calc
      inner ℂ y p = inner ℂ (W.starProjection y) p := by
        rw [W.starProjection_eq_self_iff.mpr hy]
      _ = inner ℂ y (W.starProjection p) := W.inner_starProjection_left_eq_right y p
      _ = inner ℂ y y := rfl
  have hid : inner ℂ (y - U y) (U w) = -(2 : ℂ) * inner ℂ y y := by
    rw [inner_sub_left, U.inner_map_map, huphi, inner_sub_right,
      two_smul, inner_add_right, hip]
    ring
  have heq : ‖inner ℂ (y - U y) (U w)‖ = 2 * ‖y‖ ^ 2 := by
    rw [hid, norm_mul, norm_neg, inner_self_eq_norm_sq_to_K]
    simp
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (y - U y) (U w)
  rw [heq, U.norm_map] at hcs
  have hh := mul_le_mul_of_nonneg_right hbound (norm_nonneg w)
  by_cases hz : ‖y‖ = 0
  · rw [hz]; positivity
  have hypos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hz)
  have hh2 : (2 * ‖y‖) * ‖y‖ ≤ (c * ‖w‖) * ‖y‖ := by nlinarith only [hcs.trans hh]
  have hh3 := (mul_le_mul_iff_left₀ hypos).mp hh2
  linarith

private lemma high_component {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U : E →ₗᵢ[ℂ] E) (c : ℝ) (x : E) :
    x - (⨆ μ ∈ {μ : ℂ | ‖μ‖ = 1 ∧ |μ.arg| ≤ c},
      Module.End.eigenspace U.toLinearMap μ).starProjection x ∈
      ⨆ μ ∈ {μ : ℂ | c < |μ.arg|}, Module.End.eigenspace U.toLinearMap μ := by
  classical
  let Lo : Submodule ℂ E := ⨆ μ ∈ {μ : ℂ | ‖μ‖ = 1 ∧ |μ.arg| ≤ c},
    Module.End.eigenspace U.toLinearMap μ
  let Hi : Submodule ℂ E := ⨆ μ ∈ {μ : ℂ | c < |μ.arg|}, Module.End.eigenspace U.toLinearMap μ
  have hsum : Lo ⊔ Hi = ⊤ := by
    apply top_unique
    rw [← eigen_span U]
    apply iSup_le
    intro μ v hv
    by_cases hz : v = 0
    · simpa [hz] using (Lo ⊔ Hi).zero_mem
    have hm := eigen_norm U hz (Module.End.mem_eigenspace_iff.mp hv)
    by_cases hμ : |μ.arg| ≤ c
    · have hmem : v ∈ Lo := Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem ⟨hm,hμ⟩ hv)
      exact (show Lo ≤ Lo ⊔ Hi from le_sup_left) hmem
    · have hmem : v ∈ Hi := Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem (lt_of_not_ge hμ) hv)
      exact (show Hi ≤ Lo ⊔ Hi from le_sup_right) hmem
  have horth : Hi ≤ Loᗮ := by
    apply iSup_le
    intro μ
    apply iSup_le
    intro hμ v hv
    rw [Submodule.mem_orthogonal]
    intro w hw
    have hw' : w ∈ ⨆ ν : {ν : ℂ | ‖ν‖ = 1 ∧ |ν.arg| ≤ c},
        Module.End.eigenspace U.toLinearMap ν := by simpa only [iSup_subtype] using hw
    obtain ⟨f, hf, hs⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ w).mp hw'
    rw [← hs]
    change inner ℂ (∑ ν ∈ f.support, f ν) v = 0
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro ν hν
    exact eigen_orth U (by intro h; have := ν.property.2; rw [h] at this; exact (not_lt_of_ge this) hμ)
      (Module.End.mem_eigenspace_iff.mp (hf ν)) (Module.End.mem_eigenspace_iff.mp hv)
  have hx : x ∈ Lo ⊔ Hi := by rw [hsum]; trivial
  obtain ⟨l, hl, h, hh, rfl⟩ := Submodule.mem_sup.mp hx
  have hproj : Lo.starProjection h = 0 := by
    exact Submodule.eq_starProjection_of_mem_orthogonal Lo.zero_mem (by simpa using horth hh)
  change l + h - Lo.starProjection (l + h) ∈ Hi
  rw [map_add, hproj, Lo.starProjection_eq_self_iff.mpr hl]
  simpa using hh

private theorem tensor_inner {A B : Type*} [Fintype A] [Fintype B]
    (u x : EuclideanSpace ℂ A) (v y : EuclideanSpace ℂ B) :
    inner ℂ (tensorVec u v) (tensorVec x y) = inner ℂ u x * inner ℂ v y := by
  simp only [PiLp.inner_apply, tensorVec, RCLike.inner_apply,
    map_mul, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

private lemma ket_inner {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    inner ℂ (ket i) (ket j) = if i = j then 1 else 0 := by
  simp [ket, EuclideanSpace.inner_single_left]

private lemma third_inner {N : ℕ} (P : AdvAlg N)
    (v w : EuclideanSpace ℂ (Fin P.d)) :
    inner ℂ (P.thirdReg v) (P.thirdReg w) = inner ℂ v w := by
  simp [AdvAlg.thirdReg, PiLp.inner_apply, Fin.sum_univ_succ]

private lemma ket_sub_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) : ‖ket a - ket b‖ ^ 2 ≤ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), ket_inner]
  by_cases h : a = b
  · norm_num [h, ket]
  · norm_num [h, ket]

private lemma tminus_norm {N : ℕ} (P : AdvAlg N) (x : Fin N → Bool) :
    ‖P.tMinus x‖ ≤ 1 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [AdvAlg.tMinus, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hp]
  apply (inv_mul_le_iff₀ hp).mpr
  nlinarith [ket_sub_bound ((0 : Fin (N+1)),(false,(0 : Fin (P.d+1))))
    ((1 : Fin (N+1)),(P.f x,(0 : Fin (P.d+1)))), norm_nonneg
    (ket ((0 : Fin (N+1)),(false,(0 : Fin (P.d+1)))) -
      ket ((1 : Fin (N+1)),(P.f x,(0 : Fin (P.d+1)))))]

private lemma witness_bounds {N : ℕ} (P : AdvAlg N) (x : P.D) (hA : 0 < P.A) :
    (P.piSpace x).starProjection (P.psi x) =
      ((0.01 / Real.sqrt P.A : ℝ) : ℂ) • P.tMinus x ∧
    (P.lambdaSpace).starProjection (P.psi x) = 0 ∧
    ‖P.psi x‖ ≤ 0.01 / Real.sqrt P.A + Real.sqrt P.A := by
  classical
  let qj := fun j : Fin N => tensorVec (ket j.succ)
    (tensorVec (ket (!(x : Fin N → Bool) j)) (P.thirdReg (P.v x j)))
  let q := ∑ j, qj j
  have hqinner (i j : Fin N) : inner ℂ (qj i) (qj j) =
      if i = j then inner ℂ (P.v x i) (P.v x j) else 0 := by
    dsimp [qj]
    rw [tensor_inner, tensor_inner, ket_inner, ket_inner, third_inner]
    by_cases h : i = j
    · subst j; simp
    · simp [h, Fin.succ_inj]
  have hqnorm : ‖q‖ ^ 2 = ∑ j, ‖P.v x j‖ ^ 2 := by
    have h : inner ℂ q q = ∑ j, inner ℂ (P.v x j) (P.v x j) := by
      simp only [q, sum_inner, inner_sum, hqinner, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [inner_self_eq_norm_sq_to_K] at h
    exact_mod_cast h
  have hobj : ∑ j, ‖P.v x j‖ ^ 2 ≤ P.A := by
    have h := (le_max_right (∑ j, ‖P.u x j‖₊ ^ 2) (∑ j, ‖P.v x j‖₊ ^ 2)).trans
      (Finset.le_sup (f := fun y : P.D => max (∑ j, ‖P.u y j‖₊ ^ 2)
        (∑ j, ‖P.v y j‖₊ ^ 2)) (Finset.mem_univ x))
    change ∑ j, ‖P.v x j‖ ^ 2 ≤ (((Finset.univ.sup fun y : P.D =>
      max (∑ j, ‖P.u y j‖₊ ^ 2) (∑ j, ‖P.v y j‖₊ ^ 2)) : ℝ≥0) : ℝ)
    simpa only [NNReal.coe_sum, NNReal.coe_pow, coe_nnnorm] using (NNReal.coe_le_coe.mpr h)
  have hqn : ‖q‖ ≤ Real.sqrt P.A := by
    nlinarith [Real.sq_sqrt hA.le, Real.sqrt_nonneg P.A]
  have hqorth : q ∈ (P.piSpace x)ᗮ := by
    apply Submodule.sum_mem
    intro i hi
    apply (Submodule.mem_orthogonal _ _).mpr
    intro u hu
    change u ∈ Submodule.span ℂ (ket '' _) at hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      change inner ℂ (ket z) (qj i) = 0
      rw [ket, EuclideanSpace.inner_single_left]
      simp only [map_one, one_mul]
      dsimp [qj, tensorVec, AdvAlg.thirdReg]
      rcases hz with ⟨j, hj, hb⟩ | hk
      · by_cases hij : i = j
        · subst i
          simp [ket, hj, hb]
        · have hh : z.1 ≠ i.succ := by rw [hj]; exact fun h => hij (Fin.succ_inj.mp h).symm
          simp [ket, hh]
      · simp [hk, ket]
    | zero => simp
    | add a b ha hb iha ihb => simp [inner_add_left, iha, ihb]
    | smul a b hb ihb => simp [inner_smul_left, ihb]
  have ht : P.tMinus x ∈ P.piSpace x := by
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · apply Submodule.subset_span
      exact ⟨_, Or.inr rfl, rfl⟩
    · apply Submodule.subset_span
      exact ⟨_, Or.inr rfl, rfl⟩
  have hqzero : (P.piSpace x).starProjection q = 0 :=
    Submodule.eq_starProjection_of_mem_orthogonal (Submodule.zero_mem _) (by simpa using hqorth)
  have hl : P.psi x ∈ (P.lambdaSpace)ᗮ := by
    apply Submodule.le_orthogonal_orthogonal
    exact Submodule.subset_span ⟨x,rfl⟩
  refine ⟨?_, Submodule.eq_starProjection_of_mem_orthogonal (Submodule.zero_mem _) (by simpa using hl), ?_⟩
  · change (P.piSpace x).starProjection
      (((0.01 / Real.sqrt P.A : ℝ) : ℂ) • P.tMinus x - q) = _
    rw [map_sub, map_smul, hqzero, sub_zero, Submodule.starProjection_eq_self_iff.mpr ht]
  · calc
      ‖P.psi x‖ ≤ ‖((0.01 / Real.sqrt P.A : ℝ) : ℂ) • P.tMinus x‖ + ‖q‖ := norm_sub_le _ _
      _ ≤ 0.01 / Real.sqrt P.A + Real.sqrt P.A := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : 0 ≤ (0.01 : ℝ) / Real.sqrt P.A)]
        nlinarith [tminus_norm P x, div_nonneg (by norm_num : (0 : ℝ) ≤ 0.01) (Real.sqrt_nonneg P.A)]

theorem solution {N : ℕ} (P : AdvAlg N)
    (hfeas : DualFeasibleDeWolf P.f P.D P.d P.u P.v) (hA : 0 < P.A) (x : P.D) :
    ∃ φ ∈ (⨆ μ ∈ {μ : ℂ | 1 / (1000 * P.A) < |Complex.arg μ|},
        Module.End.eigenspace
          ((P.walk x : AdvSpace N P.d →L[ℂ] AdvSpace N P.d) : AdvSpace N P.d →ₗ[ℂ] AdvSpace N P.d)
          μ),
      ‖P.tMinus x - φ‖ ≤ 1 / 20 + 1 / (2000 * P.A) := by
  classical
  let c := 1 / (1000 * P.A)
  let a := (0.01 : ℝ) / Real.sqrt P.A
  let U : AdvSpace N P.d →ₗᵢ[ℂ] AdvSpace N P.d :=
    ((P.lambdaSpace).reflection.trans (P.piSpace x).reflection).toLinearIsometry
  let W : Submodule ℂ (AdvSpace N P.d) :=
    ⨆ μ ∈ {μ : ℂ | ‖μ‖ = 1 ∧ |μ.arg| ≤ c}, Module.End.eigenspace U.toLinearMap μ
  let y := W.starProjection (P.tMinus x)
  refine ⟨P.tMinus x - y, high_component U c (P.tMinus x), ?_⟩
  have ha : 0 < a := div_pos (by norm_num) (Real.sqrt_pos.mpr hA)
  have hb := witness_bounds P x hA
  have hc := gap_bound (P.piSpace x) P.lambdaSpace c (by dsimp [c]; positivity)
    (P.psi x) hb.2.1
  rw [hb.1, map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ha] at hc
  change a * ‖y‖ ≤ c / 2 * ‖P.psi x‖ at hc
  have heq : c / 2 * (a + Real.sqrt P.A) = a * (1 / 20 + 1 / (2000 * P.A)) := by
    dsimp [c,a]
    field_simp
    nlinarith [Real.sq_sqrt hA.le]
  have hh := hc.trans (mul_le_mul_of_nonneg_left hb.2.2 (by dsimp [c]; positivity : 0 ≤ c / 2))
  change a * ‖y‖ ≤ c / 2 * (a + Real.sqrt P.A) at hh
  rw [heq] at hh
  have hyn : ‖y‖ ≤ 1 / 20 + 1 / (2000 * P.A) := (mul_le_mul_iff_right₀ ha).mp hh
  simpa only [sub_sub_cancel] using hyn
