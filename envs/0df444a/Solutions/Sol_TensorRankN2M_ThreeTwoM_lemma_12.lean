-- Prove2me | solution 1 for TensorRankN2M.ThreeTwoM.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:39:29.600174+00:00
-- url     : https://prove2.me/submissions/d07f666c-3347-45e3-9a14-e50c7fda63e0

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition
import Definitions.Def_TensorRankN2M_ThreeTwoM_Normalization
import Definitions.Def_TensorRankN2M_ThreeTwoM_SkewAugmentation
import Definitions.Def_TensorRankN2M_ThreeTwoM_N2M
import Definitions.Def_TensorRankN2M_ThreeTwoM_CaseN3

section
set_option autoImplicit false

namespace TensorRankN2M.Dev.Common

open TensorRankN2M.ThreeTwoM

variable {𝔽 : Type*} [Field 𝔽] {k l m R : ℕ}

theorem W_D_Bvec (d : Decomposition 𝔽 k l m R) (A : Matrix (Fin k) (Fin l) 𝔽)
    (B : Matrix (Fin l) (Fin m) 𝔽) : d.W ((d.D A).mulVec (d.Bvec B)) = A * B := by
  rw [d.eq A B]
  simp [Decomposition.W, Decomposition.D, Decomposition.Bvec, Fintype.linearCombination_apply,
    Matrix.mulVec_diagonal]

theorem Bvec_injective [NeZero k] (d : Decomposition 𝔽 k l m R) :
    Function.Injective d.Bvec := by
  rw [injective_iff_map_eq_zero]
  intro B hB
  have h0 : ∀ A : Matrix (Fin k) (Fin l) 𝔽, A * B = 0 := by
    intro A
    rw [← W_D_Bvec d A B, hB]
    simp
  ext i j
  have h1 := congrFun (congrFun (h0 (Matrix.single (0 : Fin k) i (1 : 𝔽))) 0) j
  simpa [Matrix.mul_apply, Matrix.single_apply] using h1

end TensorRankN2M.Dev.Common
end

section
set_option autoImplicit false

namespace TensorRankN2M.Dev.Lemma12

open TensorRankN2M.ThreeTwoM

def a1 : Idx 3 := ⟨1, by decide⟩
def a2 : Idx 3 := ⟨2, by decide⟩

theorem a12 : a1 ≠ a2 := by decide

theorem forall_idx (P : Idx 3 → Prop) : (∀ i, P i) ↔ P a1 ∧ P a2 := by
  constructor
  · intro h; exact ⟨h _, h _⟩
  · rintro ⟨h1, h2⟩ ⟨i, hi⟩
    fin_cases i
    · exact absurd rfl hi
    · exact h1
    · exact h2

theorem sum_idx {M : Type*} [AddCommMonoid M] (g : Idx 3 → M) : ∑ i, g i = g a1 + g a2 := by
  have : (Finset.univ : Finset (Idx 3)) = {a1, a2} := by
    ext ⟨i, hi⟩
    fin_cases i
    · exact absurd rfl hi
    · simp [a1]
    · simp [a2]
  rw [this, Finset.sum_pair a12]

theorem card_idx : Fintype.card (Idx 3) = 2 := by decide

section

variable {𝔽 : Type*} [Field 𝔽] {m R : ℕ} (d : Decomposition 𝔽 3 2 m R)

theorem f_apply (i : Fin 3) (u : Matrix (Fin 2) (Fin m) 𝔽) (r : Fin R) :
    d.f i u r = d.α r (Matrix.single i 0 1) * d.β r u := by
  simp [Decomposition.f, Decomposition.D, Decomposition.Bvec, Matrix.mulVec_diagonal]

theorem ell_apply (u : Idx 3 → U 𝔽 m) : d.ell u = d.f 1 (u a1) + d.f 2 (u a2) := by
  simp [Decomposition.ell, sum_idx, a1, a2]

theorem h_skew (x : U 𝔽 m) :
    d.h (skewOfU 𝔽 m x) a1 = -(d.f 2 x) ∧ d.h (skewOfU 𝔽 m x) a2 = d.f 1 x := by
  have e : ∀ i, d.h (skewOfU 𝔽 m x) i = d.ell (fun j => (skewCoef i j : 𝔽) • x) := by
    intro i
    simp [Decomposition.h, skewAug, skewOfU]
    congr 1
  constructor
  · rw [e, ell_apply]
    simp [skewCoef, a1, a2]
  · rw [e, ell_apply]
    simp [skewCoef, a1, a2]

theorem mem_J (y : Fin R → 𝔽) : y ∈ d.J ↔ ∃ u : U 𝔽 m, d.f 0 u = y := by
  simp [Decomposition.J, Submodule.mem_map]

theorem mem_N (x : U 𝔽 m) :
    x ∈ d.Nspace ↔ -(d.f 2 x) ∈ d.J ∧ d.f 1 x ∈ d.J := by
  have : x ∈ d.Nspace ↔ ∀ i, d.h (skewOfU 𝔽 m x) i ∈ d.J := by
    simp only [Decomposition.Nspace, LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · intro h i
      have := congrFun h i
      simpa [Decomposition.H] using this
    · intro h
      ext1 i
      simpa [Decomposition.H] using h i
  rw [this, forall_idx, (h_skew d x).1, (h_skew d x).2]


theorem skew_apply (y : U 𝔽 m) (i j : Idx 3) :
    (skewOfU 𝔽 m y).1 i j = (skewCoef i j : 𝔽) • y := by
  rfl

theorem sc11 : (skewCoef a1 a1 : 𝔽) = 0 := by simp [skewCoef]
theorem sc22 : (skewCoef a2 a2 : 𝔽) = 0 := by simp [skewCoef]
theorem sc12 : (skewCoef a1 a2 : 𝔽) = -1 := by
  have : a1.1 < a2.1 := by decide
  simp [skewCoef, this]
theorem sc21 : (skewCoef a2 a1 : 𝔽) = 1 := by
  have : a1.1 < a2.1 := by decide
  simp [skewCoef, this, not_lt_of_gt this]

theorem skew_surj : Function.Surjective (skewOfU 𝔽 m) := by
  intro cc
  have hc0 := cc.2.1
  have hc := cc.2.2
  refine ⟨-(cc.1 a1 a2), ?_⟩
  apply Subtype.ext
  funext i j
  rw [skew_apply]
  have h21 : cc.1 a2 a1 = -cc.1 a1 a2 := hc a1 a2
  revert i j
  rw [forall_idx]
  refine ⟨?_, ?_⟩ <;> rw [forall_idx] <;> refine ⟨?_, ?_⟩
  · rw [sc11, hc0]; simp
  · rw [sc12]; simp
  · rw [sc21, h21]; simp
  · rw [sc22, hc0]; simp

theorem a0_ne (hd : d.StronglyNormalized) (r : Fin R) : d.α r (Matrix.single 0 0 1) ≠ 0 := by
  have h := hd.2
  unfold Decomposition.D at h
  rw [Matrix.isUnit_diagonal] at h
  exact (Pi.isUnit_iff.1 h r).ne_zero

theorem f0_inj (hd : d.StronglyNormalized) : Function.Injective (d.f 0) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have h : ∀ r, d.β r v = 0 := by
    intro r
    have := congrFun hv r
    rw [f_apply] at this
    exact (mul_eq_zero.1 this).resolve_left (a0_ne d hd r)
  apply TensorRankN2M.Dev.Common.Bvec_injective d
  ext r
  simp [Decomposition.Bvec, h r]

theorem key_eq (hd : d.StronglyNormalized) (x s1 s2 : Matrix (Fin 2) (Fin m) 𝔽)
    (h1 : d.f 0 s1 = -(d.f 2 x)) (h2 : d.f 0 s2 = d.f 1 x) :
    d.f 1 s1 + d.f 2 s2 = 0 := by
  ext r
  have e1 := congrFun h1 r
  have e2 := congrFun h2 r
  simp only [f_apply, Pi.neg_apply] at e1 e2
  simp only [f_apply, Pi.add_apply, Pi.zero_apply]
  have : d.α r (Matrix.single 0 0 1) *
      (d.α r (Matrix.single 1 0 1) * d.β r s1 + d.α r (Matrix.single 2 0 1) * d.β r s2) = 0 := by
    linear_combination d.α r (Matrix.single 1 0 1) * e1 + d.α r (Matrix.single 2 0 1) * e2
  exact (mul_eq_zero.1 this).resolve_left (a0_ne d hd r)

theorem finrank_ineq {A V : Type*} [AddCommGroup A] [Module 𝔽 A] [FiniteDimensional 𝔽 A]
    [AddCommGroup V] [Module 𝔽 V] [FiniteDimensional 𝔽 V] (φ : A →ₗ[𝔽] V) (W : Submodule 𝔽 V) :
    Module.finrank 𝔽 A + Module.finrank 𝔽 W ≤
      Module.finrank 𝔽 (W.comap φ) + Module.finrank 𝔽 V := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (W.mkQ ∘ₗ φ)
  have h2 : LinearMap.ker (W.mkQ ∘ₗ φ) = W.comap φ := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have h3 := Submodule.finrank_quotient_add_finrank W
  have h4 : Module.finrank 𝔽 (LinearMap.range (W.mkQ ∘ₗ φ)) ≤ Module.finrank 𝔽 (V ⧸ W) :=
    Submodule.finrank_le _
  rw [h2] at h1
  omega

theorem memK (u : Idx 3 → U 𝔽 m) : u ∈ LinearMap.ker d.L ↔ d.ell u ∈ d.J := by
  simp [Decomposition.L, Submodule.Quotient.mk_eq_zero]

theorem main (hd : d.StronglyNormalized) :
    (Module.finrank 𝔽 d.Nspace : ℤ) - d.Delta ≤ Module.finrank 𝔽 d.Sspace := by
  classical
  have f0inj : Function.Injective (d.f 0 ∘ₗ (U 𝔽 m).subtype) :=
    (f0_inj d hd).comp Subtype.val_injective
  obtain ⟨lam, hlam⟩ := LinearMap.exists_leftInverse_of_injective
    (d.f 0 ∘ₗ (U 𝔽 m).subtype) (LinearMap.ker_eq_bot.2 f0inj)
  have hlam' : ∀ u : U 𝔽 m, lam (d.f 0 u) = u := fun u => LinearMap.congr_fun hlam u
  let σ1 : U 𝔽 m →ₗ[𝔽] U 𝔽 m := lam ∘ₗ (-(d.f 2 ∘ₗ (U 𝔽 m).subtype))
  let σ2 : U 𝔽 m →ₗ[𝔽] U 𝔽 m := lam ∘ₗ d.f 1 ∘ₗ (U 𝔽 m).subtype
  have hσ1 : ∀ x : U 𝔽 m, σ1 x = lam (-(d.f 2 x)) := fun x => rfl
  have hσ2 : ∀ x : U 𝔽 m, σ2 x = lam (d.f 1 x) := fun x => rfl
  have spec1 : ∀ x ∈ d.Nspace, d.f 0 (σ1 x) = -(d.f 2 x) := by
    intro x hx
    obtain ⟨u, hu⟩ := (mem_J d _).1 ((mem_N d x).1 hx).1
    rw [hσ1, ← hu, hlam' u, hu]
  have spec2 : ∀ x ∈ d.Nspace, d.f 0 (σ2 x) = d.f 1 x := by
    intro x hx
    obtain ⟨u, hu⟩ := (mem_J d _).1 ((mem_N d x).1 hx).2
    rw [hσ2, ← hu, hlam' u]
  let Ψ : U 𝔽 m →ₗ[𝔽] (Idx 3 → U 𝔽 m) := LinearMap.pi fun i => if i = a1 then σ1 else σ2
  have hΨ1 : ∀ x, Ψ x a1 = σ1 x := by intro x; simp [Ψ]
  have hΨ2 : ∀ x, Ψ x a2 = σ2 x := by intro x; simp [Ψ, a12.symm]
  have hΨK : ∀ x ∈ d.Nspace, Ψ x ∈ LinearMap.ker d.L := by
    intro x hx
    rw [memK, ell_apply, hΨ1, hΨ2]
    rw [key_eq d hd x (σ1 x) (σ2 x) (spec1 x hx) (spec2 x hx)]
    exact zero_mem _
  let φ : d.Nspace →ₗ[𝔽] LinearMap.ker d.L :=
    LinearMap.codRestrict _ (Ψ ∘ₗ d.Nspace.subtype) (fun x => hΨK x.1 x.2)
  let E : (Idx 3 → d.Nspace) →ₗ[𝔽] (Idx 3 → U 𝔽 m) :=
    LinearMap.pi fun i => d.Nspace.subtype ∘ₗ LinearMap.proj i
  have hEinj : Function.Injective E := by
    intro v w h
    funext i
    exact Subtype.ext (congrFun h i)
  have hEr : ∀ u, u ∈ LinearMap.range E ↔ ∀ i, u i ∈ d.Nspace := by
    intro u
    constructor
    · rintro ⟨v, rfl⟩ i
      exact (v i).2
    · intro h
      exact ⟨fun i => ⟨u i, h i⟩, rfl⟩
  have hEK : LinearMap.range E ≤ LinearMap.ker d.L := by
    intro u hu
    rw [hEr, forall_idx] at hu
    rw [memK, ell_apply]
    have h1 := ((mem_N d _).1 hu.1).2
    have h2 := neg_mem_iff.1 ((mem_N d _).1 hu.2).1
    exact add_mem h1 h2
  let W : Submodule 𝔽 (LinearMap.ker d.L) := (LinearMap.range E).comap (LinearMap.ker d.L).subtype
  have hW : Module.finrank 𝔽 W = 2 * Module.finrank 𝔽 d.Nspace := by
    have e1 : W.map (LinearMap.ker d.L).subtype = LinearMap.range E := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 hEK
    have e2 := Submodule.finrank_map_subtype_eq (LinearMap.ker d.L) W
    rw [e1, LinearMap.finrank_range_of_inj hEinj] at e2
    rw [← e2]
    haveI : Module.Free 𝔽 d.Nspace := by
      convert Module.Free.of_divisionRing 𝔽 d.Nspace
    rw [Module.finrank_pi_fintype]
    simp [card_idx]
  have hineq := finrank_ineq (A := d.Nspace) (V := LinearMap.ker d.L) φ W
  have hS : d.Sspace = (W.comap φ).map d.Nspace.subtype := by
    ext x
    rw [Submodule.mem_map]
    constructor
    · intro hx
      obtain ⟨⟨hxN, h1⟩, h2⟩ := hx
      obtain ⟨y1, hy1, hy1e⟩ := h1
      obtain ⟨y2, hy2, hy2e⟩ := h2
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      show Ψ x ∈ LinearMap.range E
      rw [hEr, forall_idx, hΨ1, hΨ2]
      refine ⟨?_, ?_⟩
      · have : -(σ1 x) = y2 := by
          apply f0inj
          have hy2e' : d.f 0 y2.1 = d.f 2 x.1 := hy2e
          show d.f 0 (-((σ1 x).1)) = d.f 0 y2.1
          rw [map_neg, spec1 x hxN, hy2e', neg_neg]
        rw [← neg_mem_iff, this]
        exact hy2
      · have : σ2 x = y1 := by
          apply f0inj
          have hy1e' : d.f 0 y1.1 = d.f 1 x.1 := hy1e
          show d.f 0 (σ2 x).1 = d.f 0 y1.1
          rw [spec2 x hxN, hy1e']
        rw [this]
        exact hy1
    · rintro ⟨y, hy, rfl⟩
      have hy' : Ψ y.1 ∈ LinearMap.range E := hy
      rw [hEr, forall_idx, hΨ1, hΨ2] at hy'
      refine ⟨⟨y.2, ?_⟩, ?_⟩
      · refine ⟨σ2 y.1, hy'.2, ?_⟩
        simpa using spec2 y.1 y.2
      · refine ⟨-(σ1 y.1), (neg_mem_iff).2 hy'.1, ?_⟩
        simp [spec1 y.1 y.2]
  have hSr : Module.finrank 𝔽 d.Sspace = Module.finrank 𝔽 (W.comap φ) := by
    rw [hS]
    exact Submodule.finrank_map_subtype_eq d.Nspace _
  -- ranks
  have hrkH : Module.finrank 𝔽 (LinearMap.range d.H) + Module.finrank 𝔽 d.Nspace
      = Module.finrank 𝔽 (U 𝔽 m) := by
    have := LinearMap.finrank_range_add_finrank_ker (d.H ∘ₗ skewOfU 𝔽 m)
    rwa [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 skew_surj)] at this
  have hrkL := LinearMap.finrank_range_add_finrank_ker d.L
  have hpi : Module.finrank 𝔽 (Idx 3 → U 𝔽 m) = 2 * Module.finrank 𝔽 (U 𝔽 m) := by
    simp [Module.finrank_pi_fintype, card_idx]
  unfold Decomposition.Delta
  omega

end

end TensorRankN2M.Dev.Lemma12

namespace TensorRankN2M.ThreeTwoM

/-- Lemma 12 (p. 6). -/
theorem chk_lemma_12 {𝔽 : Type*} [Field 𝔽] [IsAlgClosed 𝔽] {m R : ℕ} (hm : 3 ≤ m)
    (d : Decomposition 𝔽 3 2 m R) (hd : d.StronglyNormalized) :
    (Module.finrank 𝔽 d.Nspace : ℤ) - d.Delta ≤ Module.finrank 𝔽 d.Sspace :=
  TensorRankN2M.Dev.Lemma12.main d hd

end TensorRankN2M.ThreeTwoM
end

theorem solution : type_of% @TensorRankN2M.ThreeTwoM.chk_lemma_12 := @TensorRankN2M.ThreeTwoM.chk_lemma_12
