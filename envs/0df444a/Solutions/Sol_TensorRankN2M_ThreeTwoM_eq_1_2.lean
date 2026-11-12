-- Prove2me | solution 1 for TensorRankN2M.ThreeTwoM.eq_1_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:39:30.550192+00:00
-- url     : https://prove2.me/submissions/37c30093-0402-4f8a-9dea-7424542a2145

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition
import Definitions.Def_TensorRankN2M_ThreeTwoM_Normalization
import Definitions.Def_TensorRankN2M_ThreeTwoM_SkewAugmentation
import Definitions.Def_TensorRankN2M_ThreeTwoM_N2M
import Theorems.Thm_TensorRankN2M_ThreeTwoM_lemma_10

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

theorem W_surjective [NeZero l] (d : Decomposition 𝔽 k l m R) : Function.Surjective d.W := by
  have key : ∀ (i : Fin k) (j : Fin m), d.W ((d.D (Matrix.single i (0 : Fin l) (1 : 𝔽))).mulVec
      (d.Bvec (Matrix.single (0 : Fin l) j (1 : 𝔽)))) = Matrix.single i j 1 := by
    intro i j
    rw [W_D_Bvec]
    simp [Matrix.single_mul_single_same]
  intro M
  refine ⟨∑ i, ∑ j, M i j • (d.D (Matrix.single i (0 : Fin l) (1 : 𝔽))).mulVec
      (d.Bvec (Matrix.single (0 : Fin l) j (1 : 𝔽))), ?_⟩
  simp only [map_sum, map_smul, key]
  ext a b
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and]

end TensorRankN2M.Dev.Common
end

section
set_option autoImplicit false

namespace TensorRankN2M.Dev.Eq12

open TensorRankN2M.ThreeTwoM

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

variable {𝔽 : Type*} [Field 𝔽] {n m R : ℕ} [NeZero n]

theorem W_f (d : Decomposition 𝔽 n 2 m R) (i : Fin n) (x : Matrix (Fin 2) (Fin m) 𝔽)
    (hx : x ∈ U 𝔽 m) : d.W (d.f i x) = 0 := by
  have h := Common.W_D_Bvec d (Matrix.single i (0 : Fin 2) (1 : 𝔽)) x
  have : d.f i x = (d.D (Matrix.single i (0 : Fin 2) (1 : 𝔽))).mulVec (d.Bvec x) := rfl
  rw [this, h]
  ext a b
  simp [Matrix.mul_apply, Matrix.single_apply, hx b]

theorem ell_mem (d : Decomposition 𝔽 n 2 m R) (u : Idx n → U 𝔽 m) :
    d.ell u ∈ LinearMap.ker d.W := by
  rw [LinearMap.mem_ker]
  simp only [Decomposition.ell, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.subtype_apply, map_sum]
  exact Finset.sum_eq_zero fun i _ => W_f d i.1 _ (u i).2

theorem g_mem (d : Decomposition 𝔽 n 2 m R) (x : Matrix (Fin 2) (Fin m) 𝔽) :
    d.g x ∈ LinearMap.ker d.W := by
  rw [LinearMap.mem_ker]
  simp only [Decomposition.g, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
    Matrix.mulVecLin_apply]
  rw [Common.W_D_Bvec, Common.W_D_Bvec]
  ext a b
  simp [Decomposition.sandwich, Matrix.mul_apply, Matrix.single_apply]

theorem J_le (d : Decomposition 𝔽 n 2 m R) : d.J ≤ LinearMap.ker d.W := by
  rintro _ ⟨x, hx, rfl⟩
  exact (LinearMap.mem_ker).2 (W_f d 0 x hx)

theorem f0_injective [NeZero n] (d : Decomposition 𝔽 n 2 m R) (hd : d.StronglyNormalized) :
    Function.Injective (d.f 0) := by
  have h1 := Matrix.mulVec_injective_iff_isUnit.2 hd.2
  exact h1.comp (Common.Bvec_injective d)

theorem finrank_U : Module.finrank 𝔽 (U 𝔽 m) = m := by
  let φ : Matrix (Fin 2) (Fin m) 𝔽 →ₗ[𝔽] (Fin m → 𝔽) := LinearMap.proj 0
  have hker : LinearMap.ker φ = U 𝔽 m := by
    ext x
    simp only [LinearMap.mem_ker, φ, LinearMap.proj_apply]
    show x 0 = 0 ↔ ∀ j, x 0 j = 0
    exact funext_iff
  have hsurj : Function.Surjective φ := by
    intro v
    refine ⟨Matrix.of fun i j => if i = 0 then v j else 0, ?_⟩
    show (Matrix.of fun i j => if i = 0 then v j else 0) 0 = v
    ext j
    simp
  have := LinearMap.finrank_range_add_finrank_ker φ
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, hker] at this
  simp [Module.finrank_matrix] at this
  omega

theorem finrank_J (d : Decomposition 𝔽 n 2 m R) (hd : d.StronglyNormalized) :
    Module.finrank 𝔽 d.J = m := by
  unfold Decomposition.J
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (d.f 0) (f0_injective d hd) (U 𝔽 m)).symm,
    finrank_U]

theorem finrank_kerW (d : Decomposition 𝔽 n 2 m R) :
    Module.finrank 𝔽 (LinearMap.ker d.W) + n * m = R := by
  have := LinearMap.finrank_range_add_finrank_ker d.W
  rw [LinearMap.range_eq_top.2 (Common.W_surjective d), finrank_top] at this
  simp [Module.finrank_matrix] at this
  omega

theorem finrank_KerWModJ (d : Decomposition 𝔽 n 2 m R) (hd : d.StronglyNormalized) :
    Module.finrank 𝔽 d.KerWModJ + m + n * m = R := by
  have h1 := Submodule.finrank_quotient_add_finrank (d.J.comap (LinearMap.ker d.W).subtype)
  have h2 : Module.finrank 𝔽 (d.J.comap (LinearMap.ker d.W).subtype) = m := by
    have hJ := finrank_J d hd
    have : (d.J.comap (LinearMap.ker d.W).subtype).map (LinearMap.ker d.W).subtype = d.J := by
      rw [Submodule.map_comap_eq, Submodule.range_subtype]
      exact inf_eq_right.2 (J_le d)
    have e := LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (Submodule.injective_subtype (LinearMap.ker d.W)) (d.J.comap (LinearMap.ker d.W).subtype))
    rw [this] at e
    omega
  have := finrank_kerW d
  unfold Decomposition.KerWModJ
  omega


/-- The `ker W`-valued `i`-th component of `Φ`. -/
noncomputable def compKer (d : Decomposition 𝔽 n 2 m R) (i : Idx n) :
    (Idx n → U 𝔽 m) × SkewArrays 𝔽 (U 𝔽 m) (Idx n) →ₗ[𝔽] LinearMap.ker d.W :=
  LinearMap.codRestrict (LinearMap.ker d.W)
    (-(d.g ∘ₗ (U 𝔽 m).subtype ∘ₗ LinearMap.proj i ∘ₗ LinearMap.fst 𝔽 _ _) +
      LinearMap.proj i ∘ₗ d.h ∘ₗ LinearMap.snd 𝔽 _ _) (by
    intro x
    have h1 := g_mem d ((x.1 i : U 𝔽 m) : Matrix (Fin 2) (Fin m) 𝔽)
    have h2 : d.h x.2 i ∈ LinearMap.ker d.W := by
      show d.ell _ ∈ _
      exact ell_mem d _
    simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, LinearMap.fst_apply, LinearMap.snd_apply, Submodule.subtype_apply]
    exact add_mem (neg_mem h1) h2)

noncomputable def Psi (d : Decomposition 𝔽 n 2 m R) :
    (Idx n → U 𝔽 m) × SkewArrays 𝔽 (U 𝔽 m) (Idx n) →ₗ[𝔽]
      LinearMap.range d.L × (Idx n → d.KerWModJ) :=
  LinearMap.prod
    (LinearMap.codRestrict (LinearMap.range d.L) (d.L ∘ₗ LinearMap.fst 𝔽 _ _)
      (fun x => ⟨_, rfl⟩))
    (LinearMap.pi fun i => (Submodule.mkQ _) ∘ₗ compKer d i)

noncomputable def Tmap (d : Decomposition 𝔽 n 2 m R) :
    LinearMap.range d.L × (Idx n → d.KerWModJ) →ₗ[𝔽]
      ((Fin R → 𝔽) ⧸ d.J) × (Idx n → (Fin R → 𝔽) ⧸ d.J) :=
  LinearMap.prodMap (LinearMap.range d.L).subtype
    (LinearMap.pi fun i => (Submodule.mapQ _ d.J (LinearMap.ker d.W).subtype le_rfl) ∘ₗ
      LinearMap.proj i)

theorem Phi_eq (d : Decomposition 𝔽 n 2 m R) : d.Φ = Tmap d ∘ₗ Psi d := by
  apply LinearMap.ext
  intro x
  refine Prod.ext rfl ?_
  funext i
  simp [Tmap, Psi, compKer, Decomposition.Φ]

theorem finrank_range_Phi_le (d : Decomposition 𝔽 n 2 m R) :
    Module.finrank 𝔽 (LinearMap.range d.Φ) ≤
      Module.finrank 𝔽 (LinearMap.range d.L) + (n - 1) * Module.finrank 𝔽 d.KerWModJ := by
  have h1 : Module.finrank 𝔽 (LinearMap.range d.Φ) ≤ Module.finrank 𝔽 (LinearMap.range (Psi d)) := by
    rw [Phi_eq d, LinearMap.range_comp]
    exact Submodule.finrank_map_le _ _
  haveI : Module.Free 𝔽 d.KerWModJ := Module.Free.of_divisionRing _ _
  haveI : Module.Finite 𝔽 d.KerWModJ := inferInstance
  have h2 := Submodule.finrank_le (LinearMap.range (Psi d))
  rw [Module.finrank_prod, Module.finrank_pi_fintype (R := 𝔽) (M := fun _ : Idx n => d.KerWModJ)] at h2
  have hc : Fintype.card (Idx n) = n - 1 := by
    simp [Idx, Fintype.card_subtype_compl]
  simp [hc] at h2
  omega

theorem finrank_ker_Phi (d : Decomposition 𝔽 n 2 m R) (hn : 3 ≤ n) (hm : 3 ≤ m) [IsAlgClosed 𝔽]
    (hd : d.StronglyNormalized) :
    Module.finrank 𝔽 (LinearMap.ker d.Φ) = Module.finrank 𝔽 (LinearMap.ker d.H) := by
  rw [ThreeTwoM.lemma_10 hn hm d hd]
  have : (⊥ : Submodule 𝔽 (Idx n → U 𝔽 m)).prod (LinearMap.ker d.H) =
      (LinearMap.ker d.H).map (LinearMap.inr 𝔽 (Idx n → U 𝔽 m)
        (SkewArrays 𝔽 (U 𝔽 m) (Idx n))) := by
    ext x
    simp [Submodule.mem_prod, eq_comm]
  rw [this]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
    (LinearMap.inr_injective) _)).symm

instance fd_U : FiniteDimensional 𝔽 (U 𝔽 m) := inferInstance
instance fd_pi : FiniteDimensional 𝔽 (Idx n → U 𝔽 m) := inferInstance
instance fd_skew : FiniteDimensional 𝔽 (SkewArrays 𝔽 (U 𝔽 m) (Idx n)) := inferInstance

theorem rn_gen {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [FiniteDimensional K V] (f : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.ker f) =
      Module.finrank K V :=
  LinearMap.finrank_range_add_finrank_ker f

theorem rn_dom {W : Type*} [AddCommGroup W] [Module 𝔽 W]
    (f : (Idx n → U 𝔽 m) × SkewArrays 𝔽 (U 𝔽 m) (Idx n) →ₗ[𝔽] W) :
    Module.finrank 𝔽 (LinearMap.range f) + Module.finrank 𝔽 (LinearMap.ker f) =
      Module.finrank 𝔽 ((Idx n → U 𝔽 m) × SkewArrays 𝔽 (U 𝔽 m) (Idx n)) :=
  by
  have := @rn_gen 𝔽 ((Idx n → U 𝔽 m) × SkewArrays 𝔽 (U 𝔽 m) (Idx n)) W _ _ _ _ _ _ f
  convert this using 2

theorem finrank_dom (d : Decomposition 𝔽 n 2 m R) :
    Module.finrank 𝔽 ((Idx n → U 𝔽 m) × SkewArrays 𝔽 (U 𝔽 m) (Idx n)) =
      (n - 1) * m + (Module.finrank 𝔽 (LinearMap.range d.H) + Module.finrank 𝔽 (LinearMap.ker d.H)) := by
  haveI : Module.Free 𝔽 (SkewArrays 𝔽 (U 𝔽 m) (Idx n)) := Module.Free.of_divisionRing 𝔽 (SkewArrays 𝔽 (U 𝔽 m) (Idx n))
  rw [Module.finrank_prod, Module.finrank_pi_fintype (R := 𝔽) (M := fun _ : Idx n => U 𝔽 m)]
  have hc : Fintype.card (Idx n) = n - 1 := by
    simp [Idx, Fintype.card_subtype_compl]
  simp [hc, finrank_U]
  have := @rn_gen 𝔽 (SkewArrays 𝔽 (U 𝔽 m) (Idx n)) (Idx n → (Fin R → 𝔽) ⧸ d.J) _ _ _ _ _ _ d.H
  omega

theorem ineq1 [IsAlgClosed 𝔽] (hn : 3 ≤ n) (hm : 3 ≤ m) (d : Decomposition 𝔽 n 2 m R)
    (hd : d.StronglyNormalized) :
    (n - 1) * m + Module.finrank 𝔽 (LinearMap.range d.H) ≤
      Module.finrank 𝔽 (LinearMap.range d.L) + (n - 1) * Module.finrank 𝔽 d.KerWModJ := by
  have h1 : Module.finrank 𝔽 (LinearMap.range d.Φ) + Module.finrank 𝔽 (LinearMap.ker d.Φ) =
      Module.finrank 𝔽 ((Idx n → U 𝔽 m) × SkewArrays 𝔽 (U 𝔽 m) (Idx n)) :=
    rn_dom d.Φ
  rw [finrank_ker_Phi d hn hm hd, finrank_dom d] at h1
  have h2 := finrank_range_Phi_le d
  omega

end TensorRankN2M.Dev.Eq12

namespace TensorRankN2M.ThreeTwoM

theorem chk_eq_1_2 {𝔽 : Type*} [Field 𝔽] [IsAlgClosed 𝔽] {n m R : ℕ} [NeZero n]
    (hn : 3 ≤ n) (hm : 3 ≤ m) (d : Decomposition 𝔽 n 2 m R)
    (hd : d.StronglyNormalized) :
    (n - 1) * Module.finrank 𝔽 (U 𝔽 m) + Module.finrank 𝔽 (LinearMap.range d.H) ≤
        Module.finrank 𝔽 (LinearMap.range d.L) + (n - 1) * Module.finrank 𝔽 d.KerWModJ ∧
      ((n : ℚ) + 2) * m +
          ((Module.finrank 𝔽 (LinearMap.range d.H) : ℚ) -
            Module.finrank 𝔽 (LinearMap.range d.L)) / ((n : ℚ) - 1) ≤ R := by
  have h1 := Dev.Eq12.ineq1 hn hm d hd
  have hK := Dev.Eq12.finrank_KerWModJ d hd
  rw [Dev.Eq12.finrank_U]
  refine ⟨h1, ?_⟩
  obtain ⟨p, hp⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have hpq : (3 : ℚ) ≤ n := by exact_mod_cast hn
  have hnm : (0 : ℚ) < (n : ℚ) - 1 := by linarith
  rw [← sub_nonneg]
  have hq : (((n - 1 : ℕ) : ℚ)) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have h1' : (((n - 1) * m + Module.finrank 𝔽 (LinearMap.range d.H) : ℕ) : ℚ) ≤
      ((Module.finrank 𝔽 (LinearMap.range d.L) + (n - 1) * Module.finrank 𝔽 d.KerWModJ : ℕ) : ℚ) := by
    exact_mod_cast h1
  have hK' : (Module.finrank 𝔽 d.KerWModJ : ℚ) + m + n * m = R := by exact_mod_cast hK
  push_cast at h1'
  rw [hq] at h1'
  rw [show (R : ℚ) - (((n : ℚ) + 2) * m + ((Module.finrank 𝔽 (LinearMap.range d.H) : ℚ) -
      Module.finrank 𝔽 (LinearMap.range d.L)) / ((n : ℚ) - 1)) =
      ((n - 1) * Module.finrank 𝔽 d.KerWModJ + Module.finrank 𝔽 (LinearMap.range d.L) -
        ((n - 1) * m + Module.finrank 𝔽 (LinearMap.range d.H))) / ((n : ℚ) - 1) from by
    field_simp
    nlinarith [hK']]
  apply div_nonneg _ hnm.le
  linarith

end TensorRankN2M.ThreeTwoM
end

theorem solution : type_of% @TensorRankN2M.ThreeTwoM.chk_eq_1_2 := @TensorRankN2M.ThreeTwoM.chk_eq_1_2
