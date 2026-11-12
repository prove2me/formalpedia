-- Prove2me | solution 1 for TensorRankN2M.ThreeTwoM.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:48:48.305756+00:00
-- url     : https://prove2.me/submissions/8c7eab48-1b42-4c22-afc4-970aa3d7ffe0

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition
import Definitions.Def_TensorRankN2M_ThreeTwoM_Normalization
import Definitions.Def_TensorRankN2M_ThreeTwoM_SkewAugmentation
import Definitions.Def_TensorRankN2M_ThreeTwoM_N2M
import Definitions.Def_TensorRankN2M_ThreeTwoM_CaseN3
import Theorems.Thm_TensorRankN2M_ThreeTwoM_eq_1_2
import Theorems.Thm_TensorRankN2M_ThreeTwoM_lemma_11
import Theorems.Thm_TensorRankN2M_ThreeTwoM_lemma_12
import Theorems.Thm_TensorRankN2M_ThreeTwoM_lemma_8
import Theorems.Thm_TensorRankN2M_ThreeTwoM_lemma_6

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


instance fd_U : FiniteDimensional 𝔽 (U 𝔽 m) := inferInstance
instance fd_pi : FiniteDimensional 𝔽 (Idx n → U 𝔽 m) := inferInstance
instance fd_skew : FiniteDimensional 𝔽 (SkewArrays 𝔽 (U 𝔽 m) (Idx n)) := inferInstance

end TensorRankN2M.Dev.Eq12

namespace TensorRankN2M.ThreeTwoM

end TensorRankN2M.ThreeTwoM
end

section
set_option autoImplicit false

namespace TensorRankN2M.Dev.Thm1Core

open TensorRankN2M.ThreeTwoM

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

section
variable {K : Type*} [Field K] {m R : ℕ} (d : Decomposition K 3 2 m R)

noncomputable def ellKer : (Idx 3 → U K m) →ₗ[K] LinearMap.ker d.W :=
  LinearMap.codRestrict _ d.ell (Dev.Eq12.ell_mem d)

theorem L_eq : d.L = (Submodule.mapQ (d.J.comap (LinearMap.ker d.W).subtype) d.J
    (LinearMap.ker d.W).subtype le_rfl) ∘ₗ
    ((d.J.comap (LinearMap.ker d.W).subtype).mkQ ∘ₗ ellKer d) := by
  apply LinearMap.ext
  intro u
  rfl

theorem rkL_le : Module.finrank K (LinearMap.range d.L) ≤ Module.finrank K d.KerWModJ := by
  haveI : Module.Finite K d.KerWModJ := inferInstance
  rw [L_eq, LinearMap.range_comp]
  refine (Submodule.finrank_map_le _ _).trans ?_
  exact Submodule.finrank_le _

noncomputable def eqv : Fin 2 ≃ Idx 3 :=
  Fintype.equivOfCardEq (by simp [Idx, Fintype.card_subtype_compl])

noncomputable def Ein : SkewArrays K (U K m) (Fin 2) →ₗ[K] SkewArrays K (U K m) (Idx 3) :=
  LinearMap.codRestrict _
    (LinearMap.pi fun i => LinearMap.pi fun j =>
      (LinearMap.proj (eqv.symm j) ∘ₗ LinearMap.proj (eqv.symm i) ∘ₗ
        (SkewArrays K (U K m) (Fin 2)).subtype))
    (fun c => ⟨fun i => by simpa using c.2.1 (eqv.symm i), fun i j => by
      simpa using c.2.2 (eqv.symm i) (eqv.symm j)⟩)

noncomputable def Eout : (Idx 3 → (Fin R → K) ⧸ d.J) →ₗ[K] (Fin 2 → (Fin R → K) ⧸ d.J) :=
  LinearMap.funLeft K _ eqv

noncomputable def Rin : (Fin 2 → U K m) →ₗ[K] (Idx 3 → U K m) :=
  LinearMap.funLeft K _ eqv.symm

theorem Rin_surj : Function.Surjective (Rin (K := K) (m := m)) := by
  intro v
  refine ⟨fun i => v (eqv i), ?_⟩
  ext i : 1
  simp [Rin]

theorem skewAug_eq : skewAug (d.L ∘ₗ Rin) = Eout d ∘ₗ d.H ∘ₗ Ein := by
  apply LinearMap.ext
  intro c
  funext k
  show d.L (Rin (c.1 k)) = d.L _
  congr 1
  funext j
  show c.1 k (eqv.symm j) = c.1 (eqv.symm (eqv k)) (eqv.symm j)
  rw [Equiv.symm_apply_apply]

theorem rkL_le_rkH : Module.finrank K (LinearMap.range d.L) ≤
    2 * Module.finrank K (LinearMap.range d.H) := by
  have h := lemma_11 (𝔽 := K) 2 (by norm_num) (d.L ∘ₗ Rin)
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 Rin_surj)] at h
  have hr : LinearMap.range (skewAug (d.L ∘ₗ Rin)) ≤ Submodule.map (Eout d) (LinearMap.range d.H) := by
    rw [skewAug_eq]
    rintro _ ⟨c, rfl⟩
    exact ⟨_, ⟨Ein c, rfl⟩, rfl⟩
  have h2 := (Submodule.rank_mono hr).trans (rank_map_le _ _)
  have h3 := h.trans (by gcongr : (2 : Cardinal) * Module.rank K (LinearMap.range (skewAug (d.L ∘ₗ Rin))) ≤ 2 * Module.rank K (LinearMap.range d.H))
  norm_num at h3
  have e1 := Module.finrank_eq_rank K (LinearMap.range d.L)
  have e2 := Module.finrank_eq_rank K (LinearMap.range d.H)
  rw [← e1, ← e2] at h3
  exact_mod_cast h3

theorem rkH_ge : m ≤ Module.finrank K (LinearMap.range d.H) + Module.finrank K d.Nspace := by
  have h := LinearMap.finrank_range_add_finrank_ker (d.H ∘ₗ skewOfU K m)
  rw [Dev.Eq12.finrank_U] at h
  have h2 : Module.finrank K (LinearMap.range (d.H ∘ₗ skewOfU K m)) ≤
      Module.finrank K (LinearMap.range d.H) :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  have h3 : Module.finrank K (LinearMap.ker (d.H ∘ₗ skewOfU K m)) = Module.finrank K d.Nspace := rfl
  omega

theorem S_ne_bot [IsAlgClosed K] (hd : d.StronglyNormalized) (hS : d.Sspace ≠ ⊥) :
    Module.finrank K d.Sspace + 2 ≤ Module.finrank K d.Nspace := by
  set S' : Submodule K (Matrix (Fin 2) (Fin m) K) := d.Sspace.map (U K m).subtype with hS'
  have hne : S' ≠ ⊥ := by
    intro h
    apply hS
    rw [Submodule.eq_bot_iff]
    intro x hx
    have : (x : Matrix (Fin 2) (Fin m) K) ∈ S' := ⟨x, hx, rfl⟩
    rw [h] at this
    exact Subtype.ext (by simpa using this)
  have h8 := lemma_8 d hd S' hne
  have hS'f : Module.finrank K S' = Module.finrank K d.Sspace :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _)
      d.Sspace)).symm
  have hinj : Function.Injective (d.f 0 ∘ₗ (U K m).subtype) :=
    (Dev.Eq12.f0_injective d hd).comp (Submodule.injective_subtype _)
  have hle : (⨆ i : Fin 3, S'.map (d.f i)) ≤ d.Nspace.map (d.f 0 ∘ₗ (U K m).subtype) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : y ∈ d.Nspace := (Submodule.mem_inf.1 (Submodule.mem_inf.1 hy).1).1
    have h2 := (Submodule.mem_inf.1 (Submodule.mem_inf.1 hy).1).2
    have h3 := (Submodule.mem_inf.1 hy).2
    fin_cases i
    · exact ⟨y, h1, rfl⟩
    · exact h2
    · exact h3
  have h9 := Submodule.finrank_mono hle
  have h10 : Module.finrank K (d.Nspace.map (d.f 0 ∘ₗ (U K m).subtype)) =
      Module.finrank K d.Nspace :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj d.Nspace)).symm
  simp only [Nat.reduceSub] at h8
  omega

theorem N_le_one [IsAlgClosed K] (hm : 3 ≤ m) (hd : d.StronglyNormalized)
    (hΔ : d.Delta < 2) : Module.finrank K d.Nspace ≤ 1 := by
  have h12 := lemma_12 hm d hd
  by_cases hS : d.Sspace = ⊥
  · rw [hS, finrank_bot] at h12
    omega
  · have := S_ne_bot d hd hS
    omega

end

theorem arith (m R rH rL K N : ℕ) (hm : 3 ≤ m) (hK : K + m + 3 * m = R)
    (h1 : 2 * m + rH ≤ rL + 2 * K) (h2 : rL ≤ K) (h3 : rL ≤ 2 * rH)
    (h4 : m ≤ rH + N) (h5 : (2 * rH : ℤ) < rL + 2 → N ≤ 1) : 24 * m + 2 ≤ 5 * R := by
  by_cases hc : (2 * rH : ℤ) < rL + 2
  · have := h5 hc
    omega
  · omega

theorem _root_.TensorRankN2M.Dev.Thm1.core_proof {K : Type*} [Field K] [IsAlgClosed K] {m R : ℕ}
    (hm : 3 ≤ m) (d : Decomposition K 3 2 m R) (hd : d.StronglyNormalized) :
    ⌈(24 * (m : ℚ) + 2) / 5⌉₊ ≤ R := by
  have e12 := (eq_1_2 (n := 3) (by norm_num) hm d hd).1
  rw [Dev.Eq12.finrank_U] at e12
  have hK := Dev.Eq12.finrank_KerWModJ d hd
  have hΔ : (2 * Module.finrank K (LinearMap.range d.H) : ℤ) <
      Module.finrank K (LinearMap.range d.L) + 2 → Module.finrank K d.Nspace ≤ 1 := by
    intro h
    exact N_le_one d hm hd (by unfold Decomposition.Delta; omega)
  have key := arith m R _ _ _ _ hm (by omega) (by omega) (rkL_le d) (rkL_le_rkH d) (rkH_ge d) hΔ
  rw [Nat.ceil_le, div_le_iff₀ (by norm_num)]
  exact_mod_cast (by omega : 24 * m + 2 ≤ R * 5)

end TensorRankN2M.Dev.Thm1Core
end

section
set_option autoImplicit false

namespace TensorRankN2M.Dev.Thm1

open TensorRankN2M.ThreeTwoM

/-- Interface: the core numerical bound for a strongly normalized decomposition over an
algebraically closed field. -/
theorem core {K : Type*} [Field K] [IsAlgClosed K] {m R : ℕ} (hm : 3 ≤ m)
    (d : Decomposition K 3 2 m R) (hd : d.StronglyNormalized) :
    ⌈(24 * (m : ℚ) + 2) / 5⌉₊ ≤ R := Thm1.core_proof hm d hd

end TensorRankN2M.Dev.Thm1
end

section
set_option autoImplicit false

namespace TensorRankN2M.Dev.Thm1Red

open TensorRankN2M.ThreeTwoM

/-- The coordinate functional `A ↦ A i j`. -/
def entry (𝔽 : Type*) [Field 𝔽] {a b : ℕ} (i : Fin a) (j : Fin b) :
    Matrix (Fin a) (Fin b) 𝔽 →ₗ[𝔽] 𝔽 where
  toFun A := A i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem entry_apply (𝔽 : Type*) [Field 𝔽] {a b : ℕ} (i : Fin a) (j : Fin b)
    (A : Matrix (Fin a) (Fin b) 𝔽) : entry 𝔽 i j A = A i j := rfl

/-- The standard decomposition. -/
noncomputable def std (𝔽 : Type*) [Field 𝔽] (k l m : ℕ) :
    Decomposition 𝔽 k l m (Fintype.card (Fin k × Fin l × Fin m)) where
  α r := entry 𝔽 ((Fintype.equivFin (Fin k × Fin l × Fin m)).symm r).1
    ((Fintype.equivFin (Fin k × Fin l × Fin m)).symm r).2.1
  β r := entry 𝔽 ((Fintype.equivFin (Fin k × Fin l × Fin m)).symm r).2.1
    ((Fintype.equivFin (Fin k × Fin l × Fin m)).symm r).2.2
  C r := Matrix.single ((Fintype.equivFin (Fin k × Fin l × Fin m)).symm r).1
    ((Fintype.equivFin (Fin k × Fin l × Fin m)).symm r).2.2 (1 : 𝔽)
  eq A B := by
    rw [Equiv.sum_comp (Fintype.equivFin (Fin k × Fin l × Fin m)).symm
      (fun x : Fin k × Fin l × Fin m => (entry 𝔽 x.1 x.2.1 A * entry 𝔽 x.2.1 x.2.2 B) •
        Matrix.single x.1 x.2.2 (1 : 𝔽))]
    ext p q
    simp only [Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply,
      entry_apply, Matrix.mul_apply, smul_eq_mul]
    simp [ite_and, mul_ite]

theorem std_nonempty (𝔽 : Type*) [Field 𝔽] (k l m : ℕ) :
    ∃ R, Nonempty (Decomposition 𝔽 k l m R) := ⟨_, ⟨std 𝔽 k l m⟩⟩

/-- Extension of a linear form to `K` by the entries. -/
noncomputable def extForm {𝔽 : Type*} [Field 𝔽] (K : Type*) [Field K] [Algebra 𝔽 K] {a b : ℕ}
    (f : Matrix (Fin a) (Fin b) 𝔽 →ₗ[𝔽] 𝔽) : Matrix (Fin a) (Fin b) K →ₗ[K] K :=
  ∑ i, ∑ j, algebraMap 𝔽 K (f (Matrix.single i j 1)) • entry K i j

theorem extForm_single {𝔽 : Type*} [Field 𝔽] (K : Type*) [Field K] [Algebra 𝔽 K] {a b : ℕ}
    (f : Matrix (Fin a) (Fin b) 𝔽 →ₗ[𝔽] 𝔽) (i : Fin a) (j : Fin b) :
    extForm K f (Matrix.single i j 1) = algebraMap 𝔽 K (f (Matrix.single i j 1)) := by
  simp [extForm, LinearMap.sum_apply, Matrix.single_apply, ite_and, Algebra.algebraMap_eq_smul_one]

/-- Base change of a decomposition. -/
noncomputable def baseChange {𝔽 : Type*} [Field 𝔽] (K : Type*) [Field K] [Algebra 𝔽 K]
    {k l m R : ℕ} (d : Decomposition 𝔽 k l m R) : Decomposition K k l m R where
  α r := extForm K (d.α r)
  β r := extForm K (d.β r)
  C r := (d.C r).map (algebraMap 𝔽 K)
  eq A B := by
    let L : Matrix (Fin k) (Fin l) K →ₗ[K] Matrix (Fin l) (Fin m) K →ₗ[K] Matrix (Fin k) (Fin m) K :=
      LinearMap.mk₂ K (fun A B => A * B) (fun _ _ _ => Matrix.add_mul _ _ _)
        (fun c A B => Matrix.smul_mul c A B) (fun _ _ _ => Matrix.mul_add _ _ _)
        (fun c A B => Matrix.mul_smul A c B)
    let L2 : Matrix (Fin k) (Fin l) K →ₗ[K] Matrix (Fin l) (Fin m) K →ₗ[K]
        Matrix (Fin k) (Fin m) K :=
      LinearMap.mk₂ K (fun A B => ∑ r, (extForm K (d.α r) A * extForm K (d.β r) B) •
          (d.C r).map (algebraMap 𝔽 K))
        (fun A A' B => by simp [add_mul, add_smul, Finset.sum_add_distrib])
        (fun c A B => by simp [mul_assoc, Finset.smul_sum, smul_smul])
        (fun A B B' => by simp [mul_add, add_smul, Finset.sum_add_distrib])
        (fun c A B => by
          simp only [map_smul, smul_eq_mul, Finset.smul_sum, smul_smul]
          exact Finset.sum_congr rfl fun r _ => by rw [mul_left_comm])
    have : L = L2 := by
      refine LinearMap.ext_basis (Matrix.stdBasis K (Fin k) (Fin l))
        (Matrix.stdBasis K (Fin l) (Fin m)) ?_
      rintro ⟨i, j⟩ ⟨j', q⟩
      simp only [Matrix.stdBasis_eq_single, L, L2, LinearMap.mk₂_apply, extForm_single]
      have h := congrArg (fun M => M.map (algebraMap 𝔽 K))
        (d.eq (Matrix.single i j 1) (Matrix.single j' q 1))
      simp only [Matrix.map_mul, Matrix.map_single, map_one] at h
      rw [h]
      ext x y
      simp [Matrix.sum_apply]
    exact congrArg (fun F => F A B) this

theorem prune {𝔽 : Type*} [Field 𝔽] {k l m R : ℕ} (d : Decomposition 𝔽 k l m R) :
    ∃ R' ≤ R, ∃ d' : Decomposition 𝔽 k l m R', ∀ r, d'.α r ≠ 0 := by
  classical
  let p : Fin R → Prop := fun r => d.α r ≠ 0
  let e := (Fintype.equivFin {r // p r}).symm
  refine ⟨Fintype.card {r // p r}, ?_, ?_, ?_⟩
  · simpa using Fintype.card_subtype_le p
  · refine
      { α := fun r => d.α (e r)
        β := fun r => d.β (e r)
        C := fun r => d.C (e r)
        eq := fun A B => ?_ }
    rw [d.eq A B, Equiv.sum_comp e (fun x : {r // p r} => (d.α x A * d.β x B) • d.C x)]
    rw [← Finset.sum_subtype (Finset.univ.filter p) (p := p) (by simp)
      (fun r => (d.α r A * d.β r B) • d.C r)]
    rw [Finset.sum_filter_of_ne]
    intro r _ hr h
    exact hr (by simp [h])
  · intro r
    exact (e r).2

end TensorRankN2M.Dev.Thm1Red

namespace TensorRankN2M.Dev.Thm1Red

open TensorRankN2M.ThreeTwoM

theorem bound_of_decomp {𝔽 : Type*} [Field 𝔽] {m R : ℕ} (hm : 3 ≤ m)
    (d : Decomposition 𝔽 3 2 m R) : ⌈(24 * (m : ℚ) + 2) / 5⌉₊ ≤ R := by
  obtain ⟨R', hR', d', hd'⟩ := prune (baseChange (AlgebraicClosure 𝔽) d)
  obtain ⟨S, T, hS⟩ := TensorRankN2M.ThreeTwoM.lemma_6 d' hd'
  exact (TensorRankN2M.Dev.Thm1.core hm _ hS).trans hR'

end TensorRankN2M.Dev.Thm1Red

namespace TensorRankN2M.ThreeTwoM

theorem chk_theorem_1 {𝔽 : Type*} [Field 𝔽] (m : ℕ) (hm : 3 ≤ m) :
    ⌈(24 * (m : ℚ) + 2) / 5⌉₊ ≤ tensorRank 𝔽 3 2 m := by
  obtain ⟨R, hR⟩ := TensorRankN2M.Dev.Thm1Red.std_nonempty 𝔽 3 2 m
  have hne : {R : ℕ | Nonempty (Decomposition 𝔽 3 2 m R)}.Nonempty := ⟨R, hR⟩
  obtain ⟨d⟩ := Nat.sInf_mem hne
  exact TensorRankN2M.Dev.Thm1Red.bound_of_decomp hm d

end TensorRankN2M.ThreeTwoM
end

theorem solution : type_of% @TensorRankN2M.ThreeTwoM.chk_theorem_1 := @TensorRankN2M.ThreeTwoM.chk_theorem_1
