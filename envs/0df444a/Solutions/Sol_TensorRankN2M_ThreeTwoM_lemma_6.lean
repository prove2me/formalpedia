-- Prove2me | solution 1 for TensorRankN2M.ThreeTwoM.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:39:29.808249+00:00
-- url     : https://prove2.me/submissions/13e08865-0014-40aa-a06c-b1e6ff2edac7

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition
import Definitions.Def_TensorRankN2M_ThreeTwoM_Normalization

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

end TensorRankN2M.Dev.Common
end

section
set_option autoImplicit false

namespace TensorRankN2M.Dev.Lemma6

open TensorRankN2M.ThreeTwoM Matrix

section Generic

variable {𝔽 : Type*} [Field 𝔽] {σ : Type*}

/-- Generic: the set where some nonzero polynomial does not vanish contains the set. -/
def Good (P : (σ → 𝔽) → Prop) : Prop :=
  ∃ Q : MvPolynomial σ 𝔽, Q ≠ 0 ∧ ∀ p, MvPolynomial.eval p Q ≠ 0 → P p

theorem good_of_ne {Q : MvPolynomial σ 𝔽} (hQ : Q ≠ 0) :
    Good (fun p : σ → 𝔽 => MvPolynomial.eval p Q ≠ 0) := ⟨Q, hQ, fun _ h => h⟩

theorem good_mono {P P' : (σ → 𝔽) → Prop} (h : ∀ p, P p → P' p) (hP : Good P) : Good P' := by
  obtain ⟨Q, hQ, hQP⟩ := hP
  exact ⟨Q, hQ, fun p hp => h p (hQP p hp)⟩

theorem good_and {P P' : (σ → 𝔽) → Prop} (h : Good P) (h' : Good P') :
    Good (fun p => P p ∧ P' p) := by
  obtain ⟨Q, hQ, hQP⟩ := h
  obtain ⟨Q', hQ', hQP'⟩ := h'
  refine ⟨Q * Q', mul_ne_zero hQ hQ', fun p hp => ?_⟩
  rw [map_mul] at hp
  exact ⟨hQP p (left_ne_zero_of_mul hp), hQP' p (right_ne_zero_of_mul hp)⟩

theorem good_forall {ι : Type*} [Fintype ι] {P : ι → (σ → 𝔽) → Prop} (h : ∀ i, Good (P i)) :
    Good (fun p => ∀ i, P i p) := by
  choose Q hQ hQP using h
  refine ⟨∏ i, Q i, Finset.prod_ne_zero_iff.2 fun i _ => hQ i, fun p hp i => hQP i p ?_⟩
  rw [map_prod] at hp
  exact (Finset.prod_ne_zero_iff.1 hp) i (Finset.mem_univ _)

theorem good_exists [Infinite 𝔽] {P : (σ → 𝔽) → Prop} (h : Good P) : ∃ p, P p := by
  obtain ⟨Q, hQ, hQP⟩ := h
  by_contra hne
  push Not at hne
  apply hQ
  apply MvPolynomial.funext
  intro x
  by_contra hx
  exact hne x (hQP x (by simpa using hx))

theorem good_inj {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (M : Matrix ι (Fin k) (MvPolynomial σ 𝔽)) (p0 : σ → 𝔽)
    (h0 : ∀ a : Fin k → 𝔽, (M.map (MvPolynomial.eval p0)) *ᵥ a = 0 → a = 0) :
    Good (fun p => ∀ a : Fin k → 𝔽, (M.map (MvPolynomial.eval p)) *ᵥ a = 0 → a = 0) := by
  classical
  have hinj : Function.Injective (Matrix.mulVecLin (M.map (MvPolynomial.eval p0))) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact h0 a ha
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 hinj)
  set K : Matrix (Fin k) ι 𝔽 := LinearMap.toMatrix' g with hK
  let N : Matrix (Fin k) (Fin k) (MvPolynomial σ 𝔽) :=
    Matrix.of fun i j => ∑ r, MvPolynomial.C (K i r) * M r j
  have hev : ∀ p, MvPolynomial.eval p N.det
      = (K * M.map (MvPolynomial.eval p)).det := by
    intro p
    refine (RingHom.map_det _ _).trans ?_
    congr 1
    ext i j
    simp [N, Matrix.mul_apply]
  have hdet0 : (K * M.map (MvPolynomial.eval p0)).det ≠ 0 := by
    intro hd
    rw [← Matrix.exists_mulVec_eq_zero_iff] at hd
    obtain ⟨a, ha, hKa⟩ := hd
    apply ha
    rw [← Matrix.mulVec_mulVec, hK, LinearMap.toMatrix'_mulVec] at hKa
    have := LinearMap.congr_fun hg a
    simpa [hKa] using this.symm
  refine ⟨N.det, ?_, fun p hp a ha => ?_⟩
  · intro h
    apply hdet0
    rw [← hev p0, h, map_zero]
  · rw [hev] at hp
    by_contra hne
    apply hp
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨a, hne, by rw [← Matrix.mulVec_mulVec, ha, Matrix.mulVec_zero]⟩

end Generic

section Main

variable {𝔽 : Type*} [Field 𝔽] {k l m R : ℕ}

theorem phi_vecMulVec (φ : Matrix (Fin k) (Fin l) 𝔽 →ₗ[𝔽] 𝔽) (a : Fin k → 𝔽) (p : Fin l → 𝔽) :
    φ (Matrix.vecMulVec a p) = ∑ i, ∑ j, a i * p j * φ (Matrix.single i j 1) := by
  have : Matrix.vecMulVec a p = ∑ i, ∑ j, (a i * p j) • Matrix.single i j (1 : 𝔽) := by
    ext x y
    simp [Matrix.sum_apply, Matrix.single_apply, Matrix.vecMulVec_apply, ite_and]
  rw [this]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem phi_lin (φ : Matrix (Fin k) (Fin l) 𝔽 →ₗ[𝔽] 𝔽) (a : Fin k → 𝔽) (p : Fin l → 𝔽) :
    φ (Matrix.vecMulVec a p) = ∑ i, a i * φ (Matrix.vecMulVec (Pi.single i 1) p) := by
  rw [phi_vecMulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [phi_vecMulVec]
  simp [Pi.single_apply, Finset.mul_sum, mul_assoc]

theorem vecMulVec_single_single (i : Fin k) (j : Fin l) :
    Matrix.vecMulVec (Pi.single i (1 : 𝔽)) (Pi.single j 1) = Matrix.single i j 1 := by
  ext x y
  by_cases hx : x = i <;> by_cases hy : y = j <;>
    simp_all [Matrix.vecMulVec_apply, Matrix.single_apply, Pi.single_apply, eq_comm]

/-- polynomial `p ↦ φ(e_i ⊗ p)` -/
noncomputable def Ppoly (φ : Matrix (Fin k) (Fin l) 𝔽 →ₗ[𝔽] 𝔽) (i : Fin k) :
    MvPolynomial (Fin l) 𝔽 :=
  ∑ j, MvPolynomial.X j * MvPolynomial.C (φ (Matrix.single i j 1))

theorem eval_Ppoly (φ : Matrix (Fin k) (Fin l) 𝔽 →ₗ[𝔽] 𝔽) (i : Fin k) (p : Fin l → 𝔽) :
    MvPolynomial.eval p (Ppoly φ i) = φ (Matrix.vecMulVec (Pi.single i 1) p) := by
  rw [phi_vecMulVec]
  simp [Ppoly, Pi.single_apply]

theorem exists_single_ne (φ : Matrix (Fin k) (Fin l) 𝔽 →ₗ[𝔽] 𝔽) (hφ : φ ≠ 0) :
    ∃ i j, φ (Matrix.single i j 1) ≠ 0 := by
  by_contra h
  push Not at h
  apply hφ
  apply LinearMap.ext
  intro A
  have hA : A = ∑ i, ∑ j, A i j • Matrix.single i j (1 : 𝔽) := by
    ext x y
    simp [Matrix.sum_apply, Matrix.single_apply, ite_and]
  show φ A = 0
  rw [hA, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, h]
  simp

def Inj (d : Decomposition 𝔽 k l m R) (S : Finset (Fin R)) (p : Fin l → 𝔽) : Prop :=
  ∀ a : Fin k → 𝔽, (∀ r ∈ S, d.α r (Matrix.vecMulVec a p) = 0) → a = 0

theorem good_Inj (d : Decomposition 𝔽 k l m R) (S : Finset (Fin R))
    (h : ∃ p0, Inj d S p0) : Good (fun p : Fin l → 𝔽 => Inj d S p) := by
  classical
  obtain ⟨p0, h0⟩ := h
  let M : Matrix S (Fin k) (MvPolynomial (Fin l) 𝔽) := Matrix.of fun r i => Ppoly (d.α r) i
  have hM : ∀ (p : Fin l → 𝔽) (a : Fin k → 𝔽),
      (M.map (MvPolynomial.eval p)) *ᵥ a = fun r : S => d.α r (Matrix.vecMulVec a p) := by
    intro p a
    ext r
    rw [phi_lin]
    simp [Matrix.mulVec, dotProduct, M, eval_Ppoly, mul_comm]
  have hG := good_inj M p0 (fun a ha => h0 a (fun r hr => by
    have := congrFun ha ⟨r, hr⟩
    rwa [hM] at this))
  refine good_mono (fun p hp a ha => hp a ?_) hG
  rw [hM]
  funext r
  exact ha r r.2

theorem good_p [NeZero l] (d : Decomposition 𝔽 k l m R) (hα : ∀ r, d.α r ≠ 0) :
    Good (fun p : Fin l → 𝔽 => p 0 ≠ 0 ∧ (∀ r, ∃ i, d.α r (Matrix.vecMulVec (Pi.single i 1) p) ≠ 0) ∧
      ∀ S : Finset (Fin R), (∃ p0, Inj d S p0) → Inj d S p) := by
  classical
  refine good_and ?_ (good_and ?_ ?_)
  · refine good_mono (fun p hp => by simpa using hp) (good_of_ne (MvPolynomial.X_ne_zero (0 : Fin l)))
  · refine good_forall fun r => ?_
    obtain ⟨i0, j0, hij⟩ := exists_single_ne (d.α r) (hα r)
    have hQ : Ppoly (d.α r) i0 ≠ 0 := by
      intro h0
      have := congrArg (MvPolynomial.eval (Pi.single j0 (1 : 𝔽))) h0
      rw [eval_Ppoly, vecMulVec_single_single] at this
      exact hij (by simpa using this)
    exact good_mono (fun p hp => ⟨i0, by rwa [eval_Ppoly] at hp⟩) (good_of_ne hQ)
  · refine good_forall fun S => ?_
    by_cases h : ∃ p0, Inj d S p0
    · exact good_mono (fun p hp _ => hp) (good_Inj d S h)
    · exact ⟨1, one_ne_zero, fun p _ h' => absurd h' h⟩

theorem good_u [NeZero k] (d : Decomposition 𝔽 k l m R) (p : Fin l → 𝔽)
    (hp : ∀ r, ∃ i, d.α r (Matrix.vecMulVec (Pi.single i 1) p) ≠ 0) :
    Good (fun u : Fin k → 𝔽 => u 0 ≠ 0 ∧ ∀ r, d.α r (Matrix.vecMulVec u p) ≠ 0) := by
  classical
  refine good_and ?_ ?_
  · exact good_mono (fun p hp => by simpa using hp) (good_of_ne (MvPolynomial.X_ne_zero (0 : Fin k)))
  · refine good_forall fun r => ?_
    obtain ⟨i0, hi0⟩ := hp r
    have hev : ∀ u : Fin k → 𝔽, MvPolynomial.eval u
        (∑ i, MvPolynomial.X i * MvPolynomial.C (d.α r (Matrix.vecMulVec (Pi.single i 1) p)))
        = d.α r (Matrix.vecMulVec u p) := by
      intro u
      rw [phi_lin]
      simp
    have hQ : (∑ i, MvPolynomial.X i *
        MvPolynomial.C (d.α r (Matrix.vecMulVec (Pi.single i 1) p)) : MvPolynomial (Fin k) 𝔽) ≠ 0 := by
      intro h0
      have := congrArg (MvPolynomial.eval (Pi.single i0 (1 : 𝔽))) h0
      rw [hev] at this
      apply hi0
      have h2 := phi_lin (d.α r) (Pi.single i0 1) p
      rw [this] at h2
      simpa [Pi.single_apply] using h2.symm
    exact good_mono (fun u hu => by rwa [hev] at hu) (good_of_ne hQ)


theorem key_b (d : Decomposition 𝔽 k l m R) (p : Fin l → 𝔽)
    (hp : ∀ S : Finset (Fin R), (∃ p0, Inj d S p0) → Inj d S p)
    (w : Matrix (Fin l) (Fin m) 𝔽) (hw : w ≠ 0) (a : Fin k → 𝔽)
    (h : ∀ r, d.α r (Matrix.vecMulVec a p) * d.β r w = 0) : a = 0 := by
  classical
  have hw' : ∃ i0 j0, w i0 j0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hw (by ext i j; exact hc i j)
  obtain ⟨i0, j0, hij⟩ := hw'
  have hS : Inj d (Finset.univ.filter fun r => d.β r w ≠ 0) p := by
    apply hp
    refine ⟨Pi.single i0 1, fun a' ha' => ?_⟩
    have hz : ∀ r, d.α r (Matrix.vecMulVec a' (Pi.single i0 1)) * d.β r w = 0 := by
      intro r
      by_cases hr : d.β r w = 0
      · rw [hr, mul_zero]
      · rw [ha' r (by simp [hr]), zero_mul]
    have h0 : (d.D (Matrix.vecMulVec a' (Pi.single i0 1))).mulVec (d.Bvec w) = 0 := by
      ext r
      simp [Decomposition.D, Decomposition.Bvec, Matrix.mulVec_diagonal, hz r]
    have h1 := Common.W_D_Bvec d (Matrix.vecMulVec a' (Pi.single i0 1)) w
    rw [h0, map_zero] at h1
    ext i
    have := congrFun (congrFun h1 i) j0
    simpa [Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.single_apply, hij] using this.symm
  apply hS
  intro r hr
  have hr' : d.β r w ≠ 0 := by simpa using hr
  exact (mul_eq_zero.1 (h r)).resolve_right hr'

theorem vecMulVec_mulVec (U : Matrix (Fin k) (Fin k) 𝔽) (g : Fin k → 𝔽) (p : Fin l → 𝔽) :
    Matrix.vecMulVec (U *ᵥ g) p = ∑ i, g i • Matrix.vecMulVec (fun a => U a i) p := by
  ext x y
  simp [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Main

section Basis

variable {𝔽 : Type*} [Field 𝔽] {n : ℕ} [NeZero n]

def colMat (u : Fin n → 𝔽) : Matrix (Fin n) (Fin n) 𝔽 :=
  Matrix.of fun i j => if j = 0 then u i else if i = j then 1 else 0

theorem colMat_mulVec (u a : Fin n → 𝔽) (i : Fin n) :
    (colMat u *ᵥ a) i = u i * a 0 + (if i = 0 then 0 else a i) := by
  by_cases hi : i = 0
  · subst hi
    simp only [Matrix.mulVec, dotProduct, colMat, Matrix.of_apply]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [hj, Ne.symm hj]
    · simp
  · simp only [Matrix.mulVec, dotProduct, colMat, Matrix.of_apply]
    rw [Finset.sum_eq_add 0 i (Ne.symm hi)]
    · simp [hi]
    · intro c _ hc
      simp [hc.1, Ne.symm hc.2]
    · simp
    · simp
  
theorem colMat_inj {u : Fin n → 𝔽} (hu : u 0 ≠ 0) (a : Fin n → 𝔽) (h : colMat u *ᵥ a = 0) :
    a = 0 := by
  have h0 : a 0 = 0 := by
    have := congrFun h 0
    rw [colMat_mulVec] at this
    simpa [hu] using this
  funext i
  have := congrFun h i
  rw [colMat_mulVec] at this
  by_cases hi : i = 0
  · subst hi; exact h0
  · simpa [hi, h0] using this

theorem colMat_det {u : Fin n → 𝔽} (hu : u 0 ≠ 0) : (colMat u).det ≠ 0 := by
  intro h
  rw [← Matrix.exists_mulVec_eq_zero_iff] at h
  obtain ⟨a, ha, h⟩ := h
  exact ha (colMat_inj hu a h)

end Basis

section Final

variable {𝔽 : Type*} [Field 𝔽] {k l m R : ℕ}

theorem main [NeZero k] [NeZero l] [Infinite 𝔽]
    (d : Decomposition 𝔽 k l m R) (hα : ∀ r, d.α r ≠ 0) :
    ∃ (S : GL (Fin k) 𝔽) (T : GL (Fin l) 𝔽), (d.changeBasis S T).StronglyNormalized := by
  classical
  obtain ⟨p, hp0, hp1, hp2⟩ := good_exists (good_p d hα)
  obtain ⟨u, hu0, hu1⟩ := good_exists (good_u d p hp1)
  have hU : (colMat u).det ≠ 0 := colMat_det hu0
  have hTm : (colMat p)ᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact colMat_det hp0
  let S : GL (Fin k) 𝔽 := (Matrix.GeneralLinearGroup.mkOfDetNeZero (colMat u) hU)⁻¹
  let T : GL (Fin l) 𝔽 := Matrix.GeneralLinearGroup.mkOfDetNeZero (colMat p)ᵀ hTm
  refine ⟨S, T, ?_⟩
  have hSi : (↑S⁻¹ : Matrix (Fin k) (Fin k) 𝔽) = colMat u := by
    simp [S]
  have hT : (↑T : Matrix (Fin l) (Fin l) 𝔽) = (colMat p)ᵀ := by
    simp [T]
  have hα' : ∀ r A, (d.changeBasis S T).α r A = d.α r (colMat u * A * (colMat p)ᵀ) := by
    intro r A
    show d.α r ((↑S⁻¹ : Matrix (Fin k) (Fin k) 𝔽) * A * (↑T : Matrix (Fin l) (Fin l) 𝔽)) = _
    rw [hSi, hT]
  have hβ : ∀ r v, (d.changeBasis S T).β r v = d.β r ((↑T⁻¹ : Matrix (Fin l) (Fin l) 𝔽) * v) := by
    intro r v
    show d.β r ((↑T⁻¹ : Matrix (Fin l) (Fin l) 𝔽) * v * (1 : Matrix (Fin m) (Fin m) 𝔽)) = _
    rw [Matrix.mul_one]
  have hcol : ∀ i : Fin k, colMat u * Matrix.single i (0 : Fin l) (1 : 𝔽) * (colMat p)ᵀ
      = Matrix.vecMulVec (fun a => colMat u a i) p := by
    intro i
    have h1 : Matrix.single i (0 : Fin l) (1 : 𝔽) * (colMat p)ᵀ
        = Matrix.of fun a j => if a = i then p j else 0 := by
      ext a j
      by_cases ha : a = i
      · subst ha
        rw [Matrix.single_mul_apply_same]
        simp [colMat]
      · rw [Matrix.single_mul_apply_of_ne (h := ha)]
        simp [ha]
    rw [Matrix.mul_assoc, h1]
    ext x y
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply, colMat]
  constructor
  · intro v hv
    have hw : (↑T⁻¹ : Matrix (Fin l) (Fin l) 𝔽) * v ≠ 0 := by
      intro h
      apply hv
      have : (↑T : Matrix (Fin l) (Fin l) 𝔽) * ((↑T⁻¹ : Matrix (Fin l) (Fin l) 𝔽) * v) = v := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
      rw [← this, h, Matrix.mul_zero]
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have key : ∀ r, d.α r (Matrix.vecMulVec (colMat u *ᵥ g) p) *
        d.β r ((↑T⁻¹ : Matrix (Fin l) (Fin l) 𝔽) * v) = 0 := by
      intro r
      have h1 := congrFun hg r
      simp only [Decomposition.f, Decomposition.D, Decomposition.Bvec, hα', hβ, hcol,
        Matrix.sum_apply] at h1
      simp [Matrix.mulVec_diagonal] at h1
      simp only [hβ] at h1
      rw [vecMulVec_mulVec, map_sum, Finset.sum_mul]
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul]
      simp [mul_assoc]
    have := key_b d p hp2 _ hw _ key
    exact congrFun (colMat_inj hu0 g this) i
  · have : (d.changeBasis S T).D (Matrix.single (0 : Fin k) (0 : Fin l) 1) =
        Matrix.diagonal fun r => d.α r (Matrix.vecMulVec u p) := by
      simp only [Decomposition.D, hα', hcol]
      have : (fun a => colMat u a 0) = u := by
        funext a; simp [colMat]
      rw [this]
    rw [this, Matrix.isUnit_diagonal, Pi.isUnit_iff]
    intro r
    exact isUnit_iff_ne_zero.2 (hu1 r)

end Final

end TensorRankN2M.Dev.Lemma6

namespace TensorRankN2M.ThreeTwoM

/-- Lemma 6 (Strong normalization, p. 4), under the standing assumptions of §2 (p. 2): `𝔽` is
algebraically closed and no `α_r` is constant `0`. For a decomposition of ⟨k,l,m⟩ there is a change
of basis `(α_r(S⁻¹AT), β_r(T⁻¹B), S C_r)` after which `{f_i(v) : 0 ≤ i < k}` is linearly
independent for every nonzero `v ∈ 𝔽^{l×m}` and `D(e_{0,0})` is invertible. -/
theorem chk_lemma_6 {𝔽 : Type*} [Field 𝔽] [IsAlgClosed 𝔽] {k l m R : ℕ} [NeZero k] [NeZero l]
    (d : Decomposition 𝔽 k l m R) (hα : ∀ r, d.α r ≠ 0) :
    ∃ (S : GL (Fin k) 𝔽) (T : GL (Fin l) 𝔽), (d.changeBasis S T).StronglyNormalized := by
  exact TensorRankN2M.Dev.Lemma6.main d hα


end TensorRankN2M.ThreeTwoM
end

theorem solution : type_of% @TensorRankN2M.ThreeTwoM.chk_lemma_6 := @TensorRankN2M.ThreeTwoM.chk_lemma_6
