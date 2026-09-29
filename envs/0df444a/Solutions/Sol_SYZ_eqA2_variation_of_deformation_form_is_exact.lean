-- Prove2me | solution 1 for SYZ.eqA2_variation_of_deformation_form_is_exact
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:24:48.232235+00:00
-- url     : https://prove2.me/submissions/fc5907c1-9c0e-4e8a-8f20-4299034a520e

import Mathlib
import Definitions.Def_syz_flat_model

/-! a8b6c7ce SYZ.eqA2_variation_of_deformation_form_is_exact.
Route: `θ^b` is closed in `x` for every parameter (harmonic gauge), and the family is jointly
smooth, so by symmetry of second derivatives `∂_a θ^b` is again a closed 1-form on `ℝ^n`.
Mathlib's Poincaré lemma for convex sets (`Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`)
then gives a primitive on `univ`. No `Theorems.*` module is imported. -/

set_option autoImplicit false

namespace SYZL

open SYZ

section Glue

variable {n m : ℕ}

/-- `x`-direction `j` and `t`-direction `a` in `Dom m × Dom n` -/
noncomputable def vX (m : ℕ) {n : ℕ} (j : Fin n) : Dom m × Dom n := (0, basis j)
noncomputable def vT {m : ℕ} (n : ℕ) (a : Fin m) : Dom m × Dom n := (basis a, 0)

/-- expand a vector of `Dom k` in the standard basis -/
lemma dom_expand {k : ℕ} (v : Dom k) : v = ∑ c, v c • basis c := by
  ext i
  simp [basis, Finset.sum_apply, Pi.single_apply]

lemma fderiv_expand {k : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h : Dom k → V) (t v : Dom k) : fderiv ℝ h t v = ∑ c, v c • D h c t := by
  conv_lhs => rw [dom_expand v]
  simp [map_sum, map_smul, D]

lemma D_right {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : Dom m × Dom n → V)
    (t : Dom m) (x : Dom n) (hd : DifferentiableAt ℝ h (t, x)) (j : Fin n) :
    D (fun y => h (t, y)) j x = fderiv ℝ h (t, x) (vX m j) := by
  have H : HasFDerivAt (fun y => h (t, y))
      ((fderiv ℝ h (t, x)).comp (ContinuousLinearMap.inr ℝ (Dom m) (Dom n))) x :=
    hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  unfold D
  rw [H.fderiv]
  rfl

lemma D_left {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : Dom m × Dom n → V)
    (t : Dom m) (x : Dom n) (hd : DifferentiableAt ℝ h (t, x)) (a : Fin m) :
    D (fun s => h (s, x)) a t = fderiv ℝ h (t, x) (vT n a) := by
  have H : HasFDerivAt (fun s => h (s, x))
      ((fderiv ℝ h (t, x)).comp (ContinuousLinearMap.inl ℝ (Dom m) (Dom n))) t :=
    hd.hasFDerivAt.comp t (hasFDerivAt_prodMk_left t x)
  unfold D
  rw [H.fderiv]
  rfl

/-- the family as a map on `Dom m × Dom n` -/
noncomputable def Phi (S : SYZFamily n m) : Dom m × Dom n → Amb n := fun p => S.F p.1 p.2

lemma Phi_smooth (S : SYZFamily n m) (k : ℕ) : ContDiff ℝ k (Phi S) :=
  S.smooth.of_le (by exact_mod_cast le_top)

lemma Phi_diff (S : SYZFamily n m) : Differentiable ℝ (Phi S) :=
  (Phi_smooth S 1).differentiable (by norm_num)

lemma cols_smooth (S : SYZFamily n m) (k : ℕ) (u : Dom m × Dom n) :
    ContDiff ℝ k (fun p => fderiv ℝ (Phi S) p u) :=
  ((Phi_smooth S (k + 1)).fderiv_right (m := k) (by norm_cast)).clm_apply contDiff_const

lemma DF_eq (S : SYZFamily n m) (t : Dom m) (x : Dom n) (j : Fin n) :
    D (S.F t) j x = fderiv ℝ (Phi S) (t, x) (vX m j) :=
  D_right (Phi S) t x (Phi_diff S _) j

lemma DFt_eq (S : SYZFamily n m) (t : Dom m) (x : Dom n) (a : Fin m) :
    D (fun s => S.F s x) a t = fderiv ℝ (Phi S) (t, x) (vT n a) :=
  D_left (Phi S) t x (Phi_diff S _) a

lemma thetaM_eq (S : SYZFamily n m) (a : Fin m) (t : Dom m) (x : Dom n) (i : Fin n) :
    thetaM S.F a t x i =
      kForm (fderiv ℝ (Phi S) (t, x) (vT n a)) (fderiv ℝ (Phi S) (t, x) (vX m i)) := by
  unfold thetaM; rw [DF_eq, DFt_eq]

lemma kForm_smooth {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (k : ℕ)
    (f g : P → Amb n) (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) :
    ContDiff ℝ k (fun p => kForm (f p) (g p)) :=
  Complex.imCLM.contDiff.comp (hf.inner ℂ hg)

lemma theta_smooth (S : SYZFamily n m) (k : ℕ) (a : Fin m) (i : Fin n) :
    ContDiff ℝ k (fun p : Dom m × Dom n => thetaM S.F a p.1 p.2 i) := by
  simp only [thetaM_eq]
  exact kForm_smooth k _ _ (cols_smooth S k _) (cols_smooth S k _)

/-- directional derivative of a directional derivative -/
lemma fderiv_fderiv_apply {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (h : P → ℝ) (hh : ContDiff ℝ 2 h) (p v w : P) :
    fderiv ℝ (fun q => fderiv ℝ h q w) p v = fderiv ℝ (fderiv ℝ h) p v w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ h) p :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) p
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

/-- the variation `∂_a θ^b` as a function of `x` -/
noncomputable def varT (S : SYZFamily n m) (a b : Fin m) (t : Dom m) (i : Fin n) (y : Dom n) : ℝ :=
  D (fun s => thetaM S.F b s y i) a t

lemma varT_eq (S : SYZFamily n m) (a b : Fin m) (t : Dom m) (i : Fin n) (y : Dom n) :
    varT S a b t i y =
      fderiv ℝ (fun p : Dom m × Dom n => thetaM S.F b p.1 p.2 i) (t, y) (vT n a) :=
  D_left (fun p : Dom m × Dom n => thetaM S.F b p.1 p.2 i) t y
    (((theta_smooth S 1 b i).differentiable (by norm_num)) _) a

lemma varT_smooth (S : SYZFamily n m) (a b : Fin m) (t : Dom m) (i : Fin n) :
    ContDiff ℝ 1 (varT S a b t i) := by
  have h2 := theta_smooth S 2 b i
  have h1 : ContDiff ℝ 1 (fun p : Dom m × Dom n =>
      fderiv ℝ (fun p : Dom m × Dom n => thetaM S.F b p.1 p.2 i) p (vT n a)) :=
    (h2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have : varT S a b t i = fun y => fderiv ℝ (fun p : Dom m × Dom n => thetaM S.F b p.1 p.2 i)
      (t, y) (vT n a) := funext fun y => varT_eq S a b t i y
  rw [this]
  exact h1.comp ((contDiff_const (c := t)).prodMk contDiff_id)

/-- `∂_a θ^b` is closed in `x` -/
theorem varT_closed (S : SYZFamily n m) (a b : Fin m) (t : Dom m) (i j : Fin n) (x : Dom n) :
    D (varT S a b t i) j x = D (varT S a b t j) i x := by
  set Θ : Fin n → Dom m × Dom n → ℝ := fun k p => thetaM S.F b p.1 p.2 k with hΘ
  have hs : ∀ k, ContDiff ℝ 2 (Θ k) := fun k => theta_smooth S 2 b k
  -- closedness in `x` of `θ^b`, as an identity of functions of `p`
  have hcl : ∀ k l, (fun p => fderiv ℝ (Θ k) p (vX m l)) = fun p => fderiv ℝ (Θ l) p (vX m k) := by
    intro k l
    funext p
    have e1 := D_right (Θ k) p.1 p.2 (((hs k).differentiable (by norm_num)) _) l
    have e2 := D_right (Θ l) p.1 p.2 (((hs l).differentiable (by norm_num)) _) k
    have hh := (S.harmonic p.1 b).1 l k p.2
    simp only [hΘ] at e1 e2
    rw [← e1, ← e2]
    exact hh
  have key : ∀ k l, D (varT S a b t k) l x =
      fderiv ℝ (fun p => fderiv ℝ (Θ k) p (vX m l)) (t, x) (vT n a) := by
    intro k l
    have hfun : varT S a b t k = fun y => fderiv ℝ (Θ k) (t, y) (vT n a) :=
      funext fun y => varT_eq S a b t k y
    have hg : ContDiff ℝ 1 (fun p => fderiv ℝ (Θ k) p (vT n a)) :=
      ((hs k).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    rw [hfun, D_right (fun p => fderiv ℝ (Θ k) p (vT n a)) t x
      ((hg.differentiable (by norm_num)) _) l]
    rw [fderiv_fderiv_apply _ (hs k), fderiv_fderiv_apply _ (hs k)]
    exact (hs k).contDiffAt.isSymmSndFDerivAt (by simp) _ _
  rw [key, key, hcl]

/-- the `k`-th coordinate functional on `Dom n` -/
noncomputable def pr (k : Fin n) : Dom n →L[ℝ] ℝ := EuclideanSpace.proj k

@[simp] lemma pr_apply (k : Fin n) (w : Dom n) : pr k w = w k := rfl

end Glue

end SYZL

open SYZ in
theorem solution {n m : ℕ}
    (S : SYZFamily n m) (a b : Fin m) (t : Dom m) :
    ∃ psi : Dom n → ℝ, ∀ (x : Dom n) (i : Fin n),
      D (fun s => thetaM S.F b s x i) a t = D psi i x := by
  set v : Fin n → Dom n → ℝ := fun k => SYZL.varT S a b t k with hv
  have hvd : ∀ k, Differentiable ℝ (v k) := fun k =>
    (SYZL.varT_smooth S a b t k).differentiable (by norm_num)
  set ω : Dom n → Dom n →L[ℝ] ℝ := fun y => ∑ k, v k y • SYZL.pr k with hω
  have hωd : ∀ y, HasFDerivAt ω (∑ k, (fderiv ℝ (v k) y).smulRight (SYZL.pr k)) y := by
    intro y
    exact HasFDerivAt.fun_sum fun k _ => ((hvd k) y).hasFDerivAt.smul_const (SYZL.pr k)
  have hωdiff : DifferentiableOn ℝ ω Set.univ := fun y _ =>
    (hωd y).differentiableAt.differentiableWithinAt
  have happ : ∀ y u w, fderiv ℝ ω y u w = ∑ k, ∑ j, u j * D (v k) j y * w k := by
    intro y u w
    rw [(hωd y).fderiv]
    simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [SYZL.fderiv_expand, Finset.sum_smul, sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [smul_eq_mul, FunLike.coe_smul, Pi.smul_apply, SYZL.pr_apply]
  have hsymm : ∀ y ∈ Set.univ, ∀ u w, fderiv ℝ ω y u w = fderiv ℝ ω y w u := by
    intro y _ u w
    rw [happ, happ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hv]
    simp only
    rw [SYZL.varT_closed S a b t j k y]
    ring
  obtain ⟨f, hf⟩ := convex_univ.exists_forall_hasFDerivAt_of_fderiv_symmetric isOpen_univ
    hωdiff hsymm
  refine ⟨f, fun x i => ?_⟩
  unfold D
  rw [(hf x (Set.mem_univ x)).fderiv]
  simp only [hω, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    SYZL.pr_apply, smul_eq_mul, basis]
  rw [Finset.sum_eq_single i]
  · simp [hv, SYZL.varT, D, basis]
  · intro k _ hk
    simp [hk]
  · simp
