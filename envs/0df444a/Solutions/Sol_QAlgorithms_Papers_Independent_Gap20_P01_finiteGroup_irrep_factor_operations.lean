-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P01.finiteGroup_irrep_factor_operations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:02:55.443613+00:00
-- url     : https://prove2.me/submissions/949dbeef-a7b8-498c-a24b-95a5dc424129

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P01
noncomputable section

open scoped BigOperators Matrix Kronecker ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms
open QAlgorithms.Papers.Independent.Gap20.P01

open QAlgorithms.Papers.Independent.Support21.P09 (Rep UnitaryRep elementaryGates)

theorem g73e_rep_inv_mul {G : Type} [Group G] (X : FiniteIrrep G) (g : G) :
    X.rep g⁻¹ * X.rep g = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

theorem g73e_rep_mul_inv {G : Type} [Group G] (X : FiniteIrrep G) (g : G) :
    X.rep g * X.rep g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem g73e_schur_scalar {G : Type} [Group G] (X : FiniteIrrep G)
    (T : Matrix (Fin X.dim) (Fin X.dim) ℂ) (hT : ∀ g, X.rep g * T = T * X.rep g) :
    ∃ c : ℂ, T = c • 1 := by
  haveI : Nonempty (Fin X.dim) := ⟨⟨0, X.positive⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' T)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  let V := LinearMap.ker (Matrix.toLin' (T - c • 1))
  have hinv : ∀ g w, w ∈ V → (X.rep g).mulVec w ∈ V := by
    intro g w hw
    simp only [V, LinearMap.mem_ker, Matrix.toLin'_apply] at hw ⊢
    rw [Matrix.mulVec_mulVec]
    have : (T - c • 1) * X.rep g = X.rep g * (T - c • 1) := by
      rw [sub_mul, mul_sub, hT g, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
    rw [this, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  rcases X.irreducible V hinv with h | h
  · exfalso
    have hvV : v ∈ V := by
      simp only [V, LinearMap.mem_ker, Matrix.toLin'_apply]
      have := hv.apply_eq_smul
      rw [Matrix.toLin'_apply] at this
      rw [Matrix.sub_mulVec, this, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
    rw [h] at hvV
    exact hv.2 ((Submodule.mem_bot ℂ).mp hvV)
  · have : Matrix.toLin' (T - c • 1) = 0 := LinearMap.ker_eq_top.mp h
    have := (Matrix.toLin' (R := ℂ) (m := Fin X.dim) (n := Fin X.dim)).injective
      (this.trans (map_zero _).symm)
    exact sub_eq_zero.mp this

theorem g73e_schur_zero {G : Type} [Group G] (X Y : FiniteIrrep G)
    (hne : ¬ IrrepEquivalent X Y)
    (T : Matrix (Fin X.dim) (Fin Y.dim) ℂ) (hT : ∀ g, X.rep g * T = T * Y.rep g) :
    T = 0 := by
  by_contra hT0
  have hT0' : Matrix.toLin' T ≠ 0 := by
    intro h; apply hT0
    exact (Matrix.toLin' (R := ℂ) (m := Fin X.dim) (n := Fin Y.dim)).injective
      (h.trans (map_zero _).symm)
  let K := LinearMap.ker (Matrix.toLin' T)
  have hK : ∀ g w, w ∈ K → (Y.rep g).mulVec w ∈ K := by
    intro g w hw
    simp only [K, LinearMap.mem_ker, Matrix.toLin'_apply] at hw ⊢
    rw [Matrix.mulVec_mulVec, ← hT g, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  have hinj : Function.Injective (Matrix.toLin' T) := by
    rcases Y.irreducible K hK with h | h
    · exact LinearMap.ker_eq_bot.mp h
    · exact absurd (LinearMap.ker_eq_top.mp h) hT0'
  let Rg := LinearMap.range (Matrix.toLin' T)
  have hR : ∀ g w, w ∈ Rg → (X.rep g).mulVec w ∈ Rg := by
    intro g w hw
    obtain ⟨u, rfl⟩ := hw
    refine ⟨(Y.rep g).mulVec u, ?_⟩
    simp only [Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hT g]
  have hsurj : Function.Surjective (Matrix.toLin' T) := by
    rcases X.irreducible Rg hR with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) hT0'
    · exact LinearMap.range_eq_top.mp h
  let e := LinearEquiv.ofBijective (Matrix.toLin' T) ⟨hinj, hsurj⟩
  let S : Matrix (Fin Y.dim) (Fin X.dim) ℂ := LinearMap.toMatrix' e.symm.toLinearMap
  apply hne
  refine ⟨T, S, ?_, ?_, hT⟩
  · apply (Matrix.toLin' (R := ℂ) (m := Fin X.dim) (n := Fin X.dim)).injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one]
    simp only [S, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
    exact e.apply_symm_apply v
  · apply (Matrix.toLin' (R := ℂ) (m := Fin Y.dim) (n := Fin Y.dim)).injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one]
    simp only [S, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
    exact e.symm_apply_apply v

theorem g73e_avg_intertwines {G : Type} [Group G] [Fintype G] (X Y : FiniteIrrep G)
    (E : Matrix (Fin X.dim) (Fin Y.dim) ℂ) (h : G) :
    X.rep h * (∑ g, X.rep g * E * Y.rep g⁻¹) = (∑ g, X.rep g * E * Y.rep g⁻¹) * Y.rep h := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  rw [← Equiv.sum_comp (Equiv.mulLeft h) (fun g => X.rep g * E * Y.rep g⁻¹ * Y.rep h)]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Equiv.coe_mulLeft, mul_inv_rev, map_mul, Matrix.mul_assoc]
  rw [g73e_rep_inv_mul, Matrix.mul_one]

theorem g73e_single_entry {m n p q : Type} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix p q ℂ) (k : n) (l : p) (i : m) (j : q) :
    (A * Matrix.single k l (1 : ℂ) * B) i j = A i k * B l j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.single_apply, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]

theorem g73e_orth_ne {G : Type} [Group G] [Fintype G] (X Y : FiniteIrrep G)
    (hne : ¬ IrrepEquivalent X Y) (i : Fin X.dim) (k : Fin X.dim) (l : Fin Y.dim) (j : Fin Y.dim) :
    ∑ g, X.rep g i k * Y.rep g⁻¹ l j = 0 := by
  have hM := g73e_schur_zero X Y hne (∑ g, X.rep g * Matrix.single k l (1 : ℂ) * Y.rep g⁻¹)
    (g73e_avg_intertwines X Y _)
  have := congrFun (congrFun hM i) j
  simpa [Matrix.sum_apply, g73e_single_entry] using this

theorem g73e_orth_eq {G : Type} [Group G] [Fintype G] (X : FiniteIrrep G)
    (i k l j : Fin X.dim) :
    ∑ g, X.rep g i k * X.rep g⁻¹ l j =
      if i = j ∧ k = l then (Fintype.card G : ℂ) / X.dim else 0 := by
  obtain ⟨c, hc⟩ := g73e_schur_scalar X (∑ g, X.rep g * Matrix.single k l (1 : ℂ) * X.rep g⁻¹)
    (g73e_avg_intertwines X X _)
  have htr := congrArg Matrix.trace hc
  rw [Matrix.trace_sum] at htr
  have hterm : ∀ g, Matrix.trace (X.rep g * Matrix.single k l (1 : ℂ) * X.rep g⁻¹) =
      Matrix.trace (Matrix.single k l (1 : ℂ)) := by
    intro g
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, g73e_rep_inv_mul, Matrix.one_mul]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul] at htr
  have hd : (X.dim : ℂ) ≠ 0 := by exact_mod_cast X.positive.ne'
  have hcval : c = (Fintype.card G : ℂ) * Matrix.trace (Matrix.single k l (1 : ℂ)) / X.dim := by
    rw [eq_div_iff hd]; rw [nsmul_eq_mul] at htr; rw [htr]
  have := congrFun (congrFun hc i) j
  simp only [Matrix.sum_apply, g73e_single_entry] at this
  rw [this, hcval]
  by_cases hkl : k = l
  · subst hkl
    rw [Matrix.trace_single_eq_same]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · rw [Matrix.trace_single_eq_of_ne k l (1:ℂ) hkl]
    simp [hkl]

theorem g73e_rep_inv_eq {G : Type} [Group G] (X : FiniteIrrep G) (g : G) :
    X.rep g⁻¹ = (X.rep g)ᴴ := by
  have hu := X.unitary g
  rw [Matrix.mem_unitaryGroup_iff] at hu
  calc X.rep g⁻¹ = X.rep g⁻¹ * (X.rep g * star (X.rep g)) := by rw [hu, Matrix.mul_one]
    _ = (X.rep g)ᴴ := by rw [← Matrix.mul_assoc, g73e_rep_inv_mul, Matrix.one_mul]; rfl

theorem g73e_rep_inv_apply {G : Type} [Group G] (X : FiniteIrrep G) (g : G) (i j : Fin X.dim) :
    X.rep g⁻¹ i j = star (X.rep g j i) := by
  rw [g73e_rep_inv_eq]; rfl

theorem g73e_coef_sq {G : Type} [Fintype G] (d : ℕ) :
    ((Real.sqrt ((d : ℝ) / (Fintype.card G : ℝ)) : ℂ)) * ((Real.sqrt ((d : ℝ) / (Fintype.card G : ℝ)) : ℂ))
      = (d : ℂ) / (Fintype.card G : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast; ring

theorem g73e_FFH {G L : Type} [Group G] [Fintype G] [Fintype L] (D : FiniteDual G L) :
    fourierMinus D * (fourierMinus D)ᴴ = 1 := by
  ext ⟨μ, i, j⟩ ⟨ν, k, l⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, fourierMinus]
  have hterm : ∀ g : G, (Real.sqrt ((D.irrep μ).dim / (Fintype.card G : ℝ)) : ℂ) *
      (D.irrep μ).rep g⁻¹ i j *
      star ((Real.sqrt ((D.irrep ν).dim / (Fintype.card G : ℝ)) : ℂ) * (D.irrep ν).rep g⁻¹ k l) =
      ((Real.sqrt ((D.irrep μ).dim / (Fintype.card G : ℝ)) : ℂ) *
        (Real.sqrt ((D.irrep ν).dim / (Fintype.card G : ℝ)) : ℂ)) *
      ((D.irrep ν).rep g l k * (D.irrep μ).rep g⁻¹ i j) := by
    intro g
    rw [g73e_rep_inv_apply (D.irrep ν) g k l, star_mul', star_star, Complex.star_def,
      Complex.conj_ofReal]
    ring
  simp only [hterm]
  rw [← Finset.mul_sum]
  by_cases h : μ = ν
  · subst h
    rw [g73e_orth_eq, g73e_coef_sq]
    have hd : ((D.irrep μ).dim : ℂ) ≠ 0 := by exact_mod_cast (D.irrep μ).positive.ne'
    have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [Matrix.one_apply]
    by_cases h1 : l = j ∧ k = i
    · obtain ⟨rfl, rfl⟩ := h1
      simp only [and_self, if_true]
      field_simp
    · rw [if_neg h1, if_neg, mul_zero]
      intro h2
      apply h1
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and, Prod.mk.injEq] at h2
      exact ⟨h2.2.symm, h2.1.symm⟩
  · rw [g73e_orth_ne (D.irrep ν) (D.irrep μ) (D.inequivalent ν μ (Ne.symm h)), mul_zero,
      Matrix.one_apply, if_neg]
    intro h2
    exact h (congrArg Sigma.fst h2)

def g73e_rt {G : Type} [Group G] [Fintype G] (h : G) :
    EuclideanSpace ℂ G →ₗ[ℂ] EuclideanSpace ℂ G where
  toFun φ := WithLp.toLp 2 (fun x => φ (x * h))
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

theorem g73e_rt_apply {G : Type} [Group G] [Fintype G] (h : G) (φ : EuclideanSpace ℂ G) (x : G) :
    g73e_rt h φ x = φ (x * h) := rfl

theorem g73e_rt_mul {G : Type} [Group G] [Fintype G] (g h : G) (φ : EuclideanSpace ℂ G) :
    g73e_rt (g * h) φ = g73e_rt g (g73e_rt h φ) := by
  ext x; simp [g73e_rt_apply, mul_assoc]

theorem g73e_rt_one {G : Type} [Group G] [Fintype G] (φ : EuclideanSpace ℂ G) :
    g73e_rt 1 φ = φ := by
  ext x; simp [g73e_rt_apply]

theorem g73e_rt_inner {G : Type} [Group G] [Fintype G] (h : G) (φ ψ : EuclideanSpace ℂ G) :
    inner ℂ (g73e_rt h φ) (g73e_rt h ψ) = inner ℂ φ ψ := by
  simp only [PiLp.inner_apply, g73e_rt_apply]
  exact Equiv.sum_comp (Equiv.mulRight h) (fun x => inner ℂ (φ x) (ψ x))

theorem g73e_kernel_zero {G L : Type} [Group G] [Fintype G] [Fintype L] (D : FiniteDual G L)
    (f : EuclideanSpace ℂ G)
    (hf : ∀ μ (i j : Fin (D.irrep μ).dim), ∑ g, (D.irrep μ).rep g⁻¹ i j * f g = 0) : f = 0 := by
  by_contra hf0
  let K : Submodule ℂ (EuclideanSpace ℂ G) :=
    { carrier := {φ | ∀ μ (i j : Fin (D.irrep μ).dim), ∑ g, (D.irrep μ).rep g⁻¹ i j * φ g = 0}
      add_mem' := by
        intro a b ha hb μ i j
        simp only [Set.mem_ofPred_eq, PiLp.add_apply, mul_add, Finset.sum_add_distrib] at *
        rw [ha, hb, add_zero]
      zero_mem' := by intro μ i j; simp
      smul_mem' := by
        intro c a ha μ i j
        simp only [Set.mem_ofPred_eq, PiLp.smul_apply, smul_eq_mul] at *
        have := ha μ i j
        calc ∑ g, (D.irrep μ).rep g⁻¹ i j * (c * a g)
            = c * ∑ g, (D.irrep μ).rep g⁻¹ i j * a g := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun g _ => by ring
          _ = 0 := by rw [this, mul_zero] }
  have hKmem : ∀ φ, φ ∈ K ↔ ∀ μ (i j : Fin (D.irrep μ).dim),
      ∑ g, (D.irrep μ).rep g⁻¹ i j * φ g = 0 := fun φ => Iff.rfl
  have hKinv : ∀ h, ∀ φ ∈ K, g73e_rt h φ ∈ K := by
    intro h φ hφ
    rw [hKmem] at hφ ⊢
    intro μ i j
    simp only [g73e_rt_apply]
    rw [← Equiv.sum_comp (Equiv.mulRight h⁻¹)]
    simp only [Equiv.coe_mulRight, mul_inv_rev, inv_inv, inv_mul_cancel_right, map_mul,
      Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, hφ, mul_zero, Finset.sum_const_zero]
  let P : ℕ → Prop := fun n => ∃ W : Submodule ℂ (EuclideanSpace ℂ G), W ≤ K ∧
    (∀ h, ∀ φ ∈ W, g73e_rt h φ ∈ W) ∧ W ≠ ⊥ ∧ Module.finrank ℂ W = n
  have hP : ∃ n, P n := ⟨_, K, le_rfl, hKinv, by
    intro hK; apply hf0
    have : f ∈ K := hf
    rw [hK] at this; exact (Submodule.mem_bot ℂ).mp this, rfl⟩
  classical
  obtain ⟨W, hWK, hWinv, hWbot, hWrank⟩ := Nat.find_spec hP
  have hmin : ∀ W' : Submodule ℂ (EuclideanSpace ℂ G), W' ≤ K →
      (∀ h, ∀ φ ∈ W', g73e_rt h φ ∈ W') → W' ≠ ⊥ →
      Module.finrank ℂ W ≤ Module.finrank ℂ W' := by
    intro W' h1 h2 h3
    rw [hWrank]
    exact Nat.find_min' hP ⟨W', h1, h2, h3, rfl⟩
  have hk : 0 < Module.finrank ℂ W :=
    Nat.pos_of_ne_zero (fun h => hWbot (Submodule.finrank_eq_zero.mp h))
  let b := stdOrthonormalBasis ℂ W
  let B : Fin (Module.finrank ℂ W) → EuclideanSpace ℂ G := fun p => (b p : EuclideanSpace ℂ G)
  have hBW : ∀ p, B p ∈ W := fun p => (b p).2
  have hBorth : ∀ p q, inner ℂ (B p) (B q) = if p = q then (1 : ℂ) else 0 := by
    intro p q
    have := orthonormal_iff_ite.mp b.orthonormal p q
    rw [← this]; rfl
  have hexp : ∀ φ ∈ W, φ = ∑ p, inner ℂ (B p) φ • B p := by
    intro φ hφ
    have := b.sum_repr' ⟨φ, hφ⟩
    have h2 := congrArg Subtype.val this
    rw [Submodule.coe_sum] at h2
    exact h2.symm
  have hpars : ∀ φ ∈ W, ∀ ψ ∈ W, ∑ p, inner ℂ φ (B p) * inner ℂ (B p) ψ = inner ℂ φ ψ := by
    intro φ hφ ψ hψ
    exact b.sum_inner_mul_inner ⟨φ, hφ⟩ ⟨ψ, hψ⟩
  let σf : G → Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ :=
    fun g p q => inner ℂ (B p) (g73e_rt g (B q))
  have hrtB : ∀ g q, g73e_rt g (B q) = ∑ p, σf g p q • B p :=
    fun g q => hexp _ (hWinv g _ (hBW q))
  let σ : Rep G (Fin (Module.finrank ℂ W)) :=
    { toFun := σf
      map_one' := by
        ext p q
        simp only [σf, g73e_rt_one, hBorth, Matrix.one_apply]
      map_mul' := by
        intro g h
        ext p q
        simp only [σf, g73e_rt_mul, Matrix.mul_apply]
        rw [hrtB h q, map_sum, inner_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [map_smul, inner_smul_right, mul_comm] }
  have hσ : ∀ g, σ g = σf g := fun g => rfl

  have hunit : UnitaryRep σ := by
    intro g
    rw [Matrix.mem_unitaryGroup_iff']
    ext p q
    rw [Matrix.mul_apply, Matrix.one_apply]
    change ∑ l, star (inner ℂ (B l) (g73e_rt g (B p))) * inner ℂ (B l) (g73e_rt g (B q)) = _
    have : ∀ l, star (inner ℂ (B l) (g73e_rt g (B p))) * inner ℂ (B l) (g73e_rt g (B q)) =
        inner ℂ (g73e_rt g (B p)) (B l) * inner ℂ (B l) (g73e_rt g (B q)) := by
      intro l; rw [← inner_conj_symm (B l) (g73e_rt g (B p))]; exact congrArg (· * _) (star_star _)
    simp only [this]
    rw [hpars _ (hWinv g _ (hBW p)) _ (hWinv g _ (hBW q)), g73e_rt_inner, hBorth]
  let Lc : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ G :=
    { toFun := fun c => ∑ p, c p • B p
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum, smul_smul] }
  have hLc : ∀ c, Lc c = ∑ p, c p • B p := fun c => rfl
  have hLcinner : ∀ c q, inner ℂ (B q) (Lc c) = c q := by
    intro c q
    rw [hLc, inner_sum]
    simp only [inner_smul_right, hBorth, mul_ite, mul_one, mul_zero]
    simp
  have hLcinj : Function.Injective Lc := by
    intro c c' h
    funext q
    rw [← hLcinner c q, ← hLcinner c' q, h]
  have hLcW : ∀ c, Lc c ∈ W := by
    intro c; rw [hLc]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (hBW p)
  have hrtLc : ∀ g c, g73e_rt g (Lc c) = Lc ((σ g).mulVec c) := by
    intro g c
    rw [hLc, hLc, map_sum]
    simp only [map_smul, hrtB, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, hσ,
      Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [mul_comm]
  have hirr : ∀ V : Submodule ℂ (Fin (Module.finrank ℂ W) → ℂ),
      (∀ g v, v ∈ V → (σ g).mulVec v ∈ V) → V = ⊥ ∨ V = ⊤ := by
    intro V hV
    by_cases hVb : V = ⊥
    · exact Or.inl hVb
    right
    let W' := LinearMap.range (Lc ∘ₗ V.subtype)
    have hW'K : W' ≤ K := by
      rintro _ ⟨v, rfl⟩
      exact hWK (hLcW _)
    have hW'inv : ∀ h, ∀ φ ∈ W', g73e_rt h φ ∈ W' := by
      rintro h _ ⟨v, rfl⟩
      refine ⟨⟨(σ h).mulVec v, hV h v v.2⟩, ?_⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
      rw [hrtLc]
    have hW'bot : W' ≠ ⊥ := by
      intro hb
      apply hVb
      rw [Submodule.eq_bot_iff]
      intro v hv
      have : Lc v ∈ W' := ⟨⟨v, hv⟩, rfl⟩
      rw [hb] at this
      exact hLcinj (((Submodule.mem_bot ℂ).mp this).trans (map_zero Lc).symm)
    have h1 := hmin W' hW'K hW'inv hW'bot
    have h2 : Module.finrank ℂ W' = Module.finrank ℂ V :=
      LinearMap.finrank_range_of_inj (hLcinj.comp Subtype.val_injective)
    have h3 := Submodule.finrank_le V
    simp only [Module.finrank_fin_fun] at h3
    apply Submodule.eq_top_of_finrank_eq
    simp only [Module.finrank_fin_fun]
    omega
  let σI : FiniteIrrep G := ⟨Module.finrank ℂ W, hk, σ, hunit, hirr⟩
  obtain ⟨μ, T, S, hTS, hST, hint⟩ := D.complete σI
  have hσTS : ∀ g, σ g = T * (D.irrep μ).rep g * S := by
    intro g
    have := hint g
    calc σ g = σ g * (T * S) := by rw [hTS, Matrix.mul_one]
      _ = T * (D.irrep μ).rep g * S := by rw [← Matrix.mul_assoc]; exact congrArg (· * S) this
  have hKσ : ∀ w ∈ K, ∀ p q, ∑ g, σ g⁻¹ p q * w g = 0 := by
    intro w hw p q
    simp only [hσTS, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    have := hw μ a b'
    calc ∑ g, T p a * (D.irrep μ).rep g⁻¹ a b' * S b' q * w g
        = T p a * S b' q * ∑ g, (D.irrep μ).rep g⁻¹ a b' * w g := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun g _ => by ring
      _ = 0 := by rw [this, mul_zero]
  have hBval : ∀ q g, B q g = ∑ l, σ g l q * B l 1 := by
    intro q g
    have := congrArg (fun φ : EuclideanSpace ℂ G => φ 1) (hrtB g q)
    simp only [g73e_rt_apply, one_mul] at this
    rw [this, WithLp.ofLp_sum, Finset.sum_apply]
    rfl
  have hB1 : ∀ q, B q 1 = 0 := by
    intro q
    have h0 := hKσ (B q) (hWK (hBW q)) q q
    rw [Finset.sum_congr rfl (fun g _ => by rw [hBval q g])] at h0
    simp only [Finset.mul_sum] at h0
    rw [Finset.sum_comm] at h0
    have h4 : ∀ l, ∑ g, σ g⁻¹ q q * (σ g l q * B l 1) =
        B l 1 * ∑ g, σI.rep g l q * σI.rep g⁻¹ q q := by
      intro l; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun g _ => by
        show σ g⁻¹ q q * (σ g l q * B l 1) = B l 1 * (σ g l q * σ g⁻¹ q q); ring
    simp only [h4, g73e_orth_eq] at h0
    simp only [and_true, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h0
    have hG : (Fintype.card G : ℂ) / (Module.finrank ℂ W : ℂ) ≠ 0 := by
      have : (Module.finrank ℂ W : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      exact div_ne_zero (by exact_mod_cast Fintype.card_ne_zero) this
    exact (mul_eq_zero.mp h0).resolve_right hG
  let q0 : Fin (Module.finrank ℂ W) := ⟨0, hk⟩
  have hBz : B q0 = 0 := by
    ext g
    rw [hBval]
    simp [hB1]
  have := hBorth q0 q0
  rw [hBz, inner_zero_left, if_pos rfl] at this
  exact zero_ne_one this

theorem g73e_coef_ne {G : Type} [Group G] [Fintype G] (d : ℕ) (hd : 0 < d) :
    ((Real.sqrt ((d : ℝ) / (Fintype.card G : ℝ)) : ℂ)) ≠ 0 := by
  have : 0 < Real.sqrt ((d : ℝ) / (Fintype.card G : ℝ)) := by
    apply Real.sqrt_pos.mpr
    have : (0:ℝ) < Fintype.card G := by
      have : Nonempty G := ⟨1⟩
      exact_mod_cast Fintype.card_pos
    positivity
  exact_mod_cast this.ne'

theorem g73e_FHF {G L : Type} [Group G] [Fintype G] [Fintype L] (D : FiniteDual G L) :
    (fourierMinus D)ᴴ * fourierMinus D = 1 := by
  have hv : ∀ v : G → ℂ, ((fourierMinus D)ᴴ * fourierMinus D).mulVec v = v := by
    intro v
    let w := v - ((fourierMinus D)ᴴ * fourierMinus D).mulVec v
    have hw : (fourierMinus D).mulVec w = 0 := by
      simp only [w, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, g73e_FFH,
        Matrix.one_mul, sub_self]
    have hw0 : WithLp.toLp 2 w = (0 : EuclideanSpace ℂ G) := by
      apply g73e_kernel_zero D
      intro μ i j
      have := congrFun hw ⟨μ, (i, j)⟩
      simp only [Matrix.mulVec, dotProduct, fourierMinus, Pi.zero_apply] at this
      have hc := g73e_coef_ne (G := G) (D.irrep μ).dim (D.irrep μ).positive
      have h2 : (Real.sqrt (((D.irrep μ).dim : ℝ) / (Fintype.card G : ℝ)) : ℂ) *
          ∑ g, (D.irrep μ).rep g⁻¹ i j * w g = 0 := by
        rw [Finset.mul_sum, ← this]
        exact Finset.sum_congr rfl fun g _ => by ring
      exact (mul_eq_zero.mp h2).resolve_left hc
    have : w = 0 := by
      have := congrArg WithLp.ofLp hw0
      simpa using this
    exact (sub_eq_zero.mp this).symm
  apply (Matrix.toLin' (R := ℂ) (m := G) (n := G)).injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hv, Matrix.one_mulVec]

theorem g73e_C_unitary {G I : Type} [Group G] [Fintype G] [Fintype I]
    (R : Rep G I) (hR : UnitaryRep R) :
    (controlledRep R)ᴴ * controlledRep R = 1 := by
  ext ⟨g, x⟩ ⟨h, y⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, controlledRep, Fintype.sum_prod_type]
  have hu := hR g
  rw [Matrix.mem_unitaryGroup_iff'] at hu
  by_cases hgh : g = h
  · subst hgh
    have := congrFun (congrFun hu x) y
    rw [Matrix.mul_apply] at this
    simp only [Matrix.star_apply] at this
    rw [Matrix.one_apply]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Prod.mk.injEq, true_and]
    rw [Finset.sum_eq_single g]
    · simp only [if_true]
      rw [this, Matrix.one_apply]
    · intro b _ hb
      simp only [if_neg hb, star_zero, zero_mul, Finset.sum_const_zero]
    · simp
  · rw [Matrix.one_apply, if_neg (by simp [hgh])]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun z _ => ?_
    by_cases hk : k = g
    · subst hk; simp [hgh]
    · simp only [if_neg hk, star_zero, zero_mul]

theorem g73e_F3_unitary {G L I : Type} [Group G] [Fintype G] [Fintype L] [Fintype I]
    (D : FiniteDual G L) (R : Rep G I) (hR : UnitaryRep R) :
    (figureThree D R)ᴴ * figureThree D R = 1 := by
  unfold figureThree
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one]
  have e1 : ((fourierMinus D)ᴴ ⊗ₖ (1 : Matrix I I ℂ)) * (fourierMinus D ⊗ₖ (1 : Matrix I I ℂ)) = 1 := by
    rw [← Matrix.mul_kronecker_mul, g73e_FHF, Matrix.one_mul, Matrix.one_kronecker_one]
  have e2 : (fourierMinus D ⊗ₖ (1 : Matrix I I ℂ)) * ((fourierMinus D)ᴴ ⊗ₖ (1 : Matrix I I ℂ)) = 1 := by
    rw [← Matrix.mul_kronecker_mul, g73e_FFH, Matrix.one_mul, Matrix.one_kronecker_one]
  calc _ = (fourierMinus D ⊗ₖ (1 : Matrix I I ℂ)) * (controlledRep R)ᴴ *
        (((fourierMinus D)ᴴ ⊗ₖ (1 : Matrix I I ℂ)) * (fourierMinus D ⊗ₖ (1 : Matrix I I ℂ))) *
        controlledRep R * ((fourierMinus D)ᴴ ⊗ₖ (1 : Matrix I I ℂ)) := by
          simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [e1, Matrix.mul_one, Matrix.mul_assoc _ (controlledRep R)ᴴ, g73e_C_unitary R hR,
        Matrix.mul_one, e2]

theorem g73e_Fminus_aux {G L : Type} [Group G] [Fintype G] [Fintype L] (D : FiniteDual G L)
    (g : G) : ∑ a, star (fourierMinus D a g) * auxiliaryStart D a =
      ((Real.sqrt (Fintype.card G))⁻¹ : ℂ) := by
  simp only [auxiliaryStart, ket, EuclideanSpace.single, PiLp.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [fourierMinus, D.trivialEntry]
  have h1 : (((D.irrep D.trivial).dim : ℕ) : ℝ) = 1 := by exact_mod_cast D.trivialDim
  rw [h1, star_mul', Complex.star_def, Complex.conj_ofReal, map_one, mul_one, one_div,
    Real.sqrt_inv]
  push_cast; rfl

theorem g73e_bd_mulVec {L : Type} [Fintype L] [DecidableEq L] {m n : L → ℕ}
    (M1 : ∀ a, Matrix (Fin (m a)) (Fin (m a)) ℂ) (M2 : ∀ a, Matrix (Fin (n a)) (Fin (n a)) ℂ)
    (φ : (Σ a, Fin (m a) × Fin (n a)) → ℂ) (a : L) (p : Fin (m a)) (k : Fin (n a)) :
    (Matrix.blockDiagonal' (fun a => M1 a ⊗ₖ M2 a)).mulVec φ ⟨a, (p, k)⟩ =
      ∑ p', ∑ k', M1 a p p' * M2 a k k' * φ ⟨a, (p', k')⟩ := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single a]
  · simp only [Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  · intro b _ hb
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hb), zero_mul]
  · simp

theorem g73e_F3_apply {G L I : Type} [Group G] [Fintype G] [Fintype L] [Fintype I]
    (D : FiniteDual G L) (R : Rep G I) (ψ : EuclideanSpace ℂ I) (a : FourierLabel D) (x : I) :
    act (figureThree D R) (tensorVec (auxiliaryStart D) ψ) (a, x) =
      ((Real.sqrt (Fintype.card G))⁻¹ : ℂ) *
        ∑ g, fourierMinus D a g * ((R g).mulVec (WithLp.ofLp ψ)) x := by
  unfold act figureThree
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h1 : ((fourierMinus D)ᴴ ⊗ₖ (1 : Matrix I I ℂ)).mulVec
      (WithLp.ofLp (tensorVec (auxiliaryStart D) ψ)) =
      fun p => ((Real.sqrt (Fintype.card G))⁻¹ : ℂ) * ψ p.2 := by
    funext ⟨g, y⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
      Matrix.one_apply, tensorVec, Matrix.conjTranspose_apply]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    rw [← g73e_Fminus_aux D g, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  have h2 : (controlledRep R).mulVec (fun p : G × I => ((Real.sqrt (Fintype.card G))⁻¹ : ℂ) * ψ p.2) =
      fun p => ((Real.sqrt (Fintype.card G))⁻¹ : ℂ) * ((R p.1).mulVec (WithLp.ofLp ψ)) p.2 := by
    funext ⟨g, y⟩
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, controlledRep]
    rw [Finset.sum_eq_single g]
    · simp only [if_true, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [h1, h2]
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  ring

theorem g73e_const {G : Type} [Group G] [Fintype G] (d : ℕ) (hd : 0 < d) :
    ((Real.sqrt (Fintype.card G))⁻¹ : ℂ) * (Real.sqrt ((d : ℝ) / (Fintype.card G : ℝ)) : ℂ) *
      ((Fintype.card G : ℂ) / d) = ((Real.sqrt d)⁻¹ : ℂ) := by
  have hG : (0:ℝ) < Fintype.card G := by
    have : Nonempty G := ⟨1⟩
    exact_mod_cast Fintype.card_pos
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have e : ((Fintype.card G : ℂ) / d) = (((Fintype.card G : ℝ) / d : ℝ) : ℂ) := by push_cast; rfl
  rw [e, ← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [Real.sqrt_div' _ hG.le]
  have h1 := Real.sq_sqrt hG.le
  have h2 := Real.sq_sqrt hd'.le
  have h3 : 0 < Real.sqrt (Fintype.card G) := Real.sqrt_pos.mpr hG
  have h4 : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd'
  have key : ∀ s t : ℝ, 0 < s → 0 < t → s⁻¹ * (t / s) * (s ^ 2 / t ^ 2) = t⁻¹ := by
    intro s t hs ht; field_simp
  have := key _ _ h3 h4
  rw [h1, h2] at this
  exact this

theorem g73e_F3_formula {G L I : Type} [Group G] [Fintype G] [Fintype L] [Fintype I]
    (D : FiniteDual G L) (R : Rep G I) (B : ReducingBasis D R) (ψ : EuclideanSpace ℂ I)
    (μ : L) (i j : Fin (D.irrep μ).dim) (x : I) :
    act (figureThree D R) (tensorVec (auxiliaryStart D) ψ) (⟨μ, (i, j)⟩, x) =
      ((Real.sqrt (D.irrep μ).dim)⁻¹ : ℂ) * ∑ p : Fin (B.multiplicity μ),
        B.synthesis x ⟨μ, (p, j)⟩ * reducingCoefficients D R B ψ ⟨μ, (p, i)⟩ := by
  rw [g73e_F3_apply]
  have hR : ∀ g, R g = B.synthesis * reducingAction D B.multiplicity g * B.synthesisᴴ := by
    intro g
    rw [← B.intertwines g, Matrix.mul_assoc, B.spans, Matrix.mul_one]
  have hRx : ∀ g, ((R g).mulVec (WithLp.ofLp ψ)) x = ∑ ν, ∑ p, ∑ k, ∑ k',
      B.synthesis x ⟨ν, (p, k)⟩ * ((D.irrep ν).rep g k k' *
        reducingCoefficients D R B ψ ⟨ν, (p, k')⟩) := by
    intro g
    rw [hR, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    conv_lhs => rw [Matrix.mulVec]
    simp only [dotProduct, Fintype.sum_sigma, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun p _ =>
      Finset.sum_congr rfl fun k _ => ?_
    unfold reducingAction
    rw [g73e_bd_mulVec (fun a => (1 : Matrix (Fin (B.multiplicity a)) (Fin (B.multiplicity a)) ℂ))
      (fun a => (D.irrep a).rep g)]
    rw [Finset.sum_eq_single p (fun b _ hb => by simp [Matrix.one_apply, Ne.symm hb]) (by simp)]
    simp only [Matrix.one_apply, if_true, one_mul, Finset.mul_sum]
    rfl
  simp only [hRx]
  have hre : ((Real.sqrt (Fintype.card G))⁻¹ : ℂ) * ∑ g, fourierMinus D ⟨μ, (i, j)⟩ g *
      (∑ ν, ∑ p, ∑ k, ∑ k', B.synthesis x ⟨ν, (p, k)⟩ * ((D.irrep ν).rep g k k' *
        reducingCoefficients D R B ψ ⟨ν, (p, k')⟩)) =
      ∑ ν, ∑ p : Fin (B.multiplicity ν), ∑ k, ∑ k', B.synthesis x ⟨ν, (p, k)⟩ *
        reducingCoefficients D R B ψ ⟨ν, (p, k')⟩ *
        (((Real.sqrt (Fintype.card G))⁻¹ : ℂ) *
          (Real.sqrt (((D.irrep μ).dim : ℝ) / (Fintype.card G : ℝ)) : ℂ) *
          ∑ g, (D.irrep ν).rep g k k' * (D.irrep μ).rep g⁻¹ i j) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k' _ => ?_
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [fourierMinus]
    ring
  rw [hre]
  rw [Finset.sum_eq_single μ]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_eq_single j (fun b _ hb => Finset.sum_eq_zero fun k' _ => by
      rw [g73e_orth_eq, if_neg (fun h => hb h.1), mul_zero, mul_zero]) (by simp)]
    rw [Finset.sum_eq_single i (fun b _ hb => by
      rw [g73e_orth_eq, if_neg (fun h => hb h.2), mul_zero, mul_zero]) (by simp)]
    rw [g73e_orth_eq, if_pos ⟨rfl, rfl⟩, ← g73e_const (G := G) (D.irrep μ).dim (D.irrep μ).positive]
    ring
  · intro ν _ hν
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun k' _ => ?_
    rw [g73e_orth_ne (D.irrep ν) (D.irrep μ) (D.inequivalent ν μ hν), mul_zero, mul_zero]
  · simp

theorem g73e_act_mul {ι : Type} [Fintype ι] (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A * B) v = act A (act B v) := by
  unfold act; simp [Matrix.mulVec_mulVec]

theorem g73e_phys_coef {G L I : Type} [Group G] [Fintype G] [Fintype L] [Fintype I]
    (D : FiniteDual G L) (R : Rep G I) (B : ReducingBasis D R)
    (A : ∀ a, Matrix.unitaryGroup (Fin (D.irrep a).dim) ℂ) (ψ : EuclideanSpace ℂ I)
    (μ : L) (p : Fin (B.multiplicity μ)) (i : Fin (D.irrep μ).dim) :
    reducingCoefficients D R B (act (physicalFactor D R B A) ψ) ⟨μ, (p, i)⟩ =
      ∑ i', (A μ : Matrix (Fin (D.irrep μ).dim) (Fin (D.irrep μ).dim) ℂ) i i' *
        reducingCoefficients D R B ψ ⟨μ, (p, i')⟩ := by
  unfold reducingCoefficients applyRect act physicalFactor
  simp only [Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, B.columns, Matrix.one_mul, ← Matrix.mulVec_mulVec]
  change (Matrix.blockDiagonal' (fun a : L =>
      (1 : Matrix (Fin (B.multiplicity a)) (Fin (B.multiplicity a)) ℂ) ⊗ₖ
        (A a : Matrix (Fin (D.irrep a).dim) (Fin (D.irrep a).dim) ℂ))).mulVec _ ⟨μ, (p, i)⟩ = _
  rw [g73e_bd_mulVec]
  rw [Finset.sum_eq_single p (fun b _ hb => by simp [Matrix.one_apply, Ne.symm hb]) (by simp)]
  simp only [Matrix.one_apply, if_true, one_mul]

theorem g73e_factor {G L I : Type} [Group G] [Fintype G] [Fintype L] [Fintype I]
    (D : FiniteDual G L) (R : Rep G I) (hR : UnitaryRep R) (B : ReducingBasis D R)
    (A : ∀ a, Matrix.unitaryGroup (Fin (D.irrep a).dim) ℂ) (ψ : EuclideanSpace ℂ I) :
    act ((figureThree D R)ᴴ *
        (auxiliaryFactor D A ⊗ₖ (1 : Matrix I I ℂ)) * figureThree D R)
        (tensorVec (auxiliaryStart D) ψ) =
      tensorVec (auxiliaryStart D) (act (physicalFactor D R B A) ψ) := by
  have key : act (auxiliaryFactor D A ⊗ₖ (1 : Matrix I I ℂ))
      (act (figureThree D R) (tensorVec (auxiliaryStart D) ψ)) =
      act (figureThree D R) (tensorVec (auxiliaryStart D) (act (physicalFactor D R B A) ψ)) := by
    ext ⟨⟨μ, i, j⟩, x⟩
    rw [g73e_F3_formula D R B _ μ i j x]
    simp only [g73e_phys_coef]
    have h1 : (act (auxiliaryFactor D A ⊗ₖ (1 : Matrix I I ℂ))
        (act (figureThree D R) (tensorVec (auxiliaryStart D) ψ))) (⟨μ, (i, j)⟩, x) =
        (auxiliaryFactor D A).mulVec
          (fun b => act (figureThree D R) (tensorVec (auxiliaryStart D) ψ) (b, x)) ⟨μ, (i, j)⟩ := by
      conv_lhs => unfold act
      simp only [WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
        Fintype.sum_prod_type, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_eq_single x (fun y _ hy => by rw [if_neg (Ne.symm hy), zero_mul]) (by simp),
        if_pos rfl]
      congr 1
      simp only [act, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    rw [h1]
    unfold auxiliaryFactor
    rw [g73e_bd_mulVec]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, g73e_F3_formula D R B ψ]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i' _ => ?_
    ring
  rw [g73e_act_mul, g73e_act_mul, key, ← g73e_act_mul, g73e_F3_unitary D R hR]
  unfold act; simp

variable {G L I : Type} [Group G] [Fintype G] [Fintype L]
  [Fintype I]

/-- PDF p.4, last paragraph: extract, apply an available controlled irrep
operation, and reverse extraction. The auxiliary register is restored,
multiplicity coordinates are untouched, and the identity is coherent across
all irrep labels. The Fourier convention correction is the one explicitly
specified in fourierMinus. This does not assert efficient arbitrary A_mu. -/
theorem solution (D : FiniteDual G L)
    (R : Rep G I) (hR : UnitaryRep R) (B : ReducingBasis D R)
    (A : ∀ a, Matrix.unitaryGroup (Fin (D.irrep a).dim) ℂ) :
    ∀ psi : EuclideanSpace ℂ I,
      act ((figureThree D R)ᴴ *
        (auxiliaryFactor D A ⊗ₖ (1 : Matrix I I ℂ)) * figureThree D R)
        (tensorVec (auxiliaryStart D) psi) =
      tensorVec (auxiliaryStart D) (act (physicalFactor D R B A) psi) := by
  intro psi
  exact g73e_factor D R hR B A psi


end
