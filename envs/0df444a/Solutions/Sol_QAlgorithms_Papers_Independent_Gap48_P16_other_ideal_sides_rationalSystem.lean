-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P16.other_ideal_sides_rationalSystem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:45:25.275194+00:00
-- url     : https://prove2.me/submissions/52b2b9a9-7137-467d-8db2-2c8659e5d72b

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16
noncomputable section

universe u

open QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Cofinite

variable (R A : Type u) [CommRing R] [Ring A] [Algebra R A]

variable {R A}

theorem g74r_exists_fin {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (x : M ⊗[R] N) :
    ∃ (n : ℕ) (m : Fin n → M) (p : Fin n → N), x = ∑ i, m i ⊗ₜ[R] p i := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a b => exact ⟨1, fun _ => a, fun _ => b, by simp⟩
  | add x y hx hy =>
    obtain ⟨n, m, p, rfl⟩ := hx
    obtain ⟨n', m', p', rfl⟩ := hy
    refine ⟨n + n', Fin.append m m', Fin.append p p', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

theorem g74r_alpha_sum {R A P M : Type u} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
    (b : P →ₗ[R] A →ₗ[R] R) {n : ℕ} (m : Fin n → M) (p : Fin n → P) (a : A) :
    pairingAlpha b M (∑ i, m i ⊗ₜ[R] p i) a = ∑ i, b (p i) a • m i := by
  rw [map_sum, LinearMap.sum_apply]
  rfl
theorem g74r_cof_top {R A : Type u} [CommRing R] [Ring A] [Algebra R A] :
    IsCofiniteLeft R A ⊤ := by
  unfold IsCofiniteLeft LeftQuotient
  haveI : Subsingleton (A ⧸ (⊤ : Submodule A A).restrictScalars R) :=
    Submodule.Quotient.subsingleton_iff.2 (by simp)
  infer_instance

theorem g74r_cof_inf {R A : Type u} [CommRing R] [Ring A] [Algebra R A] [IsNoetherianRing R]
    (I J : Submodule A A) (hI : IsCofiniteLeft R A I) (hJ : IsCofiniteLeft R A J) :
    IsCofiniteLeft R A (I ⊓ J) := by
  unfold IsCofiniteLeft LeftQuotient at *
  let f : A →ₗ[R] (A ⧸ I.restrictScalars R) × (A ⧸ J.restrictScalars R) :=
    (I.restrictScalars R).mkQ.prod (J.restrictScalars R).mkQ
  have h1 : (I ⊓ J).restrictScalars R ≤ LinearMap.ker f := by
    intro a ha
    simp only [Submodule.restrictScalars_mem, Submodule.mem_inf] at ha
    simp [f, Submodule.Quotient.mk_eq_zero, ha.1, ha.2]
  have h2 : LinearMap.ker f ≤ (I ⊓ J).restrictScalars R := by
    intro a ha
    rw [LinearMap.mem_ker] at ha
    have h := congrArg Prod.fst ha
    have h' := congrArg Prod.snd ha
    simp [f, Submodule.Quotient.mk_eq_zero] at h h'
    simp only [Submodule.restrictScalars_mem, Submodule.mem_inf]
    exact ⟨h, h'⟩
  exact Module.Finite.of_injective (((I ⊓ J).restrictScalars R).liftQ f h1)
    (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ h2))

theorem g74r_mem_fd {R A : Type u} [CommRing R] [Ring A] [Algebra R A] [IsNoetherianRing R]
    (f : Module.Dual R A) (hf : f ∈ finiteDual R A) :
    ∃ I : Submodule A A, IsCofiniteLeft R A I ∧ ∀ a ∈ I, f a = 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨⊤, g74r_cof_top, fun a _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨I, hI, hI'⟩ := hx
    obtain ⟨J, hJ, hJ'⟩ := hy
    refine ⟨I ⊓ J, g74r_cof_inf I J hI hJ, fun a ha => ?_⟩
    rw [LinearMap.add_apply, hI' a ha.1, hJ' a ha.2, add_zero]
  | smul r x _ hx =>
    obtain ⟨I, hI, hI'⟩ := hx
    refine ⟨I, hI, fun a ha => ?_⟩
    rw [LinearMap.smul_apply, hI' a ha, smul_zero]

theorem g74r_common {R A : Type u} [CommRing R] [Ring A] [Algebra R A] [IsNoetherianRing R]
    (n : ℕ) (g : Fin n → Module.Dual R A) (hg : ∀ k, g k ∈ finiteDual R A) :
    ∃ I : Submodule A A, IsCofiniteLeft R A I ∧ ∀ k, ∀ a ∈ I, g k a = 0 := by
  induction n with
  | zero => exact ⟨⊤, g74r_cof_top, fun k => k.elim0⟩
  | succ n ih =>
    obtain ⟨I, hI, hI'⟩ := ih (fun k => g k.succ) (fun k => hg _)
    obtain ⟨J, hJ, hJ'⟩ := g74r_mem_fd (g 0) (hg 0)
    refine ⟨I ⊓ J, g74r_cof_inf I J hI hJ, fun k => ?_⟩
    refine Fin.cases ?_ ?_ k
    · exact fun a ha => hJ' a ha.2
    · exact fun k a ha => hI' k a ha.1


theorem g74r_rat_core {R A X : Type u} [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup X] [Module R X] (S : Submodule R (Module.Dual R A))
    (hfin : ∀ (n : ℕ) (g : Fin n → S), ∃ J : Submodule R A,
      Module.Finite R (A ⧸ J) ∧ Module.Projective R (A ⧸ J) ∧
        (∀ φ : Module.Dual R (A ⧸ J), φ.comp J.mkQ ∈ S) ∧
        ∀ k, ∀ a ∈ J, (g k).val a = 0) :
    Function.Injective (pairingAlpha (P := S) S.subtype X) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, x, g, rfl⟩ := g74r_exists_fin (R := R) (M := X) (N := S) z
  obtain ⟨J, hJf, hJp, hmem, hJ⟩ := hfin n g
  let φ : Fin n → Module.Dual R (A ⧸ J) := fun k =>
    J.liftQ (g k).val (fun a ha => hJ k a ha)
  let θ : Module.Dual R (A ⧸ J) →ₗ[R] S :=
    LinearMap.codRestrict S J.mkQ.dualMap (fun ψ => hmem ψ)
  have hθ : ∀ k, θ (φ k) = g k := fun k => Subtype.ext (LinearMap.ext fun a => rfl)
  let w := ∑ k, φ k ⊗ₜ[R] x k
  have hw : dualTensorHom R (A ⧸ J) X w = 0 := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H a =>
      have := LinearMap.congr_fun hz a
      rw [g74r_alpha_sum] at this
      rw [LinearMap.zero_apply] at this ⊢
      rw [map_sum, LinearMap.sum_apply]
      simp only [dualTensorHom_apply]
      exact this
  have hw0 : w = 0 :=
    (dualTensorHom_bijective (R := R) (M := A ⧸ J) (N := X)).1
      (hw.trans (map_zero _).symm)
  have hz' : (∑ k, x k ⊗ₜ[R] g k) =
      TensorProduct.comm R _ X (LinearMap.rTensor X θ w) := by
    simp only [w, map_sum, LinearMap.rTensor_tmul, TensorProduct.comm_tmul, hθ]
  rw [hz', hw0, map_zero, map_zero]

/-- generic annihilator: if I has finite quotient and `mul x` maps preserve finiteness, kernel of
a ↦ ([f i a])_i is cofinite. -/
theorem g74r_ker_fin {R A : Type u} [CommRing R] [Ring A] [Algebra R A] [IsNoetherianRing R]
    (I : Submodule R A) (hf : Module.Finite R (A ⧸ I)) (m : ℕ) (F : Fin m → A →ₗ[R] A)
    (K : Submodule R A) (hK : ∀ a, a ∈ K ↔ ∀ i, F i a ∈ I) : Module.Finite R (A ⧸ K) := by
  let f : A →ₗ[R] (Fin m → A ⧸ I) := LinearMap.pi (fun i => I.mkQ.comp (F i))
  have h1 : K ≤ LinearMap.ker f := by
    intro a ha
    rw [LinearMap.mem_ker]
    funext i
    simp [f, Submodule.Quotient.mk_eq_zero, (hK a).1 ha i]
  have h2 : LinearMap.ker f ≤ K := by
    intro a ha
    rw [LinearMap.mem_ker] at ha
    rw [hK]
    intro i
    have := congrFun ha i
    simpa [f, Submodule.Quotient.mk_eq_zero] using this
  exact Module.Finite.of_injective (K.liftQ f h1)
    (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ h2))

theorem g74r_gens {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
    (I : Submodule R A) (hf : Module.Finite R (A ⧸ I)) :
    ∃ (m : ℕ) (x : Fin m → A), ∀ y : A, ∃ (r : Fin m → R), y - ∑ i, r i • x i ∈ I := by
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := A ⧸ I)
  choose x hx using fun i => Submodule.Quotient.mk_surjective I (s i)
  refine ⟨m, x, fun y => ?_⟩
  have hy : I.mkQ y ∈ Submodule.span R (Set.range s) := by rw [hs]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hy
  obtain ⟨r, hr⟩ := hy
  refine ⟨r, ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
  have : (Submodule.Quotient.mk (∑ i, r i • x i) : A ⧸ I) = ∑ i, r i • s i := by
    rw [← Submodule.mkQ_apply, map_sum]
    simp [hx]
  rw [this, hr, Submodule.mkQ_apply, sub_self]

/-- left ideal I: two-sided cofinite K ≤ I. -/
theorem g74r_annL {R A : Type u} [CommRing R] [Ring A] [Algebra R A] [IsNoetherianRing R]
    (I : Submodule R A) (hI : ∀ b a, a ∈ I → b * a ∈ I) (hf : Module.Finite R (A ⧸ I)) :
    ∃ K : Submodule R A, K ≤ I ∧ Module.Finite R (A ⧸ K) ∧
      (∀ b a, a ∈ K → b * a ∈ K) ∧ (∀ a b, a ∈ K → a * b ∈ K) := by
  obtain ⟨m, x, hx⟩ := g74r_gens I hf
  let K : Submodule R A :=
    { carrier := {a | ∀ y, a * y ∈ I}
      add_mem' := by
        intro a b ha hb y
        rw [add_mul]; exact I.add_mem (ha y) (hb y)
      zero_mem' := by intro y; rw [zero_mul]; exact I.zero_mem
      smul_mem' := by
        intro r a ha y
        rw [smul_mul_assoc]; exact I.smul_mem r (ha y) }
  have hK : ∀ a, a ∈ K ↔ ∀ i, (LinearMap.mulLeft R a) (x i) ∈ I := by
    intro a
    constructor
    · intro ha i; exact ha (x i)
    · intro ha y
      obtain ⟨r, hr⟩ := hx y
      have h1 : a * (y - ∑ i, r i • x i) ∈ I := hI a _ hr
      have h2 : a * (∑ i, r i • x i) ∈ I := by
        rw [Finset.mul_sum]
        refine I.sum_mem fun i _ => ?_
        rw [mul_smul_comm]; exact I.smul_mem _ (ha i)
      have := I.add_mem h1 h2
      rwa [mul_sub, sub_add_cancel] at this
  refine ⟨K, fun a ha => by simpa using ha 1, ?_, ?_, ?_⟩
  · exact g74r_ker_fin I hf m (fun i => LinearMap.mulRight R (x i)) K (fun a => by
      rw [hK a]; rfl)
  · intro b a ha y
    show b * a * y ∈ I
    rw [mul_assoc]; exact hI b _ (ha y)
  · intro a b ha y
    show a * b * y ∈ I
    rw [mul_assoc]; exact ha (b * y)

/-- right ideal I: two-sided cofinite K ≤ I. -/
theorem g74r_annR {R A : Type u} [CommRing R] [Ring A] [Algebra R A] [IsNoetherianRing R]
    (I : Submodule R A) (hI : ∀ a b, a ∈ I → a * b ∈ I) (hf : Module.Finite R (A ⧸ I)) :
    ∃ K : Submodule R A, K ≤ I ∧ Module.Finite R (A ⧸ K) ∧
      (∀ b a, a ∈ K → b * a ∈ K) ∧ (∀ a b, a ∈ K → a * b ∈ K) := by
  obtain ⟨m, x, hx⟩ := g74r_gens I hf
  let K : Submodule R A :=
    { carrier := {a | ∀ y, y * a ∈ I}
      add_mem' := by
        intro a b ha hb y
        rw [mul_add]; exact I.add_mem (ha y) (hb y)
      zero_mem' := by intro y; rw [mul_zero]; exact I.zero_mem
      smul_mem' := by
        intro r a ha y
        rw [mul_smul_comm]; exact I.smul_mem r (ha y) }
  have hK : ∀ a, a ∈ K ↔ ∀ i, (LinearMap.mulLeft R (x i)) a ∈ I := by
    intro a
    constructor
    · intro ha i; exact ha (x i)
    · intro ha y
      obtain ⟨r, hr⟩ := hx y
      have h1 : (y - ∑ i, r i • x i) * a ∈ I := hI _ a hr
      have h2 : (∑ i, r i • x i) * a ∈ I := by
        rw [Finset.sum_mul]
        refine I.sum_mem fun i _ => ?_
        rw [smul_mul_assoc]; exact I.smul_mem _ (ha i)
      have := I.add_mem h1 h2
      rwa [sub_mul, sub_add_cancel] at this
  refine ⟨K, fun a ha => by simpa using ha 1, ?_, ?_, ?_⟩
  · exact g74r_ker_fin I hf m (fun i => LinearMap.mulLeft R (x i)) K hK
  · intro b a ha y
    show y * (b * a) ∈ I
    rw [← mul_assoc]; exact ha (y * b)
  · intro a b ha y
    show y * (a * b) ∈ I
    rw [← mul_assoc]; exact hI _ b (ha y)

/-- two-sided R-submodule as a left ideal. -/
def g74r_toLeft {R A : Type u} [CommRing R] [Ring A] [Algebra R A] (K : Submodule R A)
    (hK : ∀ b a, a ∈ K → b * a ∈ K) : Submodule A A :=
  { carrier := K
    add_mem' := K.add_mem
    zero_mem' := K.zero_mem
    smul_mem' := fun b a ha => hK b a ha }

theorem g74r_toLeft_rs {R A : Type u} [CommRing R] [Ring A] [Algebra R A] (K : Submodule R A)
    (hK : ∀ b a, a ∈ K → b * a ∈ K) : (g74r_toLeft K hK).restrictScalars R = K := by
  ext; rfl

theorem g74r_mem_of_twosided {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
    [IsNoetherianRing R] (J : Submodule R A) (K : Submodule R A) (hKJ : K ≤ J)
    (hKf : Module.Finite R (A ⧸ K)) (hK : ∀ b a, a ∈ K → b * a ∈ K)
    (φ : Module.Dual R (A ⧸ J)) : φ.comp J.mkQ ∈ finiteDual R A := by
  apply Submodule.subset_span
  refine ⟨g74r_toLeft K hK, ?_, ?_⟩
  · unfold IsCofiniteLeft LeftQuotient
    rw [g74r_toLeft_rs]; exact hKf
  · intro a ha
    have : J.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero J).2 (hKJ ha)
    simp [this]

theorem g74r_quot_equiv {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (p : Submodule R N) :
    Nonempty ((M ⧸ p.comap e.toLinearMap) ≃ₗ[R] (N ⧸ p)) :=
  ⟨Submodule.Quotient.equiv _ p e (Submodule.map_comap_eq_of_surjective e.surjective p)⟩

/-- Remark 4.4, PDF p.13: right and two-sided sufficient conditions, separately. -/
theorem solution [IsNoetherianRing R] :
    (PropertyRight R A → IsRationalSystem (R := R) (A := A) (P := finiteDual R A) (finiteDualPairing R A)) ∧
    (PropertyTwoSided R A → IsRationalSystem (R := R) (A := A) (P := finiteDual R A) (finiteDualPairing R A)) := by
  constructor
  · intro h
    unfold IsRationalSystem finiteDualPairing
    intro X _ _
    apply g74r_rat_core
    intro n g
    obtain ⟨I, hI, hI'⟩ := g74r_common n (fun k => (g k).val) (fun k => (g k).2)
    obtain ⟨K, hKI, hKf, hKl, hKr⟩ := g74r_annL (I.restrictScalars R)
      (fun b a ha => I.smul_mem b ha) hI
    let K' : Submodule Aᵐᵒᵖ Aᵐᵒᵖ :=
      { carrier := {x | x.unop ∈ K}
        add_mem' := fun ha hb => K.add_mem ha hb
        zero_mem' := K.zero_mem
        smul_mem' := fun b x hx => by
          show (b * x).unop ∈ K
          rw [MulOpposite.unop_mul]; exact hKr _ _ hx }
    have hK'rs : K'.restrictScalars R =
        K.comap (MulOpposite.opLinearEquiv R (M := A)).symm.toLinearMap := by
      ext x; rfl
    have hK'f : IsCofiniteLeft R Aᵐᵒᵖ K' := by
      unfold IsCofiniteLeft LeftQuotient
      rw [hK'rs]
      obtain ⟨e⟩ := g74r_quot_equiv (MulOpposite.opLinearEquiv R (M := A)).symm K
      exact Module.Finite.equiv e.symm
    obtain ⟨J', hJ'K, hJ'f, hJ'p⟩ := h K' hK'f
    let J : Submodule R A := (J'.restrictScalars R).comap
      (MulOpposite.opLinearEquiv R (M := A)).toLinearMap
    obtain ⟨e⟩ := g74r_quot_equiv (MulOpposite.opLinearEquiv R (M := A)) (J'.restrictScalars R)
    have hJf : Module.Finite R (A ⧸ J) := Module.Finite.equiv e.symm
    have hJr : ∀ a b, a ∈ J → a * b ∈ J := by
      intro a b ha
      show MulOpposite.op (a * b) ∈ J'
      rw [MulOpposite.op_mul]
      exact J'.smul_mem (MulOpposite.op b) ha
    refine ⟨J, hJf, Module.Projective.of_equiv e.symm, ?_, ?_⟩
    · intro φ
      obtain ⟨L, hLJ, hLf, hLl, -⟩ := g74r_annR J hJr hJf
      exact g74r_mem_of_twosided J L hLJ hLf hLl φ
    · intro k a ha
      have h1 : MulOpposite.op a ∈ K' := hJ'K ha
      exact hI' k a (hKI h1)
  · intro h
    unfold IsRationalSystem finiteDualPairing
    intro X _ _
    apply g74r_rat_core
    intro n g
    obtain ⟨I, hI, hI'⟩ := g74r_common n (fun k => (g k).val) (fun k => (g k).2)
    obtain ⟨K, hKI, hKf, hKl, hKr⟩ := g74r_annL (I.restrictScalars R)
      (fun b a ha => I.smul_mem b ha) hI
    have hts : Ideal.IsTwoSided (g74r_toLeft K hKl : Ideal A) := ⟨fun b ha => hKr _ b ha⟩
    have hcof : IsCofiniteLeft R A (g74r_toLeft K hKl) := by
      unfold IsCofiniteLeft LeftQuotient
      rw [g74r_toLeft_rs]; exact hKf
    obtain ⟨J, -, hJK, hJf, hJp⟩ := h _ hts hcof
    refine ⟨J.restrictScalars R, hJf, hJp, ?_, ?_⟩
    · intro φ
      exact g74r_mem_of_twosided _ _ le_rfl hJf (fun b a ha => J.smul_mem b ha) φ
    · intro k a ha
      exact hI' k a (hKI (hJK ha))

end Cofinite

end
