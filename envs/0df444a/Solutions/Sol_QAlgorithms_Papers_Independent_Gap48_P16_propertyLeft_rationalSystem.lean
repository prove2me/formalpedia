-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P16.propertyLeft_rationalSystem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:37:57.904817+00:00
-- url     : https://prove2.me/submissions/aa5e179f-6035-4df3-9499-ec8490f14ed7

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16
noncomputable section

universe u

open QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Cofinite

variable (R A : Type u) [CommRing R] [Ring A] [Algebra R A]

variable {R A}

theorem g74b_exists_fin {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
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

theorem g74b_alpha_sum {R A P M : Type u} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
    (b : P →ₗ[R] A →ₗ[R] R) {n : ℕ} (m : Fin n → M) (p : Fin n → P) (a : A) :
    pairingAlpha b M (∑ i, m i ⊗ₜ[R] p i) a = ∑ i, b (p i) a • m i := by
  rw [map_sum, LinearMap.sum_apply]
  rfl
theorem g74b_cof_top {R A : Type u} [CommRing R] [Ring A] [Algebra R A] :
    IsCofiniteLeft R A ⊤ := by
  unfold IsCofiniteLeft LeftQuotient
  haveI : Subsingleton (A ⧸ (⊤ : Submodule A A).restrictScalars R) :=
    Submodule.Quotient.subsingleton_iff.2 (by simp)
  infer_instance

theorem g74b_cof_inf {R A : Type u} [CommRing R] [Ring A] [Algebra R A] [IsNoetherianRing R]
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

theorem g74b_mem_fd {R A : Type u} [CommRing R] [Ring A] [Algebra R A] [IsNoetherianRing R]
    (f : Module.Dual R A) (hf : f ∈ finiteDual R A) :
    ∃ I : Submodule A A, IsCofiniteLeft R A I ∧ ∀ a ∈ I, f a = 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨⊤, g74b_cof_top, fun a _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨I, hI, hI'⟩ := hx
    obtain ⟨J, hJ, hJ'⟩ := hy
    refine ⟨I ⊓ J, g74b_cof_inf I J hI hJ, fun a ha => ?_⟩
    rw [LinearMap.add_apply, hI' a ha.1, hJ' a ha.2, add_zero]
  | smul r x _ hx =>
    obtain ⟨I, hI, hI'⟩ := hx
    refine ⟨I, hI, fun a ha => ?_⟩
    rw [LinearMap.smul_apply, hI' a ha, smul_zero]

theorem g74b_common {R A : Type u} [CommRing R] [Ring A] [Algebra R A] [IsNoetherianRing R]
    (n : ℕ) (g : Fin n → Module.Dual R A) (hg : ∀ k, g k ∈ finiteDual R A) :
    ∃ I : Submodule A A, IsCofiniteLeft R A I ∧ ∀ k, ∀ a ∈ I, g k a = 0 := by
  induction n with
  | zero => exact ⟨⊤, g74b_cof_top, fun k => k.elim0⟩
  | succ n ih =>
    obtain ⟨I, hI, hI'⟩ := ih (fun k => g k.succ) (fun k => hg _)
    obtain ⟨J, hJ, hJ'⟩ := g74b_mem_fd (g 0) (hg 0)
    refine ⟨I ⊓ J, g74b_cof_inf I J hI hJ, fun k => ?_⟩
    refine Fin.cases ?_ ?_ k
    · exact fun a ha => hJ' a ha.2
    · exact fun k a ha => hI' k a ha.1

theorem g74b_rat_core {R A X : Type u} [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup X] [Module R X] (S : Submodule R (Module.Dual R A))
    (hfin : ∀ (n : ℕ) (g : Fin n → S), ∃ J : Submodule A A,
      Module.Finite R (LeftQuotient R A J) ∧ Module.Projective R (LeftQuotient R A J) ∧
        ∀ k, ∀ a ∈ J, (g k).val a = 0)
    (hmem : ∀ J : Submodule A A, Module.Finite R (LeftQuotient R A J) →
      ∀ φ : Module.Dual R (LeftQuotient R A J), φ.comp (J.restrictScalars R).mkQ ∈ S) :
    Function.Injective (pairingAlpha (P := S) S.subtype X) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, x, g, rfl⟩ := g74b_exists_fin (R := R) (M := X) (N := S) z
  obtain ⟨J, hJf, hJp, hJ⟩ := hfin n g
  let φ : Fin n → Module.Dual R (LeftQuotient R A J) := fun k =>
    (J.restrictScalars R).liftQ (g k).val (fun a ha => hJ k a ha)
  let θ : Module.Dual R (LeftQuotient R A J) →ₗ[R] S :=
    LinearMap.codRestrict S (J.restrictScalars R).mkQ.dualMap (fun ψ => hmem J hJf ψ)
  have hθ : ∀ k, θ (φ k) = g k := fun k => Subtype.ext (LinearMap.ext fun a => rfl)
  let w := ∑ k, φ k ⊗ₜ[R] x k
  have hw : dualTensorHom R (LeftQuotient R A J) X w = 0 := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H a =>
      have := LinearMap.congr_fun hz a
      rw [g74b_alpha_sum] at this
      rw [LinearMap.zero_apply] at this ⊢
      rw [map_sum, LinearMap.sum_apply]
      simp only [dualTensorHom_apply]
      exact this
  have hw0 : w = 0 :=
    (dualTensorHom_bijective (R := R) (M := LeftQuotient R A J) (N := X)).1
      (hw.trans (map_zero _).symm)
  have hz' : (∑ k, x k ⊗ₜ[R] g k) =
      TensorProduct.comm R _ X (LinearMap.rTensor X θ w) := by
    simp only [w, map_sum, LinearMap.rTensor_tmul, TensorProduct.comm_tmul, hθ]
  rw [hz', hw0, map_zero, map_zero]

/-- Proposition 4.2, PDF p.12: property P-left makes the evaluation system rational. -/
theorem solution [IsNoetherianRing R] (h : PropertyLeft R A) :
    IsRationalSystem (R := R) (A := A) (P := finiteDual R A) (finiteDualPairing R A) := by
  unfold IsRationalSystem finiteDualPairing
  intro X _ _
  have hfin : ∀ (n : ℕ) (g : Fin n → finiteDual R A), ∃ J : Submodule A A,
      Module.Finite R (LeftQuotient R A J) ∧ Module.Projective R (LeftQuotient R A J) ∧
        ∀ k, ∀ a ∈ J, (g k).val a = 0 := by
    intro n g
    obtain ⟨I, hI, hI'⟩ := g74b_common n (fun k => (g k).val) (fun k => (g k).2)
    obtain ⟨J, hJI, hJf, hJp⟩ := h I hI
    exact ⟨J, hJf, hJp, fun k a ha => hI' k a (hJI ha)⟩
  have hmem : ∀ J : Submodule A A, Module.Finite R (LeftQuotient R A J) →
      ∀ φ : Module.Dual R (LeftQuotient R A J), φ.comp (J.restrictScalars R).mkQ ∈ finiteDual R A :=
    fun J hJ φ => (cofiniteDualElement R A ⟨J, hJ⟩ φ).2
  generalize finiteDual R A = S at hfin hmem ⊢
  apply g74b_rat_core S hfin hmem


end Cofinite



end
