-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P16.propertyLeft_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:41:39.238223+00:00
-- url     : https://prove2.me/submissions/8f49236e-5ad7-4504-8dd8-652e880966ea

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16
noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

variable {R A B : Type u} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-- Pullback of a left ideal. -/
def S170E_comap (f : A →ₐ[R] B) (K : Submodule B B) : Submodule A A where
  carrier := {a | f a ∈ K}
  add_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq, map_add] at *; exact K.add_mem ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
    exact K.smul_mem (f c) ha

lemma S170E_comap_finite [IsNoetherianRing R] (f : A →ₐ[R] B) (K : Submodule B B)
    (hK : IsCofiniteLeft R B K) : IsCofiniteLeft R A (S170E_comap f K) := by
  unfold IsCofiniteLeft at *
  let g : A →ₗ[R] LeftQuotient R B K := (K.restrictScalars R).mkQ ∘ₗ f.toLinearMap
  have hle : (S170E_comap f K).restrictScalars R ≤ LinearMap.ker g := by
    intro a ha
    simp only [LinearMap.mem_ker, g, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ha
  let h := ((S170E_comap f K).restrictScalars R).liftQ g hle
  have hinj : Function.Injective h := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot']
    ext a
    simp only [LinearMap.mem_ker, g, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem]
    rfl
  haveI : IsNoetherian R (LeftQuotient R B K) := isNoetherian_of_isNoetherianRing_of_finite R _
  exact Module.Finite.of_injective h hinj

lemma S170E_split (f : A →ₐ[R] B) (hB : IsFiniteProjectiveRightExtension f) :
    ∃ (n : ℕ) (s : B → Fin n → A) (p : (Fin n → A) → B),
      (∀ b, p (s b) = b) ∧ (∀ b b', s (b + b') = s b + s b') ∧
      (∀ b a, s (b * f a) = fun k => s b k * a) ∧
      (∀ x y, p (x + y) = p x + p y) ∧ (∀ x a, p (fun k => x k * a) = p x * f a) := by
  letI : Module Aᵐᵒᵖ Bᵐᵒᵖ := Module.compHom Bᵐᵒᵖ f.op.toRingHom
  obtain ⟨hfin, hproj⟩ := hB
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' Aᵐᵒᵖ Bᵐᵒᵖ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hsm : ∀ (a : A) (b : B), (MulOpposite.op a • MulOpposite.op b : Bᵐᵒᵖ) = MulOpposite.op (b * f a) := by
    intro a b; rfl
  refine ⟨n, fun b k => MulOpposite.unop (σ (MulOpposite.op b) k),
    fun x => MulOpposite.unop (π (fun k => MulOpposite.op (x k))), ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    have := LinearMap.congr_fun hσ (MulOpposite.op b)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply] at this
    simp only [MulOpposite.op_unop]
    rw [show (fun k => σ (MulOpposite.op b) k) = σ (MulOpposite.op b) from rfl, this]
    rfl
  · intro b b'
    funext k
    simp [MulOpposite.op_add]
  · intro b a
    funext k
    beta_reduce
    rw [← hsm, map_smul]
    rfl
  · intro x y
    beta_reduce
    rw [show (fun k => MulOpposite.op ((x + y) k)) =
      (fun k => MulOpposite.op (x k)) + (fun k => MulOpposite.op (y k)) by funext k; simp, map_add]
    rfl
  · intro x a
    beta_reduce
    rw [show (fun k => MulOpposite.op (x k * a)) =
      MulOpposite.op a • (fun k => MulOpposite.op (x k)) by funext k; rfl, map_smul]
    rfl

end QAlgorithms.Papers.Independent.Gap48.P16

open QAlgorithms.Papers.Independent.Gap48.P16

variable {R A B : Type u} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

theorem solution [IsNoetherianRing R] (hA : PropertyLeft R A)
    (f : A →ₐ[R] B) (hf : Function.Injective f) (hB : IsFiniteProjectiveRightExtension f) :
    PropertyLeft R B := by
  intro K hK
  obtain ⟨J, hJI, hJfin, hJproj⟩ := hA _ (S170E_comap_finite f K hK)
  obtain ⟨n, s, p, hps, hsadd, hsmul, hpadd, hpmul⟩ := S170E_split f hB
  have hr : ∀ (r : R) (b : B), r • b = b * f (algebraMap R A r) := by
    intro r b; rw [Algebra.smul_def, Algebra.commutes, f.commutes]
  have hrA : ∀ (r : R) (a : A), a * algebraMap R A r = r • a := by
    intro r a; rw [Algebra.smul_def, Algebra.commutes]
  let S : B →ₗ[R] (Fin n → A) :=
    { toFun := s
      map_add' := hsadd
      map_smul' := by
        intro r b
        simp only [RingHom.id_apply]
        rw [hr, hsmul]; funext k; simp [hrA] }
  let P : (Fin n → A) →ₗ[R] B :=
    { toFun := p
      map_add' := hpadd
      map_smul' := by
        intro r x
        simp only [RingHom.id_apply]
        rw [hr, ← hpmul]; congr 1; funext k; simp [hrA] }
  let K' : Submodule B B := Submodule.span B (f '' (J : Set A))
  refine ⟨K', ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    exact hJI hj
  have hs0 : s 0 = 0 := by
    have := hsadd 0 0; simp only [add_zero] at this
    exact left_eq_add.mp this
  have hsK : ∀ x ∈ K', ∀ c : B, ∀ k, s (c * x) k ∈ J := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro c k
      rw [hsmul]
      exact J.smul_mem _ hj
    | zero => intro c k; rw [mul_zero, hs0]; exact J.zero_mem
    | add x y _ _ hx hy =>
      intro c k; rw [mul_add, hsadd]; exact J.add_mem (hx c k) (hy c k)
    | smul c' x _ hx =>
      intro c k; rw [smul_eq_mul, ← mul_assoc]; exact hx _ k
  let iq : LeftQuotient R B K' →ₗ[R] (Fin n → LeftQuotient R A J) :=
    (K'.restrictScalars R).liftQ
      (LinearMap.pi fun k => (J.restrictScalars R).mkQ ∘ₗ LinearMap.proj k ∘ₗ S) (by
        intro x hx
        simp only [LinearMap.mem_ker]
        funext k
        simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
          Function.eval, Submodule.mkQ_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
        have := hsK x hx 1 k
        rw [one_mul] at this
        exact this)
  let qk : Fin n → (LeftQuotient R A J →ₗ[R] LeftQuotient R B K') := fun k =>
    (J.restrictScalars R).liftQ ((K'.restrictScalars R).mkQ ∘ₗ P ∘ₗ LinearMap.single R (fun _ => A) k) (by
      intro j hj
      rw [LinearMap.mem_ker]
      show Submodule.Quotient.mk (p (Pi.single k j)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      have e : (Pi.single k j : Fin n → A) = fun l => (Pi.single k 1 : Fin n → A) l * j := by
        funext l; by_cases hl : l = k
        · subst hl; simp
        · simp [Pi.single_apply, hl]
      show p (Pi.single k j) ∈ K'
      rw [e, hpmul]
      exact K'.smul_mem _ (Submodule.subset_span ⟨j, hj, rfl⟩))
  let pq : (Fin n → LeftQuotient R A J) →ₗ[R] LeftQuotient R B K' :=
    ∑ k, qk k ∘ₗ LinearMap.proj k
  have H : pq ∘ₗ iq = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext b
    simp only [pq, iq, qk, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.liftQ_apply,  LinearMap.sum_apply, LinearMap.coe_proj, Function.eval,
      LinearMap.pi_apply, LinearMap.id_apply]
    change ∑ d, (K'.restrictScalars R).mkQ (P (LinearMap.single R (fun _ => A) d (S b d))) =
      (K'.restrictScalars R).mkQ b
    rw [← map_sum, ← map_sum]
    congr 1
    show p (∑ k, Pi.single k (s b k)) = b
    rw [Finset.univ_sum_single, hps]
  haveI : Module.Projective R (Fin n → LeftQuotient R A J) :=
    Module.Projective.of_equiv' (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun _ : Fin n => LeftQuotient R A J))
  haveI : Module.Projective R (LeftQuotient R B K') := Module.Projective.of_split iq pq H
  refine ⟨?_, inferInstance⟩
  exact Module.Finite.of_surjective pq (fun y => ⟨iq y, by rw [← LinearMap.comp_apply, H]; rfl⟩)
