-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P16.mockProjective_purity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:17:45.929439+00:00
-- url     : https://prove2.me/submissions/f3a6f6f5-5633-4895-8a03-15cf2076f33b

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16
noncomputable section

universe u

open QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Pairings

variable {R A P Q B M : Type u} [CommRing R]

variable [AddCommGroup A] [Module R A] [AddCommGroup P] [Module R P]

variable [AddCommGroup Q] [Module R Q] [AddCommGroup B] [Module R B]

variable [AddCommGroup M] [Module R M]

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
/-- canonical map (A → R) ⊗ M → (A → M). -/
def g74b_phi (R A M : Type u) [CommRing R] [AddCommGroup M] [Module R M] :
    (A → R) ⊗[R] M →ₗ[R] (A → M) :=
  TensorProduct.lift (LinearMap.mk₂ R (fun (g : A → R) (m : M) => fun x => g x • m)
    (fun g g' m => by funext x; simp [add_smul])
    (fun r g m => by funext x; simp [mul_smul])
    (fun g m m' => by funext x; simp [smul_add])
    (fun r g m => by funext x; simp [smul_comm r (g x) m]))

theorem g74b_phi_ev {R A P M : Type u} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
    (b : P →ₗ[R] A →ₗ[R] R) (y : P ⊗[R] M) :
    g74b_phi R A M (TensorProduct.map (evaluationEmbedding b) LinearMap.id y) =
      fun x => pairingAlpha b M (TensorProduct.comm R P M y) x := by
  induction y using TensorProduct.induction_on with
  | zero => funext x; simp
  | tmul p m => funext x; rfl
  | add y y' hy hy' =>
    funext x
    rw [map_add, map_add, hy, hy', map_add, map_add]
    rfl

theorem g74b_core {R A P M : Type u} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
    (b : P →ₗ[R] A →ₗ[R] R)
    (hrec : ∀ (n : ℕ) (p : Fin n → P), ∃ (m : ℕ) (a : Fin m → A)
      (g : Fin m → A → R), ∀ i x, b (p i) x = ∑ l, b (p i) (a l) * g l x) :
    IsTensorInjective (evaluationEmbedding b) M ↔ Function.Injective (pairingAlpha b M) := by
  unfold IsTensorInjective
  constructor
  · intro hT
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨n, m, p, rfl⟩ := g74b_exists_fin x
    obtain ⟨k, a, g, hg⟩ := hrec n p
    have hev : ∀ i, evaluationEmbedding b (p i) = ∑ l, b (p i) (a l) • g l := by
      intro i; funext x
      simp only [evaluationEmbedding, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.ltoFun_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact hg i x
    have hal : ∀ l, ∑ i, b (p i) (a l) • m i = 0 := by
      intro l
      rw [← g74b_alpha_sum, hx, LinearMap.zero_apply]
    have hz : TensorProduct.map (evaluationEmbedding b) LinearMap.id
        (TensorProduct.comm R M P (∑ i, m i ⊗ₜ[R] p i)) = 0 := by
      simp only [map_sum, TensorProduct.comm_tmul, TensorProduct.map_tmul, LinearMap.id_coe,
        id_eq, hev, TensorProduct.sum_tmul, TensorProduct.smul_tmul]
      rw [Finset.sum_comm]
      simp only [← TensorProduct.tmul_sum, hal, TensorProduct.tmul_zero, Finset.sum_const_zero]
    have := (injective_iff_map_eq_zero _).1 hT _ hz
    exact (LinearEquiv.map_eq_zero_iff (TensorProduct.comm R M P)).1 this
  · intro hA
    rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 := g74b_phi_ev b y
    rw [hy, map_zero] at h1
    have h2 : pairingAlpha b M (TensorProduct.comm R P M y) = 0 := by
      ext x; exact (congrFun h1 x).symm
    have := (injective_iff_map_eq_zero _).1 hA _ h2
    simpa using this

/-- Proposition 2.7, PDF p.5: fixed-module and universal purity criteria. -/
theorem solution (b : P →ₗ[R] A →ₗ[R] R) (h : IsMockProjective b) :
    (IsTensorInjective (evaluationEmbedding b) M ↔ Function.Injective (pairingAlpha b M)) ∧
      (IsRationalSystem b ↔ IsPureMap (evaluationEmbedding b)) := by
  have hrec := h.2
  refine ⟨g74b_core b hrec, ?_⟩
  constructor
  · intro hR
    refine ⟨?_, fun X _ _ => (g74b_core b hrec).2 (hR X)⟩
    intro p p' hp
    have hb : b p = b p' := by
      ext x
      exact congrFun hp x
    have h1 : pairingAlpha b R ((1 : R) ⊗ₜ[R] p) = pairingAlpha b R ((1 : R) ⊗ₜ[R] p') := by
      ext x
      change b p x • (1 : R) = b p' x • (1 : R)
      rw [hb]
    have h2 := h.1 h1
    have := congrArg (TensorProduct.lid R P) h2
    simpa using this
  · intro hP X _ _
    exact (g74b_core b hrec).1 (hP.2 X)


end Pairings



end
