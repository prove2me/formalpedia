-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P16.noetherian_purity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:07:34.532354+00:00
-- url     : https://prove2.me/submissions/85f118a3-3a00-4622-825a-5d11151dbade

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
theorem g74b_reconstruct {R : Type u} [CommRing R] [IsNoetherianRing R]
    (S : Type u) (n : ℕ) (f : Fin n → S → R) :
    ∃ (m : ℕ) (s : Fin m → S) (g : Fin m → S → R),
      ∀ i x, f i x = ∑ l, f i (s l) * g l x := by
  classical
  let v : S → (Fin n → R) := fun x i => f i x
  obtain ⟨t, ht, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (R := R)
    (Set.range v)).1 (IsNoetherian.noetherian _)
  have hex : ∀ y : (t : Set (Fin n → R)), ∃ x, v x = y := fun y => ht y.2
  choose s0 hs0 using hex
  let e := t.equivFin
  let s : Fin t.card → S := fun l => s0 ⟨(e.symm l).1, (e.symm l).2⟩
  have hle : Submodule.span R (t : Set (Fin n → R)) ≤
      Submodule.span R (Set.range fun l => v (s l)) := by
    rw [Submodule.span_le]
    intro y hy
    apply Submodule.subset_span
    refine ⟨e ⟨y, hy⟩, ?_⟩
    simp only [s, Equiv.symm_apply_apply]
    exact hs0 ⟨y, hy⟩
  have hx : ∀ x, v x ∈ Submodule.span R (Set.range fun l => v (s l)) := fun x =>
    hle (hspan ▸ Submodule.subset_span ⟨x, rfl⟩)
  have hx' := fun x => (Submodule.mem_span_range_iff_exists_fun R).1 (hx x)
  choose c hc using hx'
  refine ⟨t.card, s, fun l x => c x l, ?_⟩
  intro i x
  have := congrFun (hc x) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v] at this
  rw [← this]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _
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

/-- Remark 2.14, PDF p.8: no mock-projectivity hypothesis over a noetherian base. -/
theorem solution [IsNoetherianRing R] (b : P →ₗ[R] A →ₗ[R] R)
    (h : Function.Injective (pairingAlpha b R)) :
    IsTensorInjective (evaluationEmbedding b) M ↔ Function.Injective (pairingAlpha b M) := by
  exact g74b_core b (fun n p => g74b_reconstruct A n (fun i x => b (p i) x))


end Pairings



end
