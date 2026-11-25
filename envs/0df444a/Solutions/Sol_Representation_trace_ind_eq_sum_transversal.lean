-- Prove2me | solution 1 for Representation.trace_ind_eq_sum_transversal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T17:09:57.240631+00:00
-- url     : https://prove2.me/submissions/0996e2de-89fe-4a4a-93ad-e3a161ab534c

import Mathlib

set_option autoImplicit false

universe u v w

open scoped Classical

namespace SW1124FrobInd

open Representation


variable {k : Type u} {G : Type v} {V : Type w} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  (H : Subgroup G) (ρ : Representation k H V)

theorem trace_pi_eq_sum {ι : Type*} [Fintype ι] [Module.Free k V] [Module.Finite k V]
    (T : Module.End k (ι → V)) :
    LinearMap.trace k (ι → V) T =
      ∑ i, LinearMap.trace k V (LinearMap.proj i ∘ₗ T ∘ₗ LinearMap.single k (fun _ : ι => V) i) := by
  let b := Module.Free.chooseBasis k V
  rw [LinearMap.trace_eq_matrix_trace k (Pi.basis fun _ : ι => b), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.trace_eq_matrix_trace k b, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr]

theorem mem_of (t : G ⧸ H → G) (ht : ∀ c : G ⧸ H, ((t c : G) : G ⧸ H) = c) (c : G ⧸ H) (x : G)
    (hx : ((x : G) : G ⧸ H) = c) : (t c)⁻¹ * x ∈ H := by
  rw [← ht c] at hx
  exact QuotientGroup.eq.mp hx.symm

/-- the image of the generator `⟦x ⊗ a⟧` in the transversal model -/
noncomputable def aux (t : G ⧸ H → G) (ht : ∀ c : G ⧸ H, ((t c : G) : G ⧸ H) = c) (x : G) :
    V →ₗ[k] (G ⧸ H → V) :=
  LinearMap.pi fun d =>
    if h : ((x⁻¹ : G) : G ⧸ H) = d then ρ ⟨(t d)⁻¹ * x⁻¹, mem_of H t ht d x⁻¹ h⟩ else 0

variable (t : G ⧸ H → G) (ht : ∀ c : G ⧸ H, ((t c : G) : G ⧸ H) = c)

theorem aux_apply (x : G) (a : V) (d : G ⧸ H) :
    aux H ρ t ht x a d =
      if h : ((x⁻¹ : G) : G ⧸ H) = d then ρ ⟨(t d)⁻¹ * x⁻¹, mem_of H t ht d x⁻¹ h⟩ a else 0 := by
  unfold aux
  rw [LinearMap.pi_apply]
  split_ifs <;> rfl

@[simp]
theorem aux_mul (s : H) (x : G) (a : V) :
    aux H ρ t ht ((s : G) * x) (ρ s a) = aux H ρ t ht x a := by
  funext d
  rw [aux_apply, aux_apply]
  have hc : (((((s : G) * x)⁻¹ : G)) : G ⧸ H) = ((x⁻¹ : G) : G ⧸ H) := by
    rw [mul_inv_rev, QuotientGroup.mk_mul_of_mem _ (H.inv_mem s.2)]
  by_cases h : ((x⁻¹ : G) : G ⧸ H) = d
  · rw [dif_pos (hc.trans h), dif_pos h, ← Module.End.mul_apply, ← map_mul]
    congr 2
    apply Subtype.ext
    simp [mul_assoc]
  · rw [dif_neg (by rwa [hc]), dif_neg h]

/-- `IndV → (G ⧸ H → V)`, `⟦x ⊗ a⟧ ↦ (x⁻¹H ↦ ρ((t c)⁻¹ x⁻¹) a)` -/
noncomputable def psi : IndV H.subtype ρ →ₗ[k] (G ⧸ H → V) :=
  Coinvariants.lift _ (TensorProduct.lift <| (Finsupp.linearCombination k fun x => aux H ρ t ht x) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) fun _ => by ext; simp

theorem psi_mk (x : G) (a : V) : psi H ρ t ht (IndV.mk H.subtype ρ x a) = aux H ρ t ht x a := by
  simp [psi]

noncomputable def phi [Fintype (G ⧸ H)] : (G ⧸ H → V) →ₗ[k] IndV H.subtype ρ :=
  ∑ c : G ⧸ H, IndV.mk H.subtype ρ (t c)⁻¹ ∘ₗ LinearMap.proj c

theorem phi_apply [Fintype (G ⧸ H)] (F : G ⧸ H → V) :
    phi H ρ t F = ∑ c : G ⧸ H, IndV.mk H.subtype ρ (t c)⁻¹ (F c) := by
  simp [phi]

theorem mk_rel (s : H) (y : G) (a : V) :
    IndV.mk H.subtype ρ ((s : G) * y) (ρ s a) = IndV.mk H.subtype ρ y a := by
  have := Coinvariants.mk_self_apply (Representation.tprod ((leftRegular k G).comp H.subtype) ρ) s
    (MonoidAlgebra.single y (1 : k) ⊗ₜ[k] a)
  simpa using this

theorem psi_phi [Fintype (G ⧸ H)] : psi H ρ t ht ∘ₗ phi H ρ t = LinearMap.id := by
  apply LinearMap.ext
  intro F
  funext d
  rw [LinearMap.comp_apply, phi_apply, map_sum, Finset.sum_apply, Finset.sum_eq_single d]
  · rw [psi_mk, aux_apply, dif_pos (by rw [inv_inv, ht])]
    have e : (⟨(t d)⁻¹ * (t d)⁻¹⁻¹, mem_of H t ht d _ (by rw [inv_inv, ht])⟩ : H) = 1 :=
      Subtype.ext (by simp)
    rw [e, map_one]
    rfl
  · intro c _ hc
    rw [psi_mk, aux_apply, dif_neg (by rw [inv_inv, ht]; exact hc)]
  · simp

theorem phi_psi [Fintype (G ⧸ H)] : phi H ρ t ∘ₗ psi H ρ t ht = LinearMap.id := by
  apply IndV.hom_ext
  intro x
  apply LinearMap.ext
  intro a
  show phi H ρ t (psi H ρ t ht (IndV.mk H.subtype ρ x a)) = IndV.mk H.subtype ρ x a
  rw [psi_mk, phi_apply, Finset.sum_eq_single ((x⁻¹ : G) : G ⧸ H)]
  · rw [aux_apply, dif_pos rfl]
    have e : (t ((x⁻¹ : G) : G ⧸ H))⁻¹ =
        ((⟨(t ((x⁻¹ : G) : G ⧸ H))⁻¹ * x⁻¹, mem_of H t ht _ x⁻¹ rfl⟩ : H) : G) * x := by
      simp
    exact (congrArg (fun y => IndV.mk H.subtype ρ y
      (ρ ⟨(t ((x⁻¹ : G) : G ⧸ H))⁻¹ * x⁻¹, mem_of H t ht _ x⁻¹ rfl⟩ a)) e).trans (mk_rel H ρ _ x a)
  · intro d _ hd
    rw [aux_apply, dif_neg (Ne.symm hd), map_zero]
  · simp

include ht in
theorem elt_mem (g : G) (c : G ⧸ H) : (t c)⁻¹ * (g * t (g⁻¹ • c)) ∈ H :=
  mem_of H t ht c _ (by rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, ht, smul_inv_smul])

/-- the transversal model of `Ind(g)`: `(T g F) c = ρ((t c)⁻¹ g t(g⁻¹ c)) (F (g⁻¹ c))` -/
noncomputable def T (g : G) : Module.End k (G ⧸ H → V) :=
  LinearMap.pi fun c => ρ ⟨(t c)⁻¹ * (g * t (g⁻¹ • c)), elt_mem H t ht g c⟩ ∘ₗ LinearMap.proj (g⁻¹ • c)

theorem T_apply (g : G) (F : G ⧸ H → V) (c : G ⧸ H) :
    T H ρ t ht g F c = ρ ⟨(t c)⁻¹ * (g * t (g⁻¹ • c)), elt_mem H t ht g c⟩ (F (g⁻¹ • c)) := rfl

theorem psi_ind (g : G) :
    psi H ρ t ht ∘ₗ ind H.subtype ρ g = T H ρ t ht g ∘ₗ psi H ρ t ht := by
  apply IndV.hom_ext
  intro x
  apply LinearMap.ext
  intro a
  funext d
  show psi H ρ t ht (ind H.subtype ρ g (IndV.mk H.subtype ρ x a)) d =
    T H ρ t ht g (psi H ρ t ht (IndV.mk H.subtype ρ x a)) d
  rw [ind_mk, psi_mk, psi_mk, T_apply, aux_apply, aux_apply]
  have hc : (((x * g⁻¹)⁻¹ : G) : G ⧸ H) = d ↔ ((x⁻¹ : G) : G ⧸ H) = g⁻¹ • d := by
    rw [mul_inv_rev, inv_inv, ← smul_eq_mul, ← MulAction.Quotient.smul_mk, eq_inv_smul_iff]
  by_cases h : ((x⁻¹ : G) : G ⧸ H) = g⁻¹ • d
  · rw [dif_pos (hc.2 h), dif_pos h, ← Module.End.mul_apply, ← map_mul]
    congr 2
    apply Subtype.ext
    simp [mul_assoc]
  · rw [dif_neg (mt hc.1 h), dif_neg h, map_zero]

theorem trace_T [Fintype (G ⧸ H)] [Module.Free k V] [Module.Finite k V] (g : G) :
    LinearMap.trace k (G ⧸ H → V) (T H ρ t ht g) =
      ∑ c : G ⧸ H,
        if h : (t c)⁻¹ * g * t c ∈ H then LinearMap.trace k V (ρ ⟨(t c)⁻¹ * g * t c, h⟩) else 0 := by
  rw [trace_pi_eq_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : g⁻¹ • c = c
  · have hm : (t c)⁻¹ * g * t c ∈ H := by
      rw [mul_assoc]
      exact mem_of H t ht c _ (by
        rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, ht]
        exact (inv_smul_eq_iff.mp hc).symm)
    rw [dif_pos hm]
    have e : (⟨(t c)⁻¹ * (g * t (g⁻¹ • c)), elt_mem H t ht g c⟩ : H) = ⟨(t c)⁻¹ * g * t c, hm⟩ :=
      Subtype.ext (by simp [hc, mul_assoc])
    congr 1
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.coe_proj, Function.eval, T_apply]
    rw [e, hc, LinearMap.single_apply]
    simp
  · have hm : (t c)⁻¹ * g * t c ∉ H := by
      intro hm
      apply hc
      have e : ((t c : G) : G ⧸ H) = ((g * t c : G) : G ⧸ H) :=
        QuotientGroup.eq.mpr (by rwa [← mul_assoc])
      rw [ht, ← smul_eq_mul, ← MulAction.Quotient.smul_mk, ht] at e
      rw [inv_smul_eq_iff]
      exact e
    rw [dif_neg hm]
    convert map_zero (LinearMap.trace k V) using 2
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.coe_proj, Function.eval, T_apply, LinearMap.zero_apply]
    rw [LinearMap.single_apply]
    simp [hc]

end SW1124FrobInd

theorem solution {k : Type u} {G : Type v} {V : Type w}
    [CommRing k] [Group G] [AddCommGroup V] [Module k V] [Module.Free k V] [Module.Finite k V]
    (H : Subgroup G) [Fintype (G ⧸ H)] (ρ : Representation k H V)
    (t : G ⧸ H → G) (ht : ∀ c : G ⧸ H, ((t c : G) : G ⧸ H) = c) :
    Module.Free k (Representation.IndV H.subtype ρ) ∧
      Module.Finite k (Representation.IndV H.subtype ρ) ∧
      ∀ g : G,
        LinearMap.trace k (Representation.IndV H.subtype ρ) (Representation.ind H.subtype ρ g) =
          ∑ c : G ⧸ H,
            if h : (t c)⁻¹ * g * t c ∈ H then LinearMap.trace k V (ρ ⟨(t c)⁻¹ * g * t c, h⟩)
            else 0 := by
  let E : Representation.IndV H.subtype ρ ≃ₗ[k] (G ⧸ H → V) :=
    LinearEquiv.ofLinear (SW1124FrobInd.psi H ρ t ht) (SW1124FrobInd.phi H ρ t)
      (SW1124FrobInd.psi_phi H ρ t ht) (SW1124FrobInd.phi_psi H ρ t ht)
  have : Module.Free k (Representation.IndV H.subtype ρ) := Module.Free.of_equiv E.symm
  have : Module.Finite k (Representation.IndV H.subtype ρ) := Module.Finite.equiv E.symm
  refine ⟨inferInstance, inferInstance, fun g => ?_⟩
  have hconj : Representation.ind H.subtype ρ g = E.symm.conj (SW1124FrobInd.T H ρ t ht g) := by
    apply LinearMap.ext
    intro x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm]
    apply E.injective
    rw [LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun (SW1124FrobInd.psi_ind H ρ t ht g) x
  rw [hconj, LinearMap.trace_conj']
  convert SW1124FrobInd.trace_T H ρ t ht g
