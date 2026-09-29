-- Prove2me | solution 1 for Rep.exists_ker_trace_cyclicShift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a2d53f35-3c91-529b-948b-e198d6f51fcf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_ker_trace_cyclicShift

set_option autoImplicit false

universe u

open CategoryTheory

set_option maxHeartbeats 3200000 in
theorem solution {k G : Type u} [CommRing k] [Group G]
    (U : Subgroup G) [U.Normal] [U.FiniteIndex] (φ : G) (hφ : ∀ g : G, ∃ (n : ℤ) (u : G), u ∈ U ∧ g = φ ^ n * u)
    (X : Rep.{u} k G)
    (ι : X ⟶ Rep.coind U.subtype (Rep.res U.subtype X)) (τ : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ X)
    (hι : ∀ (x : X) (g : G), ((ι.hom x : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = X.ρ g x)
    (hτ : ∀ f : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom f = ∑ᶠ c : G ⧸ U, X.ρ c.out ((f : G → X) (c.out)⁻¹)) :
    ∃ (K : Rep.{u} k G) (i : K ⟶ Rep.coind U.subtype (Rep.res U.subtype X)) (E : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ K),
      Function.Injective i.hom ∧
      (∀ f : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom f = 0 ↔ ∃ κ : K, i.hom κ = f) ∧
      (∀ (f : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G),
        ((i.hom (E.hom f) : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = X.ρ φ ((f : G → X) (φ⁻¹ * g)) - (f : G → X) g) ∧
      Function.Injective ι.hom ∧ Function.Surjective E.hom ∧
      (∀ f : Rep.coind U.subtype (Rep.res U.subtype X), E.hom f = 0 ↔ ∃ x : X, ι.hom x = f) := by
  classical
  haveI : Finite (G ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (G ⧸ U) := Fintype.ofFinite _
  have memY : ∀ (f : (Rep.coind U.subtype (Rep.res U.subtype X))) (u : U) (g : G), (f : G → X) ((u : G) * g) = X.ρ (u : G) ((f : G → X) g) :=
    fun f u g => f.2 u g
  have actY : ∀ (h : G) (f : (Rep.coind U.subtype (Rep.res U.subtype X))) (g : G), (((Rep.coind U.subtype (Rep.res U.subtype X)).ρ h f : (Rep.coind U.subtype (Rep.res U.subtype X))) : G → X) g = (f : G → X) (g * h) := fun _ _ _ => rfl
  have hconj : ∀ u : G, u ∈ U → φ⁻¹ * u * φ ∈ U := fun u hu => by
    simpa using Subgroup.Normal.conj_mem ‹U.Normal› u hu φ⁻¹

  let Tfun : (Rep.coind U.subtype (Rep.res U.subtype X)) → (Rep.coind U.subtype (Rep.res U.subtype X)) := fun f => ⟨fun g => X.ρ φ ((f : G → X) (φ⁻¹ * g)), fun u g => by
      show X.ρ φ ((f : G → X) (φ⁻¹ * ((u : G) * g))) = X.ρ (u : G) (X.ρ φ ((f : G → X) (φ⁻¹ * g)))
      have h1 : φ⁻¹ * ((u : G) * g) = (φ⁻¹ * (u : G) * φ) * (φ⁻¹ * g) := by group
      rw [h1, memY f ⟨φ⁻¹ * (u : G) * φ, hconj _ u.2⟩ (φ⁻¹ * g)]
      show X.ρ φ (X.ρ (φ⁻¹ * (u : G) * φ) _) = _
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2; group⟩
  have hTfun : ∀ (f : (Rep.coind U.subtype (Rep.res U.subtype X))) (g : G), ((Tfun f : (Rep.coind U.subtype (Rep.res U.subtype X))) : G → X) g = X.ρ φ ((f : G → X) (φ⁻¹ * g)) := fun _ _ => rfl
  let T : (Rep.coind U.subtype (Rep.res U.subtype X)) →ₗ[k] (Rep.coind U.subtype (Rep.res U.subtype X)) :=
    { toFun := Tfun
      map_add' := fun f f' => by
        apply Subtype.ext; funext g
        show X.ρ φ ((f : G → X) (φ⁻¹ * g) + (f' : G → X) (φ⁻¹ * g)) = X.ρ φ _ + X.ρ φ _
        rw [map_add]
      map_smul' := fun c f => by
        apply Subtype.ext; funext g
        show X.ρ φ (c • (f : G → X) (φ⁻¹ * g)) = c • X.ρ φ _
        rw [map_smul] }
  have hT : ∀ (f : (Rep.coind U.subtype (Rep.res U.subtype X))) (g : G), ((T f : (Rep.coind U.subtype (Rep.res U.subtype X))) : G → X) g = X.ρ φ ((f : G → X) (φ⁻¹ * g)) := fun _ _ => rfl
  have hTequiv : ∀ (h : G) (f : (Rep.coind U.subtype (Rep.res U.subtype X))), T ((Rep.coind U.subtype (Rep.res U.subtype X)).ρ h f) = (Rep.coind U.subtype (Rep.res U.subtype X)).ρ h (T f) := by
    intro h f; apply Subtype.ext; funext g
    rw [hT, actY, actY, hT, mul_assoc]

  let E₀ : (Rep.coind U.subtype (Rep.res U.subtype X)) →ₗ[k] (Rep.coind U.subtype (Rep.res U.subtype X)) := T - LinearMap.id
  have hE₀ : ∀ (f : (Rep.coind U.subtype (Rep.res U.subtype X))) (g : G), ((E₀ f : (Rep.coind U.subtype (Rep.res U.subtype X))) : G → X) g = X.ρ φ ((f : G → X) (φ⁻¹ * g)) - (f : G → X) g :=
    fun _ _ => rfl
  have hE₀equiv : ∀ (h : G) (f : (Rep.coind U.subtype (Rep.res U.subtype X))), E₀ ((Rep.coind U.subtype (Rep.res U.subtype X)).ρ h f) = (Rep.coind U.subtype (Rep.res U.subtype X)).ρ h (E₀ f) := by
    intro h f
    show T ((Rep.coind U.subtype (Rep.res U.subtype X)).ρ h f) - (Rep.coind U.subtype (Rep.res U.subtype X)).ρ h f = (Rep.coind U.subtype (Rep.res U.subtype X)).ρ h (T f - f)
    rw [hTequiv, map_sub]

  have hterm : ∀ (f : (Rep.coind U.subtype (Rep.res U.subtype X))) (g : G) (u : U), X.ρ (g * u) ((f : G → X) (g * u)⁻¹) = X.ρ g ((f : G → X) g⁻¹) := by
    intro f g u
    rw [mul_inv_rev, ← Subgroup.coe_inv, memY, map_mul, Module.End.mul_apply]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel, map_one, Module.End.one_apply]
  let F : (Rep.coind U.subtype (Rep.res U.subtype X)) → G ⧸ U → X := fun f c => X.ρ c.out ((f : G → X) (c.out)⁻¹)
  have hF : ∀ (f : (Rep.coind U.subtype (Rep.res U.subtype X))) (g : G), F f (g : G ⧸ U) = X.ρ g ((f : G → X) g⁻¹) := by
    intro f g
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
    show X.ρ (Quotient.out (g : G ⧸ U)) ((f : G → X) (Quotient.out (g : G ⧸ U))⁻¹) = _
    rw [hu, hterm]
  have hτF : ∀ f : (Rep.coind U.subtype (Rep.res U.subtype X)), τ.hom f = ∑ c : G ⧸ U, F f c := fun f => by rw [hτ, finsum_eq_sum_of_fintype]

  have hτT : ∀ f : (Rep.coind U.subtype (Rep.res U.subtype X)), τ.hom (T f) = τ.hom f := by
    intro f
    rw [hτF, hτF]
    have key : ∀ c : G ⧸ U, F (T f) c = F f (c * (φ : G ⧸ U)) := by
      intro c
      induction c using QuotientGroup.induction_on with
      | H g =>
        rw [← QuotientGroup.mk_mul, hF, hF, hT, ← Module.End.mul_apply, ← map_mul, mul_inv_rev]
    simp_rw [key]
    exact Fintype.sum_bijective (· * (φ : G ⧸ U)) (Group.mulRight_bijective _) _ _ (fun _ => rfl)

  let W : Submodule k (Rep.coind U.subtype (Rep.res U.subtype X)) :=
    { carrier := {f | τ.hom f = 0}
      add_mem' := fun {a b} ha hb => by
        show τ.hom (a + b) = 0
        rw [map_add, ha, hb, add_zero]
      zero_mem' := by show τ.hom 0 = 0; exact map_zero _
      smul_mem' := fun c {f} hf => by
        show τ.hom (c • f) = 0
        rw [map_smul, hf, smul_zero] }
  have memW : ∀ f : (Rep.coind U.subtype (Rep.res U.subtype X)), f ∈ W ↔ τ.hom f = 0 := fun _ => Iff.rfl
  have hW : ∀ g : G, W ≤ W.comap ((Rep.coind U.subtype (Rep.res U.subtype X)).ρ g) := fun g f hf => by
    show τ.hom ((Rep.coind U.subtype (Rep.res U.subtype X)).ρ g f) = 0
    rw [Rep.hom_comm_apply, (memW f).1 hf, map_zero]
  let K : Rep k G := Rep.subrepresentation (Rep.coind U.subtype (Rep.res U.subtype X)) W hW

  let i : K ⟶ (Rep.coind U.subtype (Rep.res U.subtype X)) := Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap K.ρ (Rep.coind U.subtype (Rep.res U.subtype X)).ρ W.subtype (fun g κ => rfl))
  have hi : ∀ κ : K, i.hom κ = (κ : (Rep.coind U.subtype (Rep.res U.subtype X))) := fun _ => rfl

  have hE₀W : ∀ f : (Rep.coind U.subtype (Rep.res U.subtype X)), E₀ f ∈ W := fun f => by
    show τ.hom (T f - f) = 0
    rw [map_sub, hτT, sub_self]
  let EL : (Rep.coind U.subtype (Rep.res U.subtype X)) →ₗ[k] K := E₀.codRestrict W hE₀W
  let E : (Rep.coind U.subtype (Rep.res U.subtype X)) ⟶ K := Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap (Rep.coind U.subtype (Rep.res U.subtype X)).ρ K.ρ EL (fun g f => by
      apply Subtype.ext
      show E₀ ((Rep.coind U.subtype (Rep.res U.subtype X)).ρ g f) = (Rep.coind U.subtype (Rep.res U.subtype X)).ρ g (E₀ f)
      exact hE₀equiv g f))
  have hiE : ∀ f : (Rep.coind U.subtype (Rep.res U.subtype X)), i.hom (E.hom f) = E₀ f := fun _ => rfl
  have hi_inj : Function.Injective i.hom := fun a b hab => Subtype.ext (by simpa [hi] using hab)
  refine ⟨K, i, E, hi_inj, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro f
    constructor
    · intro hf; exact ⟨⟨f, (memW f).2 hf⟩, rfl⟩
    · rintro ⟨κ, rfl⟩; exact (memW _).1 κ.2
  ·
    intro f g
    rw [hiE, hE₀]
  ·
    intro x x' hx
    have := congrArg (fun f : (Rep.coind U.subtype (Rep.res U.subtype X)) => (f : G → X) 1) hx
    simpa [hι] using this
  ·
    intro κ
    obtain ⟨y, hy⟩ := κ
    have hy0 : τ.hom y = 0 := hy
    have hgen : ∀ c : G ⧸ U, c ∈ Subgroup.zpowers (φ : G ⧸ U) := by
      intro c
      induction c using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨n, u, hu, rfl⟩ := hφ g
        refine ⟨n, ?_⟩
        show (φ : G ⧸ U) ^ n = ((φ ^ n * u : G) : G ⧸ U)
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, (QuotientGroup.eq_one_iff u).mpr hu, mul_one]
    have hfin : IsOfFinOrder (φ : G ⧸ U) := isOfFinOrder_of_finite _
    have hdpos : 0 < orderOf (φ : G ⧸ U) := hfin.orderOf_pos

    let S : ℕ → X := fun m => ∑ j ∈ Finset.range m, F y ((φ : G ⧸ U) ^ j)
    have hS0 : S 0 = 0 := Finset.sum_range_zero _
    have hS_succ : ∀ m, S (m + 1) = S m + F y ((φ : G ⧸ U) ^ m) := fun m => Finset.sum_range_succ _ _

    let e := finEquivZPowers hfin
    let e' : Fin (orderOf (φ : G ⧸ U)) ≃ G ⧸ U := e.trans (Equiv.subtypeUnivEquiv hgen)
    have he' : ∀ j : Fin (orderOf (φ : G ⧸ U)), e' j = (φ : G ⧸ U) ^ (j : ℕ) := fun j => by
      show ((e j : Subgroup.zpowers (φ : G ⧸ U)) : G ⧸ U) = _
      rw [finEquivZPowers_apply]
    have hS_d : S (orderOf (φ : G ⧸ U)) = 0 := by
      have h1 : S (orderOf (φ : G ⧸ U)) = ∑ c : G ⧸ U, F y c := by
        show ∑ j ∈ Finset.range (orderOf (φ : G ⧸ U)), F y ((φ : G ⧸ U) ^ j) = _
        rw [Finset.sum_range]
        exact Fintype.sum_equiv e' _ _ (fun j => by rw [he'])
      rw [h1, ← hτF, hy0]

    let idx : G ⧸ U → ℕ := fun c => ((e'.symm c : Fin (orderOf (φ : G ⧸ U))) : ℕ)
    have hidx_lt : ∀ c, idx c < orderOf (φ : G ⧸ U) := fun c => (e'.symm c).isLt
    have hpow_idx : ∀ c, (φ : G ⧸ U) ^ (idx c) = c := fun c => by
      rw [← he', Equiv.apply_symm_apply]
    have hidx_pow : ∀ m : ℕ, idx ((φ : G ⧸ U) ^ m) = m % orderOf (φ : G ⧸ U) := fun m => by
      have h1 : e' ⟨m % orderOf (φ : G ⧸ U), Nat.mod_lt _ hdpos⟩ = (φ : G ⧸ U) ^ m := by
        rw [he', pow_mod_orderOf]
      have h2 := congrArg e'.symm h1
      rw [Equiv.symm_apply_apply] at h2
      show ((e'.symm ((φ : G ⧸ U) ^ m) : Fin _) : ℕ) = _
      rw [← h2]
    let Φ : G ⧸ U → X := fun c => S (idx c)
    have hKEY : ∀ c : G ⧸ U, Φ (c * (φ : G ⧸ U)) - Φ c = F y c := by
      intro c
      obtain ⟨m, hmc, hlt⟩ : ∃ m : ℕ, (φ : G ⧸ U) ^ m = c ∧ m < orderOf (φ : G ⧸ U) :=
        ⟨idx c, hpow_idx c, hidx_lt c⟩
      have hic : idx c = m := by rw [← hmc, hidx_pow, Nat.mod_eq_of_lt hlt]
      have hic1 : idx (c * (φ : G ⧸ U)) = (m + 1) % orderOf (φ : G ⧸ U) := by rw [← hmc, ← pow_succ, hidx_pow]
      show S (idx (c * (φ : G ⧸ U))) - S (idx c) = F y c
      rw [hic1, hic]
      rcases Nat.lt_or_ge (m + 1) (orderOf (φ : G ⧸ U)) with h | h
      · rw [Nat.mod_eq_of_lt h, hS_succ, hmc, add_sub_cancel_left]
      · have hmd : m + 1 = orderOf (φ : G ⧸ U) := le_antisymm (Nat.succ_le_of_lt hlt) h
        rw [hmd, Nat.mod_self, hS0, zero_sub]
        have : S m + F y ((φ : G ⧸ U) ^ m) = 0 := by rw [← hS_succ, hmd, hS_d]
        rw [← hmc]
        exact (eq_neg_of_add_eq_zero_right this).symm

    let fv : G → X := fun g => X.ρ g (Φ ((g⁻¹ : G) : G ⧸ U))
    have hfv : ∀ g, fv g = X.ρ g (Φ ((g⁻¹ : G) : G ⧸ U)) := fun _ => rfl
    let f : (Rep.coind U.subtype (Rep.res U.subtype X)) := ⟨fv, fun u g => by
      show fv ((u : G) * g) = X.ρ (u : G) (fv g)
      rw [hfv, hfv, mul_inv_rev, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (u : G)⁻¹).mpr (U.inv_mem u.2),
        mul_one, map_mul, Module.End.mul_apply]⟩
    have hf : ∀ g, (f : G → X) g = fv g := fun _ => rfl
    refine ⟨f, ?_⟩
    apply hi_inj
    rw [hiE]
    apply Subtype.ext; funext g
    rw [hE₀, hf, hf, hfv, hfv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, mul_inv_rev, inv_inv,
      QuotientGroup.mk_mul, ← map_sub, hKEY, hF, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply, inv_inv]
    rfl
  ·
    intro f
    constructor
    · intro hEf

      have h0 : E₀ f = 0 := by
        have := congrArg (fun κ : K => (i.hom κ : (Rep.coind U.subtype (Rep.res U.subtype X)))) hEf
        simpa [hiE] using this
      have hfix : ∀ g : G, X.ρ φ ((f : G → X) (φ⁻¹ * g)) = (f : G → X) g := fun g => by
        have := congrArg (fun y : (Rep.coind U.subtype (Rep.res U.subtype X)) => (y : G → X) g) h0
        exact sub_eq_zero.mp (by simpa [hE₀] using this)
      have hstep : ∀ h : G, (f : G → X) (φ * h) = X.ρ φ ((f : G → X) h) := fun h => by
        rw [← hfix (φ * h), inv_mul_cancel_left]
      have hstep' : ∀ h : G, (f : G → X) (φ⁻¹ * h) = X.ρ φ⁻¹ ((f : G → X) h) := fun h => by
        rw [← hfix h, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      have hzpow : ∀ (n : ℤ) (h : G), (f : G → X) (φ ^ n * h) = X.ρ (φ ^ n) ((f : G → X) h) := by
        intro n
        induction n using Int.induction_on with
        | zero => intro h; rw [zpow_zero, one_mul, map_one, Module.End.one_apply]
        | succ n ih =>
          intro h
          rw [zpow_add_one, mul_assoc, ih, hstep, ← Module.End.mul_apply, ← map_mul]
        | pred n ih =>
          intro h
          rw [zpow_sub_one, mul_assoc, ih, hstep', ← Module.End.mul_apply, ← map_mul]
      refine ⟨(f : G → X) 1, ?_⟩
      apply Subtype.ext; funext g
      rw [hι]
      obtain ⟨n, u, hu, rfl⟩ := hφ g
      rw [hzpow n u, ← mul_one u, ← Subgroup.coe_mk U u hu, memY f ⟨u, hu⟩ 1, Subgroup.coe_mk, mul_one,
        ← Module.End.mul_apply, ← map_mul]
    · rintro ⟨x, rfl⟩
      apply hi_inj
      rw [hiE, map_zero]
      apply Subtype.ext; funext g
      rw [hE₀, hι, hι, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, sub_self]
      rfl

end S_Rep_exists_ker_trace_cyclicShift
end P2MW
export P2MW.S_Rep_exists_ker_trace_cyclicShift (solution)
