-- Prove2me | solution 1 for PadicInt.ncard_setOf_forall_apply_eq_nsmul_sq_eq_card_range_of_forall_sub_mem_iInf_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/fb6374b5-83d8-585e-b34b-c25fca037ef6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_ncard_setOf_forall_apply_eq_nsmul_sq_eq_card_range_of_forall_sub_mem_iInf_ker

set_option autoImplicit false

namespace MRgalALG

open Module

variable {p : ℕ} [Fact p.Prime]

theorem natCard_range_eq_pow {Q G : Type*} [AddCommGroup Q] [Module ℤ_[p] Q] [Module.Free ℤ_[p] Q]
    [Module.Finite ℤ_[p] Q] [AddCommGroup G] (φ : Q →+ G)
    (hker : ∀ x : Q, φ x = 0 ↔ ∃ y : Q, x = (p : ℤ_[p]) • y) :
    Nat.card ↥φ.range = p ^ Module.finrank ℤ_[p] Q := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ_[p] Q
  let b : Basis ι ℤ_[p] Q := Module.Free.chooseBasis ℤ_[p] Q
  haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype ℤ_[p] Q

  let Φ : Q →+ (ι → ZMod p) :=
    { toFun := fun x i => PadicInt.toZMod (b.repr x i)
      map_zero' := by ext i; simp
      map_add' := fun x y => by ext i; simp }
  have hΦsurj : Function.Surjective Φ := by
    intro v
    refine ⟨∑ i, ((v i).val : ℤ_[p]) • b i, ?_⟩
    ext i
    simp only [Φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum, map_smul, Basis.repr_self,
      Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp [Finsupp.single_eq_same]
    · intro j _ hji
      simp [Finsupp.single_apply, hji, hji.symm]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hΦker : ∀ x : Q, Φ x = 0 ↔ ∃ y : Q, x = (p : ℤ_[p]) • y := by
    intro x
    constructor
    · intro hx
      have hdvd : ∀ i, (p : ℤ_[p]) ∣ b.repr x i := by
        intro i
        have hi : PadicInt.toZMod (b.repr x i) = 0 := by
          have := congrFun hx i
          simpa [Φ] using this
        have : b.repr x i ∈ RingHom.ker (PadicInt.toZMod (p := p)) := hi
        rwa [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
      choose cf hcf using hdvd
      refine ⟨b.repr.symm (Finsupp.equivFunOnFinite.symm cf), ?_⟩
      apply b.repr.injective
      rw [map_smul, LinearEquiv.apply_symm_apply]
      ext i
      simp [hcf i]
    · rintro ⟨y, rfl⟩
      ext i
      simp only [Φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul, Finsupp.coe_smul, Pi.smul_apply,
        smul_eq_mul, map_mul, Pi.zero_apply]
      rw [show PadicInt.toZMod (p : ℤ_[p]) = 0 from by
        rw [map_natCast, ZMod.natCast_self], zero_mul]

  have hkers : φ.ker = Φ.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hker, hΦker]
  have h1 : Nat.card ↥φ.range = Nat.card (Q ⧸ φ.ker) :=
    (Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv).symm
  have h2 : Nat.card (Q ⧸ Φ.ker) = Nat.card ↥Φ.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange Φ).toEquiv
  have h3 : Φ.range = ⊤ := AddMonoidHom.range_eq_top.mpr hΦsurj
  rw [h1, hkers, h2, h3, AddSubgroup.card_top, Nat.card_fun, Nat.card_zmod, Module.finrank_eq_nat_card_basis b]

theorem main {ι : Type*} {P : Type*} [AddCommGroup P] [Module ℤ_[p] P]
    [Module.Free ℤ_[p] P] [Module.Finite ℤ_[p] P]
    (s : ι → P →ₗ[ℤ_[p]] P) (a : ι → ℤ_[p])
    (hW : ∀ (i : ι) (x : P), s i x - x ∈ ⨅ j, LinearMap.ker (s j - a j • LinearMap.id))
    (hrank : 2 * Module.finrank ℤ_[p] ↥(⨅ j, LinearMap.ker (s j - a j • LinearMap.id)) =
      Module.finrank ℤ_[p] P)
    (i₀ : ι) (hi₀ : ¬ (p : ℤ_[p]) ∣ a i₀ - 1)
    {G : Type*} [AddCommGroup G] (π : P →+ G)
    (hker : ∀ x : P, π x = 0 ↔ ∃ y : P, x = (p : ℤ_[p]) • y)
    (g : ι → G → G) (hg : ∀ (i : ι) (x : P), π (s i x) = g i (π x))
    (c : ι → ℕ) (hc : ∀ i, (p : ℤ_[p]) ∣ a i - (c i : ℤ_[p])) :
    Set.ncard {y : G | y ∈ π.range ∧ ∀ i, g i y = c i • y} ^ 2 = Nat.card ↥π.range := by
  classical
  set W : Submodule ℤ_[p] P := ⨅ j, LinearMap.ker (s j - a j • LinearMap.id) with hWdef
  have hmemW : ∀ x : P, x ∈ W ↔ ∀ j, s j x = a j • x := by
    intro x
    simp only [hWdef, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]

  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hreg : IsSMulRegular P (p : ℤ_[p]) := Module.IsTorsionFree.isSMulRegular (IsRegular.of_ne_zero hp0)
  have hsat : ∀ z : P, (p : ℤ_[p]) • z ∈ W → z ∈ W := by
    intro z hz
    rw [hmemW] at hz ⊢
    intro j
    have h := hz j
    rw [map_smul, smul_comm] at h
    exact hreg h

  have hπp : ∀ y : P, π ((p : ℤ_[p]) • y) = 0 := fun y => (hker _).mpr ⟨y, rfl⟩
  have hπc : ∀ (i : ι) (x : P), π (a i • x) = c i • π x := by
    intro i x
    obtain ⟨t, ht⟩ := hc i
    have : a i • x = (c i : ℤ_[p]) • x + (p : ℤ_[p]) • (t • x) := by
      rw [smul_smul, ← add_smul, ← ht, add_sub_cancel]
    rw [this, map_add, hπp, add_zero, Nat.cast_smul_eq_nsmul, map_nsmul]

  have hXW : {y : G | y ∈ π.range ∧ ∀ i, g i y = c i • y} = π '' (W : Set P) := by
    ext y
    constructor
    · rintro ⟨⟨x, rfl⟩, hy⟩

      have hu : IsUnit (a i₀ - 1) := by
        rw [PadicInt.isUnit_iff]
        exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hi₀ (PadicInt.norm_lt_one_iff_dvd _ |>.mp h))
      obtain ⟨u, hu'⟩ := hu
      have hdiff : ∃ z : P, s i₀ x - a i₀ • x = (p : ℤ_[p]) • z := by
        have h0 : π (s i₀ x - a i₀ • x) = 0 := by
          rw [map_sub, hg, hπc, hy i₀, sub_self]
        exact (hker _).mp h0
      obtain ⟨z, hz⟩ := hdiff
      have hw : s i₀ x - x ∈ W := hW i₀ x
      have hkey : (a i₀ - 1) • x = (s i₀ x - x) - (p : ℤ_[p]) • z := by
        rw [← hz, sub_smul, one_smul]; abel

      have hx : x = (↑u⁻¹ : ℤ_[p]) • (s i₀ x - x) - (p : ℤ_[p]) • ((↑u⁻¹ : ℤ_[p]) • z) := by
        calc x = (↑u⁻¹ : ℤ_[p]) • ((a i₀ - 1) • x) := by
              rw [← hu', smul_smul, Units.inv_mul, one_smul]
          _ = (↑u⁻¹ : ℤ_[p]) • ((s i₀ x - x) - (p : ℤ_[p]) • z) := by rw [hkey]
          _ = (↑u⁻¹ : ℤ_[p]) • (s i₀ x - x) - (p : ℤ_[p]) • ((↑u⁻¹ : ℤ_[p]) • z) := by
              rw [smul_sub, smul_comm (↑u⁻¹ : ℤ_[p]) (p : ℤ_[p]) z]
      refine ⟨(↑u⁻¹ : ℤ_[p]) • (s i₀ x - x), W.smul_mem _ hw, ?_⟩
      conv_rhs => rw [hx]
      rw [map_sub, hπp, sub_zero]
    · rintro ⟨w, hw, rfl⟩
      refine ⟨⟨w, rfl⟩, fun i => ?_⟩
      rw [← hg, (hmemW w).mp hw i, hπc]

  haveI : IsNoetherian ℤ_[p] P := isNoetherian_of_isNoetherianRing_of_finite ℤ_[p] P
  haveI : Module.Finite ℤ_[p] W := Module.IsNoetherian.finite ℤ_[p] W
  haveI : Module.IsTorsionFree ℤ_[p] W :=
    Function.Injective.moduleIsTorsionFree (Subtype.val : W → P) Subtype.val_injective (fun _ _ => rfl)
  haveI : Module.Free ℤ_[p] W := inferInstance
  let πW : W →+ G := π.comp W.subtype.toAddMonoidHom
  have hkerW : ∀ w : W, πW w = 0 ↔ ∃ y : W, w = (p : ℤ_[p]) • y := by
    intro w
    constructor
    · intro h0
      obtain ⟨y, hy⟩ := (hker (w : P)).mp h0
      have hyW : y ∈ W := hsat y (hy ▸ w.2)
      exact ⟨⟨y, hyW⟩, Subtype.ext hy⟩
    · rintro ⟨y, rfl⟩
      exact hπp (y : P)
  have hcardW : Nat.card ↥πW.range = p ^ Module.finrank ℤ_[p] W := natCard_range_eq_pow πW hkerW
  have hcardP : Nat.card ↥π.range = p ^ Module.finrank ℤ_[p] P := natCard_range_eq_pow π hker
  have hrangeW : (πW.range : Set G) = π '' (W : Set P) := by
    ext y
    simp only [AddMonoidHom.coe_range, Set.mem_range, Set.mem_image, πW, AddMonoidHom.coe_comp,
      Function.comp_apply, LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype, SetLike.mem_coe]
    constructor
    · rintro ⟨w, rfl⟩; exact ⟨w, w.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩
  rw [hXW, ← hrangeW, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcardW, hcardP, ← pow_mul, mul_comm, hrank]

end MRgalALG

theorem solution
    (p : ℕ) [Fact p.Prime] {ι : Type*} {P : Type*} [AddCommGroup P] [Module ℤ_[p] P]
    [Module.Free ℤ_[p] P] [Module.Finite ℤ_[p] P]
    (s : ι → P →ₗ[ℤ_[p]] P) (a : ι → ℤ_[p])
    (hW : ∀ (i : ι) (x : P), s i x - x ∈ ⨅ j, LinearMap.ker (s j - a j • LinearMap.id))
    (hrank : 2 * Module.finrank ℤ_[p] ↥(⨅ j, LinearMap.ker (s j - a j • LinearMap.id)) =
      Module.finrank ℤ_[p] P)
    (i₀ : ι) (hi₀ : ¬ (p : ℤ_[p]) ∣ a i₀ - 1)
    {G : Type*} [AddCommGroup G] (π : P →+ G)
    (hker : ∀ x : P, π x = 0 ↔ ∃ y : P, x = (p : ℤ_[p]) • y)
    (g : ι → G → G) (hg : ∀ (i : ι) (x : P), π (s i x) = g i (π x))
    (c : ι → ℕ) (hc : ∀ i, (p : ℤ_[p]) ∣ a i - (c i : ℤ_[p])) :
    Set.ncard {y : G | y ∈ π.range ∧ ∀ i, g i y = c i • y} ^ 2 = Nat.card ↥π.range := by
  exact MRgalALG.main s a hW hrank i₀ hi₀ π hker g hg c hc

end S_PadicInt_ncard_setOf_forall_apply_eq_nsmul_sq_eq_card_range_of_forall_sub_mem_iInf_ker
end P2MW
export P2MW.S_PadicInt_ncard_setOf_forall_apply_eq_nsmul_sq_eq_card_range_of_forall_sub_mem_iInf_ker (solution)
