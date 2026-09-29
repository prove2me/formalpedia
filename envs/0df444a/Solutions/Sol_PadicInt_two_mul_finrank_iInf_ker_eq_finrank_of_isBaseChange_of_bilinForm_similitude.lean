-- Prove2me | solution 1 for PadicInt.two_mul_finrank_iInf_ker_eq_finrank_of_isBaseChange_of_bilinForm_similitude
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/8b7d7c6e-c786-5bc2-af39-80844200a79b

import Mathlib
import Theorems.Thm_LinearMap_BilinForm_orthogonal_le_of_similitude_of_forall_map_sub_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_two_mul_finrank_iInf_ker_eq_finrank_of_isBaseChange_of_bilinForm_similitude

set_option autoImplicit false

namespace MRgalRANK

open Module

variable {p : ℕ} [Fact p.Prime]

theorem main {ι : Type*} {P : Type*} [AddCommGroup P] [Module ℤ_[p] P]
    [Module.Free ℤ_[p] P] [Module.Finite ℤ_[p] P]
    (s : ι → P →ₗ[ℤ_[p]] P) (a : ι → ℤ_[p]) (i₀ : ι)
    (hW₀ : ∀ x : P, s i₀ x - x ∈ ⨅ j, LinearMap.ker (s j - a j • LinearMap.id))
    (hi₀ : ¬ (p : ℤ_[p]) ∣ a i₀ - 1) (hu₀ : ¬ (p : ℤ_[p]) ∣ a i₀)
    {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]
    (j : P →ₗ[ℤ_[p]] V) (hj : IsBaseChange ℚ_[p] j)
    {V' : Type*} [AddCommGroup V'] [Module ℚ_[p] V'] [FiniteDimensional ℚ_[p] V']
    (jV : V →ₗ[ℚ_[p]] V') (hjV : Function.Injective jV)
    (e : V' →ₗ[ℚ_[p]] V') (he : ∀ v : V', e (e v) = e v) (hrange : LinearMap.range jV = LinearMap.range e)
    (B : LinearMap.BilinForm ℚ_[p] V') (halt : ∀ v : V', B v v = 0)
    (hB : ∀ v : V', (∀ w : V', B v w = 0) → v = 0)
    (hadj : ∀ x y : V', B (e x) y = B x (e y))
    (g : V' →ₗ[ℚ_[p]] V') (hg : ∀ x : P, g (jV (j x)) = jV (j (s i₀ x)))
    (hsim : ∀ x y : V', B (g x) (g y) = algebraMap ℤ_[p] ℚ_[p] (a i₀) * B x y) :
    2 * Module.finrank ℤ_[p] ↥(⨅ j, LinearMap.ker (s j - a j • LinearMap.id)) =
      Module.finrank ℤ_[p] P := by
  classical
  set W : Submodule ℤ_[p] P := ⨅ j, LinearMap.ker (s j - a j • LinearMap.id) with hWdef
  have hmemW : ∀ x : P, x ∈ W ↔ ∀ j, s j x = a j • x := by
    intro x
    simp only [hWdef, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]

  set ε : ℚ_[p] := algebraMap ℤ_[p] ℚ_[p] (a i₀) with hεdef
  have hinjRK : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := IsFractionRing.injective ℤ_[p] ℚ_[p]
  have hε0 : ε ≠ 0 := by
    intro h
    apply hu₀
    have : a i₀ = 0 := hinjRK (by rw [map_zero]; exact h)
    rw [this]
    exact dvd_zero _
  have hε1 : ε ≠ 1 := by
    intro h
    apply hi₀
    have : a i₀ = 1 := hinjRK (by rw [map_one]; exact h)
    rw [this, sub_self]
    exact dvd_zero _

  let κ := Module.Free.ChooseBasisIndex ℤ_[p] P
  let bP : Basis κ ℤ_[p] P := Module.Free.chooseBasis ℤ_[p] P
  haveI : Fintype κ := Module.Free.ChooseBasisIndex.fintype ℤ_[p] P
  let bV : Basis κ ℚ_[p] V := (Algebra.TensorProduct.basis ℚ_[p] bP).map hj.equiv
  have hbV : ∀ i, bV i = j (bP i) := by
    intro i
    simp [bV, Algebra.TensorProduct.basis_apply, IsBaseChange.equiv_tmul]
  haveI : FiniteDimensional ℚ_[p] V := Module.Finite.of_basis bV
  have hdimV : Module.finrank ℚ_[p] V = Module.finrank ℤ_[p] P := by
    rw [Module.finrank_eq_card_basis bV, Module.finrank_eq_card_basis bP]
  have hsmul : ∀ (r : ℤ_[p]) (v : V), algebraMap ℤ_[p] ℚ_[p] r • v = r • v :=
    fun r v => algebraMap_smul _ r v
  have hjcoord : ∀ x : P, j x = ∑ i, algebraMap ℤ_[p] ℚ_[p] (bP.repr x i) • bV i := by
    intro x
    conv_lhs => rw [← bP.sum_repr x]
    simp only [map_sum, LinearMap.map_smul_of_tower, hbV, hsmul]
  have hrepr : ∀ (x : P) (i : κ), bV.repr (j x) i = algebraMap ℤ_[p] ℚ_[p] (bP.repr x i) := by
    intro x i
    rw [hjcoord, map_sum]
    simp only [map_smul, Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i (fun k _ hki => by simp [hki])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    simp [Finsupp.single_eq_same]
  have hjinj : Function.Injective j := by
    intro x y hxy
    apply bP.repr.injective
    ext i
    apply hinjRK
    rw [← hrepr, ← hrepr, hxy]
  have hspan : ∀ v : V, v ∈ Submodule.span ℚ_[p] (Set.range j) := by
    intro v
    have htop : Submodule.span ℚ_[p] (Set.range bV) = ⊤ := bV.span_eq
    have hle : Submodule.span ℚ_[p] (Set.range bV) ≤ Submodule.span ℚ_[p] (Set.range j) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      rw [hbV]
      exact Submodule.subset_span ⟨bP i, rfl⟩
    exact hle (htop ▸ Submodule.mem_top)

  have he_fix : ∀ v : V, e (jV v) = jV v := by
    intro v
    obtain ⟨z, hz⟩ : jV v ∈ LinearMap.range e := hrange ▸ LinearMap.mem_range_self jV v
    rw [← hz, he]
  have he_mem : ∀ y : V', ∃ w : V, jV w = e y := by
    intro y
    have : e y ∈ LinearMap.range jV := hrange ▸ LinearMap.mem_range_self e y
    obtain ⟨w, hw⟩ := this
    exact ⟨w, hw⟩
  let Bv : LinearMap.BilinForm ℚ_[p] V := B.comp jV jV
  have hBv : ∀ x y : V, Bv x y = B (jV x) (jV y) := fun x y => rfl
  have haltV : ∀ v : V, Bv v v = 0 := fun v => by rw [hBv]; exact halt _
  have hBaltV : Bv.IsAlt := haltV
  have hnondegV : ∀ v : V, (∀ w : V, Bv v w = 0) → v = 0 := by
    intro v hv
    apply hjV
    rw [map_zero]
    apply hB
    intro y
    obtain ⟨w, hw⟩ := he_mem y
    rw [← he_fix v, hadj, ← hw]
    exact hv w
  have hnondegV' : ∀ w : V, (∀ x : V, Bv x w = 0) → w = 0 := by
    intro w hw
    apply hnondegV w
    intro x
    rw [← hBaltV.neg_eq, hw x, neg_zero]
  have hNondeg : Bv.Nondegenerate := ⟨hnondegV, hnondegV'⟩
  have hgstab : ∀ v : V, g (jV v) ∈ LinearMap.range jV := by
    intro v
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (hspan v)
    · rintro _ ⟨x, rfl⟩
      exact ⟨j (s i₀ x), (hg x).symm⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add, map_add]
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [map_smul, map_smul]
      exact Submodule.smul_mem _ c hx
  let eqv := LinearEquiv.ofInjective jV hjV
  let gV : V →ₗ[ℚ_[p]] V :=
    eqv.symm.toLinearMap ∘ₗ ((g ∘ₗ jV).codRestrict (LinearMap.range jV) hgstab)
  have hgV : ∀ v : V, jV (gV v) = g (jV v) := by
    intro v
    have h1 : (eqv (gV v) : V') = g (jV v) := by
      simp only [gV, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.apply_symm_apply, LinearMap.codRestrict_apply]
    rw [← h1]
    rfl
  have hgVj : ∀ x : P, gV (j x) = j (s i₀ x) := by
    intro x
    apply hjV
    rw [hgV, hg]
  have hsimV : ∀ x y : V, Bv (gV x) (gV y) = ε * Bv x y := by
    intro x y
    rw [hBv, hBv, hgV, hgV, hsim]

  let Wq : Submodule ℚ_[p] V := Submodule.span ℚ_[p] (j '' (W : Set P))
  have heig : ∀ w ∈ Wq, gV w = ε • w := by
    intro w hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨x, hx, rfl⟩
      rw [hgVj, (hmemW x).mp hx i₀, LinearMap.map_smul_of_tower, ← hsmul]
    · simp
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, smul_add]
    · intro c x _ hx
      rw [map_smul, hx, smul_comm]
  have hmove : ∀ v : V, gV v - v ∈ Wq := by
    intro v
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (hspan v)
    · rintro _ ⟨x, rfl⟩
      rw [hgVj, ← map_sub]
      exact Submodule.subset_span ⟨s i₀ x - x, hW₀ x, rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add, show gV x + gV y - (x + y) = (gV x - x) + (gV y - y) by abel]
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ c hx
  have hiso : Wq ≤ Bv.orthogonal Wq := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    show Bv w v = 0
    have h1 : Bv (gV w) (gV v) = ε * Bv w v := hsimV w v
    rw [heig w hw, heig v hv, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      ← mul_assoc] at h1
    have h2 : (ε * ε - ε) * Bv w v = 0 := by rw [sub_mul, h1, sub_self]
    have h3 : ε * ε - ε ≠ 0 := by
      rw [show ε * ε - ε = ε * (ε - 1) by ring]
      exact mul_ne_zero hε0 (sub_ne_zero.mpr hε1)
    exact (mul_eq_zero.mp h2).resolve_left h3
  have hsurj : Function.Surjective gV := by
    intro v

    have hrel : gV (gV v - v) = ε • (gV v - v) := heig _ (hmove v)
    rw [map_sub, smul_sub] at hrel

    refine ⟨ε⁻¹ • ((1 + ε) • v - gV v), ?_⟩
    rw [map_smul, map_sub, map_smul]
    have hkey : (1 + ε) • gV v - gV (gV v) = ε • v := by
      have h' : gV (gV v) = gV v + (ε • gV v - ε • v) := by
        rw [← hrel]
        abel
      rw [h', add_smul, one_smul]
      abel
    rw [hkey, smul_smul, inv_mul_cancel₀ hε0, one_smul]
  have horth : Bv.orthogonal Wq ≤ Wq :=
    LinearMap.BilinForm.orthogonal_le_of_similitude_of_forall_map_sub_mem Bv hnondegV' Wq gV hsurj ε hε1
      hsimV hmove
  have hLag : Bv.orthogonal Wq = Wq := le_antisymm horth hiso
  have hdimWq : 2 * Module.finrank ℚ_[p] Wq = Module.finrank ℚ_[p] V := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal hNondeg Wq
    rw [hLag] at h1
    have h2 : Module.finrank ℚ_[p] Wq ≤ Module.finrank ℚ_[p] V := Submodule.finrank_le Wq
    omega

  haveI : IsNoetherian ℤ_[p] P := isNoetherian_of_isNoetherianRing_of_finite ℤ_[p] P
  haveI : Module.Finite ℤ_[p] W := Module.IsNoetherian.finite ℤ_[p] W
  haveI : Module.IsTorsionFree ℤ_[p] W :=
    Function.Injective.moduleIsTorsionFree (Subtype.val : W → P) Subtype.val_injective (fun _ _ => rfl)
  haveI : Module.Free ℤ_[p] W := inferInstance
  let μ := Module.Free.ChooseBasisIndex ℤ_[p] W
  let bW : Basis μ ℤ_[p] W := Module.Free.chooseBasis ℤ_[p] W
  haveI : Fintype μ := Module.Free.ChooseBasisIndex.fintype ℤ_[p] W
  let f : μ → V := fun k => j (bW k : P)
  have hfli : LinearIndependent ℚ_[p] f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    obtain ⟨d, hd⟩ :=
      IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ_[p]) (Finset.univ : Finset μ) c
    choose r hr using fun i => hd i (Finset.mem_univ i)

    have hsum : j (∑ i, r i • (bW i : P)) = 0 := by
      rw [map_sum]
      have hterm : ∀ i, j (r i • (bW i : P)) = (d : ℤ_[p]) • (c i • f i) := by
        intro i
        rw [LinearMap.map_smul_of_tower, ← hsmul, hr i, smul_assoc]
      simp_rw [hterm, ← Finset.smul_sum, hc, smul_zero]
    have hzero : ∑ i, r i • (bW i : P) = 0 := hjinj (by rw [hsum, map_zero])
    have hzeroW : ∑ i, r i • bW i = 0 := by
      apply Subtype.ext
      simpa [Submodule.coe_sum] using hzero
    have hr0 : ∀ i, r i = 0 := Fintype.linearIndependent_iff.mp bW.linearIndependent r hzeroW
    have hdk : (d : ℤ_[p]) • c k = 0 := by rw [← hr k, hr0 k, map_zero]
    have hd0 : ((d : ℤ_[p]) : ℤ_[p]) ≠ 0 := nonZeroDivisors.coe_ne_zero d
    rw [Algebra.smul_def] at hdk
    exact (mul_eq_zero.mp hdk).resolve_left (fun h => hd0 (hinjRK (by rw [map_zero]; exact h)))
  have hWq_span : Wq = Submodule.span ℚ_[p] (Set.range f) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, rfl⟩

      have hx' : (⟨x, hx⟩ : W) = ∑ k, bW.repr ⟨x, hx⟩ k • bW k := ((bW.sum_repr ⟨x, hx⟩)).symm
      have hxP : x = ∑ k, bW.repr ⟨x, hx⟩ k • (bW k : P) := by
        have h := congrArg Subtype.val hx'
        rw [Submodule.coe_sum] at h
        exact h
      rw [hxP, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [LinearMap.map_smul_of_tower, ← hsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨(bW k : P), (bW k).2, rfl⟩
  have hdimWqW : Module.finrank ℚ_[p] Wq = Module.finrank ℤ_[p] W := by
    rw [hWq_span, finrank_span_eq_card hfli, Module.finrank_eq_card_basis bW]

  rw [← hdimWqW, ← hdimV]
  exact hdimWq

end MRgalRANK

theorem solution
    (p : ℕ) [Fact p.Prime] {ι : Type*} {P : Type*} [AddCommGroup P] [Module ℤ_[p] P]
    [Module.Free ℤ_[p] P] [Module.Finite ℤ_[p] P]
    (s : ι → P →ₗ[ℤ_[p]] P) (a : ι → ℤ_[p]) (i₀ : ι)
    (hW₀ : ∀ x : P, s i₀ x - x ∈ ⨅ j, LinearMap.ker (s j - a j • LinearMap.id))
    (hi₀ : ¬ (p : ℤ_[p]) ∣ a i₀ - 1) (hu₀ : ¬ (p : ℤ_[p]) ∣ a i₀)
    {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]
    (j : P →ₗ[ℤ_[p]] V) (hj : IsBaseChange ℚ_[p] j)
    {V' : Type*} [AddCommGroup V'] [Module ℚ_[p] V'] [FiniteDimensional ℚ_[p] V']
    (jV : V →ₗ[ℚ_[p]] V') (hjV : Function.Injective jV)
    (e : V' →ₗ[ℚ_[p]] V') (he : ∀ v : V', e (e v) = e v) (hrange : LinearMap.range jV = LinearMap.range e)
    (B : LinearMap.BilinForm ℚ_[p] V') (halt : ∀ v : V', B v v = 0)
    (hB : ∀ v : V', (∀ w : V', B v w = 0) → v = 0)
    (hadj : ∀ x y : V', B (e x) y = B x (e y))
    (g : V' →ₗ[ℚ_[p]] V') (hg : ∀ x : P, g (jV (j x)) = jV (j (s i₀ x)))
    (hsim : ∀ x y : V', B (g x) (g y) = algebraMap ℤ_[p] ℚ_[p] (a i₀) * B x y) :
    2 * Module.finrank ℤ_[p] ↥(⨅ j, LinearMap.ker (s j - a j • LinearMap.id)) =
      Module.finrank ℤ_[p] P := by
  exact MRgalRANK.main s a i₀ hW₀ hi₀ hu₀ j hj jV hjV e he hrange B halt hB hadj g hg hsim

end S_PadicInt_two_mul_finrank_iInf_ker_eq_finrank_of_isBaseChange_of_bilinForm_similitude
end P2MW
export P2MW.S_PadicInt_two_mul_finrank_iInf_ker_eq_finrank_of_isBaseChange_of_bilinForm_similitude (solution)
