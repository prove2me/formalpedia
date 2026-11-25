-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.transvection_fix_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:23:53.047232+00:00
-- url     : https://prove2.me/submissions/dff5d573-61bd-44df-85ac-8d121e1aa9d2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RelationMapCommTransvection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_trv_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_relation_map_comm_transvection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (i k : Fin (d.D + 1)) (hik : i ≠ k) :
    trv i k Polynomial.X F0 = Polynomial.C F0 := by
  classical
  have h1 : ∀ n, F0 ∣ (trv i k Polynomial.X F0).coeff n := fun n => (hker _).1 (by
    have h2 := congrArg (fun p => Polynomial.coeff p n)
      (congrArg (fun f => f F0) (d.relation_map_comm_transvection c i k hik))
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.coe_mapRingHom, Polynomial.coeff_map] at h2
    rw [h2, (hker F0).2 dvd_rfl, map_zero, Polynomial.coeff_zero])
  obtain ⟨R, hR⟩ := (Polynomial.C_dvd_iff_dvd_coeff _ _).2 h1
  let Ψ : Polynomial (KTp K d.D d.N) →+* Polynomial (KTp K d.D d.N) :=
    Polynomial.eval₂RingHom (trv i k (-Polynomial.X)).toRingHom Polynomial.X
  have hΨ : Ψ.comp (trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X).toRingHom = Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [Ψ, trv, MvPolynomial.algebraMap_eq]
    · rintro ⟨i', j⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, trv_X, Ψ]
      split_ifs with h
      · simp [trv_X, h, Ne.symm hik]
      · simp [trv_X, h]
  have hneg : (Polynomial.compRingHom (-Polynomial.X)).comp (trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X).toRingHom =
      (trv (R := K) (D := d.D) (N := d.N) i k (-Polynomial.X)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [trv, MvPolynomial.algebraMap_eq]
    · rintro ⟨i', j⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, trv_X]
      split_ifs <;> simp
  have hC0 : (Polynomial.C F0 : Polynomial (KTp K d.D d.N)) ≠ 0 := by simpa using hF0
  have h3 : Polynomial.C F0 = Polynomial.C F0 * (R.comp (-Polynomial.X) * Ψ R) := by
    have e1 := congrArg (fun f => f F0) hΨ
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at e1
    rw [hR, map_mul] at e1
    have e2 : Ψ (Polynomial.C F0) = trv i k (-Polynomial.X) F0 := by simp [Ψ]
    have e3 := congrArg (fun f => f F0) hneg
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.coe_compRingHom_apply, hR, Polynomial.mul_comp, Polynomial.C_comp] at e3
    rw [e2, ← e3] at e1
    rw [← mul_assoc]; exact e1.symm
  have h4 : R.comp (-Polynomial.X) * Ψ R = 1 := (mul_left_cancel₀ hC0 (h3.symm.trans (mul_one _).symm))
  obtain ⟨u, hu, hu'⟩ := Polynomial.isUnit_iff.1 (isUnit_iff_exists_inv.2 ⟨_, h4⟩)
  have hRu : R = Polynomial.C u := by
    have e : (R.comp (-Polynomial.X)).comp (-Polynomial.X) = R := by
      rw [Polynomial.comp_assoc]; simp
    rw [← e, ← hu', Polynomial.C_comp]
  have h5 : (trv (R := K) i k Polynomial.X F0).eval 0 = F0 := by
    have : (Polynomial.evalRingHom 0).comp (trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X).toRingHom = RingHom.id _ := by
      apply MvPolynomial.ringHom_ext
      · intro a; simp [trv, MvPolynomial.algebraMap_eq]
      · rintro ⟨i', j⟩
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, trv_X]
        split_ifs <;> simp
    exact congrArg (fun f => f F0) this
  rw [hR, hRu, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C] at h5
  have hu1 : u = 1 := mul_left_cancel₀ hF0 (h5.trans (mul_one F0).symm)
  rw [hR, hRu, hu1, map_one, mul_one]
end ReciprocityTheory.ChartRestriction.G.T0.Data
